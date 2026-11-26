module

public import PvsNP.Complexity.PrefixWitnessSearch
public import PvsNP.SAT.AssignmentSearch
public import PvsNP.SAT.SearchOracleQuery

import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Nat.Sum

/-! # Witness search from exact binary CNF decisions -/

public section

namespace PvsNP.SATSearch

open SATAssignment (checkWord checkWord_eq_true_iff lookup ofAssignment lookup_ofAssignment
  length_ofAssignment literalIndex_lt_length_word sat_congr_on_occurringIndices)

/-- A unit-clause query accepts exactly when the prefix extends to a full
length-bounded satisfying assignment. -/
theorem mem_prefixQuery_iff_exists_assignment {word pref : BinaryWord}
    (hLength : pref.length ≤ word.length) :
    prefixQuery word pref ∈ CNFSAT ↔
      ∃ assignment : BinaryWord,
        assignment.length = word.length ∧ pref <+: assignment ∧
          checkWord word assignment = true := by
  rw [prefixQuery_mem_CNFSAT_iff]
  constructor
  · rintro ⟨F, hDecode, σ, hSat, hPref⟩
    let assignment := ofAssignment σ word.length
    have hSize : assignment.length = word.length := length_ofAssignment ..
    have hPrefix : pref <+: assignment := by
      apply List.prefix_iff_eq_take.mpr
      apply List.ext_getElem
      · rw [List.length_take, hSize, Nat.min_eq_left hLength]
      · intro i hi hj
        simp only [List.getElem_take, assignment, ofAssignment, List.getElem_ofFn]
        exact (hPref ⟨i, hi⟩).symm
    have hAgree : ∀ i ∈ CNFCode.occurringIndices F, lookup assignment i = σ i := by
      intro i hi
      obtain ⟨c, hc, l, hl, rfl⟩ := CNFCode.mem_occurringIndices_iff.mp hi
      exact lookup_ofAssignment σ (literalIndex_lt_length_word hDecode hc hl)
    exact ⟨assignment, hSize, hPrefix, (checkWord_eq_true_iff _ _).mpr
      ⟨F, hDecode, (sat_congr_on_occurringIndices F hAgree).mpr hSat⟩⟩
  · rintro ⟨assignment, _, hPrefix, hCheck⟩
    obtain ⟨F, hDecode, hSat⟩ := (checkWord_eq_true_iff _ _).mp hCheck
    refine ⟨F, hDecode, lookup assignment, hSat, fun i ↦ ?_⟩
    have hi := i.isLt.trans_le hPrefix.length_le
    simp only [lookup, List.getElem?_eq_getElem hi, Option.getD_some]
    exact (hPrefix.getElem i.isLt).symm

/-- Treat a prefix exceeding the assignment length as infeasible. -/
@[expose] def extensionOracle (answer : BinaryWord → Bool) (word pref : BinaryWord) : Bool :=
  if pref.length ≤ word.length then answer (prefixQuery word pref) else false

theorem extensionOracle_eq_true_iff (answer : BinaryWord → Bool)
    (hAnswer : ∀ q, answer q = true ↔ q ∈ CNFSAT) (word pref : BinaryWord) :
    extensionOracle answer word pref = true ↔
      ∃ assignment : BinaryWord,
        assignment.length = word.length ∧ pref <+: assignment ∧
          checkWord word assignment = true := by
  by_cases hLength : pref.length ≤ word.length
  · rw [extensionOracle, ite_eq_left hLength, hAnswer,
      mem_prefixQuery_iff_exists_assignment hLength]
  · simp only [extensionOracle, ite_eq_right hLength, Bool.false_eq_true, false_iff]
    rintro ⟨assignment, hSize, hPrefix, _⟩
    exact hLength (hPrefix.length_le.trans_eq hSize)

/-- Build an assignment and record the exact binary words submitted to the oracle. -/
def searchWithOracle (answer : BinaryWord → Bool) (word : BinaryWord) :
    Option BinaryWord × List BinaryWord :=
  let result := prefixWitnessSearch (extensionOracle answer word) word.length
  (result.1, result.2.map (prefixQuery word))

theorem searchWithOracle_sound (answer : BinaryWord → Bool)
    (hAnswer : ∀ q, answer q = true ↔ q ∈ CNFSAT) {word assignment : BinaryWord}
    (hResult : (searchWithOracle answer word).1 = some assignment) :
    assignment.length = word.length ∧ checkWord word assignment = true :=
  prefixWitnessSearch_sound (extensionOracle_eq_true_iff answer hAnswer word) hResult

theorem searchWithOracle_success_iff (answer : BinaryWord → Bool)
    (hAnswer : ∀ q, answer q = true ↔ q ∈ CNFSAT) (word : BinaryWord) :
    (∃ assignment, (searchWithOracle answer word).1 = some assignment) ↔ word ∈ CNFSAT := by
  change (∃ assignment, (prefixWitnessSearch (extensionOracle answer word) word.length).1 =
    some assignment) ↔ _
  rw [prefixWitnessSearch_complete (extensionOracle_eq_true_iff answer hAnswer word)]
  simpa only [prefixQuery_nil, List.nil_prefix, true_and] using
    (mem_prefixQuery_iff_exists_assignment (pref := []) (word := word) (Nat.zero_le _)).symm

theorem searchWithOracle_none_iff (answer : BinaryWord → Bool)
    (hAnswer : ∀ q, answer q = true ↔ q ∈ CNFSAT) (word : BinaryWord) :
    (searchWithOracle answer word).1 = none ↔ word ∉ CNFSAT := by
  rw [← searchWithOracle_success_iff answer hAnswer word]
  cases (searchWithOracle answer word).1 <;> simp

theorem searchWithOracle_query_count (answer : BinaryWord → Bool) (word : BinaryWord) :
    (searchWithOracle answer word).2.length = if answer word then word.length + 1 else 1 := by
  simp only [searchWithOracle, List.length_map, prefixWitnessSearch_query_count,
    extensionOracle, List.length_nil, Nat.zero_le, ite_true, prefixQuery_nil]

theorem searchWithOracle_query_count_le (answer : BinaryWord → Bool) (word : BinaryWord) :
    (searchWithOracle answer word).2.length ≤ word.length + 1 := by
  rw [searchWithOracle_query_count]
  split <;> omega

theorem searchWithOracle_query_length_le (answer : BinaryWord → Bool) (word q : BinaryWord)
    (h : q ∈ (searchWithOracle answer word).2) :
    q.length ≤ word.length + word.length * (word.length + 5) := by
  obtain ⟨pref, hp, rfl⟩ := List.mem_map.mp h
  rw [length_prefixQuery]
  exact prefixQueryLength_le _ _ <|
    prefixWitnessSearch_query_length_le (extensionOracle answer word) word.length pref hp

/-- Read a Cook decider at its specified clock. The running-state branch
allows this function to be defined even for machines without a halt proof. -/
def clockedOracle (D : Machine Bool) (k : Nat) (query : BinaryWord) : Bool :=
  match (D.run (query.length ^ k + k) (D.start query)).state with
  | .inl _ => false
  | .inr accept => accept

theorem clockedOracle_eq_true_iff_accepts (D : Machine Bool) (k : Nat) (query : BinaryWord)
    (hTime : D.HaltsWithin query (query.length ^ k + k)) :
    clockedOracle D k query = true ↔ D.Accepts query := by
  rw [D.accepts_iff_at_bound query hTime]
  cases hState : (D.run (query.length ^ k + k) (D.start query)).state <;>
    simp [clockedOracle, hState]

theorem clockedOracle_eq_true_iff (D : Machine Bool) (k : Nat)
    (hTime : ∀ query, D.HaltsWithin query (query.length ^ k + k))
    (hDecides : D.Decides CNFSAT) (query : BinaryWord) :
    clockedOracle D k query = true ↔ query ∈ CNFSAT :=
  (clockedOracle_eq_true_iff_accepts D k query (hTime query)).trans (hDecides query).symm

/-- The recorded calls to a clocked Cook decider recover a checked assignment
on every satisfiable word and report failure on every other word. -/
theorem searchWithClockedOracle_correct (D : Machine Bool) (k : Nat)
    (hTime : ∀ query, D.HaltsWithin query (query.length ^ k + k))
    (hDecides : D.Decides CNFSAT) (word : BinaryWord) :
    match (searchWithOracle (clockedOracle D k) word).1 with
    | none => word ∉ CNFSAT
    | some assignment => word ∈ CNFSAT ∧ assignment.length = word.length ∧
        checkWord word assignment = true := by
  have hAnswer := clockedOracle_eq_true_iff D k hTime hDecides
  cases hRun : (searchWithOracle (clockedOracle D k) word).1 with
  | none => exact (searchWithOracle_none_iff _ hAnswer word).mp hRun
  | some assignment =>
    exact ⟨(searchWithOracle_success_iff _ hAnswer word).mp ⟨assignment, hRun⟩,
      searchWithOracle_sound _ hAnswer hRun⟩

/-- The sum of the query lengths and the ticks allotted to their clocked runs.
This measures the cost of the recorded calls to the decider. -/
def oracleSearchCharge (k : Nat) (queries : List BinaryWord) : Nat :=
  (queries.map fun q ↦ q.length + (q.length ^ k + k)).sum

private theorem queryCharge_le {queries : List BinaryWord} (k B : Nat)
    (h : ∀ q ∈ queries, q.length ≤ B) :
    oracleSearchCharge k queries ≤ queries.length * (B + (B ^ k + k)) := by
  induction queries with
  | nil => simp [oracleSearchCharge]
  | cons q qs ih =>
    have hq := h q (List.mem_cons_self ..)
    have hRest := ih (fun d hd ↦ h d (List.mem_cons_of_mem _ hd))
    have hFirst : q.length + (q.length ^ k + k) ≤ B + (B ^ k + k) :=
      Nat.add_le_add hq (Nat.add_le_add_right (Nat.pow_le_pow_left hq k) k)
    simp only [oracleSearchCharge, List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    exact (Nat.add_le_add hFirst hRest).trans_eq (Nat.add_comm ..)

theorem searchWithOracle_charge_polynomiallyBounded (k : Nat) :
    PolynomiallyBounded (fun n ↦ (n + 1) *
      ((n + n * (n + 5)) + ((n + n * (n + 5)) ^ k + k))) := by
  let hN := PolynomiallyBounded.id
  let c := PolynomiallyBounded.const
  have hB := hN.add (hN.mul (hN.add (c 5)))
  exact (hN.add (c 1)).mul (hB.add ((hB.pow k).add (c k)))

theorem searchWithOracle_charge_le (answer : BinaryWord → Bool) (k : Nat) (word : BinaryWord) :
    let B := word.length + word.length * (word.length + 5)
    oracleSearchCharge k (searchWithOracle answer word).2 ≤ (word.length + 1) * (B + (B ^ k + k)) :=
  (queryCharge_le k _ (fun q ↦ searchWithOracle_query_length_le answer word q)).trans
    (Nat.mul_le_mul_right _ (searchWithOracle_query_count_le answer word))

end PvsNP.SATSearch
