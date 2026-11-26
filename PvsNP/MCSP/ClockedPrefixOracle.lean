module

public import PvsNP.Complexity.CertificateEnumeration
public import PvsNP.MCSP.MergeWitness
public import PvsNP.MCSP.Request
public import PvsNP.MCSP.StreamResources

/-! # Clocked Cook decisions for merge prefix queries -/

public section

namespace PvsNP.MCSP

open Circuits
open AssignmentQueryTree (allAssignments mem_allAssignments)

/-- Cook's clock for the canonical binary request. -/
@[expose] def mergeRequestClock (k : Nat) (r : MergeRequest) : Nat :=
  (encodeMergeRequest r).length ^ k + k

/-- Read the answer at the request clock. An unfinished computation returns false. -/
@[expose] def clockedPrefixAnswer (D : Machine Bool) (k : Nat) (r : MergeRequest) : Bool :=
  match (D.run (mergeRequestClock k r) (D.start (encodeMergeRequest r))).state with
  | .inl _ => false
  | .inr answer => answer

theorem clockedPrefixAnswer_eq_true_iff (D : Machine Bool) (k : Nat)
    (hTime : ∀ query : BinaryWord, D.HaltsWithin query (query.length ^ k + k))
    (hDecides : D.Decides MergePrefixLanguage) (r : MergeRequest) :
    clockedPrefixAnswer D k r = true ↔ MergePrefixFeasible r.cap r.old r.seen r.bit r.pref := by
  rw [← encodeMergeRequest_mem_mergePrefixLanguage, hDecides,
    D.accepts_iff_at_bound (encodeMergeRequest r) (hTime _)]
  change clockedPrefixAnswer D k r = true ↔
    (D.run (mergeRequestClock k r) (D.start (encodeMergeRequest r))).state = .inr true
  cases hState : (D.run (mergeRequestClock k r) (D.start (encodeMergeRequest r))).state <;>
    simp [clockedPrefixAnswer, hState]

/-- A uniform bound on decider ticks in terms of the sum of arity and cap. -/
@[expose] def mergeRequestTickBound (k parameters : Nat) : Nat :=
  (26 * (parameters + 1) ^ 2) ^ k + k

theorem mergeRequestTickBound_polynomiallyBounded (k : Nat) :
    PolynomiallyBounded (mergeRequestTickBound k) := by
  have hSucc := PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)
  exact (((PolynomiallyBounded.const 26).mul (hSucc.pow 2)).pow k).add
    (PolynomiallyBounded.const k)

theorem mergeRequestClock_le (k : Nat) (r : MergeRequest) :
    mergeRequestClock k r ≤ mergeRequestTickBound k (r.arity + r.cap) := by
  have hLength := (length_encodeMergeRequest_le r).trans
    (mergeRequestLengthBound_le_quadratic r.arity r.cap)
  exact Nat.add_le_add_right (Nat.pow_le_pow_left hLength k) k

/-- The decider physically halts with the reported answer within the uniform tick bound. -/
theorem clockedPrefixAnswer_run (D : Machine Bool) (k : Nat)
    (hTime : ∀ query : BinaryWord, D.HaltsWithin query (query.length ^ k + k))
    (r : MergeRequest) :
    ∃ ticks ≤ mergeRequestTickBound k (r.arity + r.cap),
      (D.run ticks (D.start (encodeMergeRequest r))).state = .inr (clockedPrefixAnswer D k r) := by
  obtain ⟨ticks, hTicks, answer, hState⟩ := hTime (encodeMergeRequest r)
  change ticks ≤ mergeRequestClock k r at hTicks
  have hAtClock : (D.run (mergeRequestClock k r) (D.start (encodeMergeRequest r))).state =
      .inr answer := by
    rw [D.run_eq_of_halted_le _ hTicks hState, hState]
  exact ⟨ticks, Nat.le_trans hTicks (mergeRequestClock_le k r), by
    simp [clockedPrefixAnswer, hAtClock, hState]⟩

private def exhaustivePrefixAnswer {n : Nat} (cap : Nat) (old : BooleanCircuit n)
    (seen : Nat) (bit : Bool) (pref : BinaryWord) : Bool :=
  (wordsOfLength [false, true] (mergeWitnessLength n cap)).any fun word ↦
    (allAssignments n).all (checkMergePrefixRow cap old seen bit pref word)

private theorem exhaustivePrefixAnswer_eq_true_iff {n : Nat} (cap : Nat)
    (old : BooleanCircuit n) (seen : Nat) (bit : Bool) (pref : BinaryWord) :
    exhaustivePrefixAnswer cap old seen bit pref = true ↔
      MergePrefixFeasible cap old seen bit pref := by
  have hCovers : ∀ b : Bool, b ∈ ([false, true] : List Bool) := by
    intro b
    cases b <;> decide
  rw [mergePrefixFeasible_iff_checked_rows]
  simp only [exhaustivePrefixAnswer, List.any_eq_true, List.all_eq_true,
    mem_wordsOfLength_iff_of_covers hCovers]
  exact exists_congr fun _ ↦ and_congr_right' ⟨fun h x ↦ h x (mem_allAssignments x),
    fun h x _ ↦ h x⟩

/-- Use the bounded Cook request on its domain, and exhaustively decide the
out-of-domain inputs needed to make the logical oracle total. -/
def clockedMergePrefixOracle {n : Nat} (D : Machine Bool) (k cap : Nat) : MergePrefixOracle n :=
  fun old seen bit pref ↦
    if hPref : pref.length ≤ mergeWitnessLength n cap then
      if hBounds : seen ≤ 2 ^ n ∧ old.size ≤ max 1 cap then
        clockedPrefixAnswer D k ⟨n, cap, old, seen, bit, pref, hBounds.1, hBounds.2, hPref⟩
      else exhaustivePrefixAnswer cap old seen bit pref
    else false

theorem clockedMergePrefixOracle_eq_answer (D : Machine Bool) (k : Nat) (r : MergeRequest) :
    clockedMergePrefixOracle D k r.cap r.old r.seen r.bit r.pref = clockedPrefixAnswer D k r := by
  simp only [clockedMergePrefixOracle, dite_eq_left r.pref_length_le,
    dite_eq_left (And.intro r.seen_le r.old_size_le)]

theorem clockedMergePrefixOracle_correct (D : Machine Bool) (k cap n : Nat)
    (hTime : ∀ query : BinaryWord, D.HaltsWithin query (query.length ^ k + k))
    (hDecides : D.Decides MergePrefixLanguage) :
    CorrectMergePrefixOracle (clockedMergePrefixOracle (n := n) D k cap) cap := by
  intro old seen bit pref
  by_cases hLength : pref.length ≤ mergeWitnessLength n cap
  · by_cases hBounds : seen ≤ 2 ^ n ∧ old.size ≤ max 1 cap
    · let r : MergeRequest := ⟨n, cap, old, seen, bit, pref, hBounds.1, hBounds.2, hLength⟩
      exact (clockedMergePrefixOracle_eq_answer D k r ▸
        clockedPrefixAnswer_eq_true_iff D k hTime hDecides r)
    · simpa only [clockedMergePrefixOracle, dite_eq_left hLength, dite_eq_right hBounds] using
        exhaustivePrefixAnswer_eq_true_iff cap old seen bit pref
  · simp only [clockedMergePrefixOracle, dite_eq_right hLength, Bool.false_eq_true, false_iff]
    rintro ⟨c, hSize, _, hPref⟩
    exact hLength (hPref.length_le.trans_eq (length_encodeMergeWitness cap c hSize))

theorem searchStream_clockedMergePrefix_isSome_iff (D : Machine Bool) (k n cap : Nat)
    (hTime : ∀ query : BinaryWord, D.HaltsWithin query (query.length ^ k + k))
    (hDecides : D.Decides MergePrefixLanguage) (bits : BinaryWord) :
    (searchStream n (mergeByPrefixSearch cap (clockedMergePrefixOracle D k cap)) bits).isSome =
      true ↔ SizeBounded n cap bits :=
  searchStream_prefixOracle_isSome_iff
    (clockedMergePrefixOracle_correct D k cap n hTime hDecides) bits

/-- Every recorded query from a retained stream state uses a canonical request
and takes at most the stated number of decider ticks. -/
theorem clockedMergePrefix_query_run (D : Machine Bool) (k n cap : Nat)
    (hTime : ∀ query : BinaryWord, D.HaltsWithin query (query.length ^ k + k))
    (hDecides : D.Decides MergePrefixLanguage) {bits : BinaryWord} {state : StreamState n}
    (hState : runStream n (mergeByPrefixSearch cap (clockedMergePrefixOracle D k cap)) bits =
      some state) (bit : Bool) {query : BinaryWord}
    (hQuery : query ∈ (searchMergeWithPrefix cap (clockedMergePrefixOracle D k cap)
      state.circuit state.seen bit).2) :
    ∃ (hSeen : state.seen ≤ 2 ^ n) (hOld : state.circuit.size ≤ max 1 cap)
        (hPref : query.length ≤ mergeWitnessLength n cap),
      let r : MergeRequest := ⟨n, cap, state.circuit, state.seen, bit, query, hSeen, hOld, hPref⟩
      ∃ ticks ≤ mergeRequestTickBound k (n + cap),
        (D.run ticks (D.start (encodeMergeRequest r))).state =
          .inr (clockedMergePrefixOracle D k cap state.circuit state.seen bit query) := by
  have hCorrect := mergeByPrefixSearch_correct
    (clockedMergePrefixOracle_correct D k cap n hTime hDecides)
  obtain ⟨hSeen, hOld⟩ := runStream_retained_bounds hCorrect hState
  have hPref := searchMergeWithPrefix_query_length_le cap (clockedMergePrefixOracle D k cap)
    state.circuit state.seen bit hQuery
  let r : MergeRequest := ⟨n, cap, state.circuit, state.seen, bit, query, hSeen, hOld, hPref⟩
  refine ⟨hSeen, hOld, hPref, ?_⟩
  rw [clockedMergePrefixOracle_eq_answer D k r]
  exact clockedPrefixAnswer_run D k hTime r

/-- Membership provides one clocked decider for all widths and gate caps. -/
theorem exists_clockedMergePrefixSearch (hLanguage : MergePrefixLanguage ∈ P) :
    ∃ (D : Machine Bool) (k : Nat),
      (∀ query : BinaryWord, D.HaltsWithin query (query.length ^ k + k)) ∧
      D.Decides MergePrefixLanguage ∧ ∀ n cap bits,
        (searchStream n (mergeByPrefixSearch cap (clockedMergePrefixOracle D k cap)) bits).isSome =
          true ↔ SizeBounded n cap bits := by
  obtain ⟨D, ⟨k, hTime⟩, hDecides⟩ := hLanguage
  exact ⟨D, k, hTime, hDecides, fun n cap ↦
    searchStream_clockedMergePrefix_isSome_iff D k n cap hTime hDecides⟩

end PvsNP.MCSP
