module

public import PvsNP.Circuits.CountingBound
public import PvsNP.Circuits.Enumerate
public import PvsNP.Circuits.TruthTable
public import PvsNP.Complexity.CircuitReductions

import Init.Data.List.Find
import Init.Data.List.Perm

/-! # A circuit lower bound by enumeration of truth tables -/

public section

namespace PvsNP.Circuits

private def circuitTables (n s : Nat) : List BinaryWord :=
  (enumerateCircuits n s).map (fun c ↦ truthTable n c.eval)

private def firstMissingTable (n s : Nat) : Option BinaryWord :=
  let tables := circuitTables n s
  (allTruthTables n).find? (fun table ↦ !(tables.contains table))

/-- Choose the first truth table omitted by the circuits of size at most `s`,
with the all-false table as a fallback when every table is covered. -/
def hardTruthTable (n s : Nat) : BinaryWord :=
  (firstMissingTable n s).getD (List.replicate (2 ^ n) false)

theorem length_hardTruthTable (n s : Nat) : (hardTruthTable n s).length = 2 ^ n := by
  unfold hardTruthTable
  cases hPick : firstMissingTable n s with
  | none => simp
  | some table =>
    have hFound : table ∈ allTruthTables n := List.mem_of_find?_eq_some hPick
    exact length_of_mem_allTruthTables hFound

private theorem hardTruthTable_notMem_circuitTables {n s : Nat}
    (hCount : (enumerateCircuits n s).length < 2 ^ (2 ^ n)) :
    hardTruthTable n s ∉ circuitTables n s := by
  cases hPick : firstMissingTable n s with
  | none =>
    have hNo := List.find?_eq_none.mp (show
      (allTruthTables n).find? (fun table ↦ !((circuitTables n s).contains table)) = none
      from hPick)
    have hCover : allTruthTables n ⊆ circuitTables n s := by
      intro table hTable
      by_contra hAbsent
      exact hNo table hTable (by simpa [Bool.not_eq_true, List.contains_iff_mem] using hAbsent)
    have hLength := (allTruthTables_nodup n).length_le_of_subset hCover
    rw [allTruthTables_length, circuitTables, List.length_map] at hLength
    exact (Nat.not_le_of_gt hCount hLength).elim
  | some table =>
    have hFound := List.find?_some (show
      (allTruthTables n).find? (fun table ↦ !((circuitTables n s).contains table)) = some table
      from hPick)
    have hAbsent : table ∉ circuitTables n s := by
      intro hIn
      have hContains := List.contains_iff_mem.mpr hIn
      simp only [hContains, Bool.not_true, Bool.false_eq_true] at hFound
    simpa only [hardTruthTable, hPick, Option.getD_some] using hAbsent

/-- When there are too few circuits to cover all tables, every small circuit
disagrees with the table selected by the search. -/
theorem hardTruthTable_mismatch {n s : Nat}
    (hCount : (enumerateCircuits n s).length < 2 ^ (2 ^ n))
    (c : BooleanCircuit n) (hSize : c.size ≤ s) :
    ∃ x : Fin n → Bool, c.eval x ≠ tableLookup n (hardTruthTable n s) (List.ofFn x) := by
  apply Classical.not_forall.mp
  intro hAgree
  obtain ⟨d, hListed, hEval⟩ := exists_mem_enumerateCircuits_of_size_le c hSize
  have hTable :
      truthTable n d.eval = hardTruthTable n s := by
    calc
      _ = truthTable n (fun x ↦ tableLookup n (hardTruthTable n s) (List.ofFn x)) :=
        congrArg (truthTable n) (funext fun x ↦ (hEval x).trans (hAgree x))
      _ = _ := truthTable_tableLookup n _ (length_hardTruthTable n s)
  exact hardTruthTable_notMem_circuitTables hCount (List.mem_map.mpr ⟨d, hListed, hTable⟩)

end PvsNP.Circuits

namespace PvsNP

open Circuits

/-- The selected table's value at a binary word, using the budget for its length. -/
def countingHardBit (word : BinaryWord) : Bool :=
  tableLookup word.length (hardTruthTable word.length (countingBudget word.length)) word

@[expose] def countingHardLanguage : BinaryLanguage :=
  {word | countingHardBit word = true}

/-- Every circuit for the length-`n` slice exceeds the enumeration budget. -/
theorem countingHardLanguage_size_gt (n : Nat) (hn : 5 ≤ n) (c : BooleanCircuit n)
    (hCorrect : ∀ x : Fin n → Bool, c.eval x = true ↔ List.ofFn x ∈ countingHardLanguage) :
    countingBudget n < c.size := by
  by_contra! hSize
  have hCount := (length_enumerateCircuits_le n (countingBudget n)).trans_lt
    (countingBudget_circuit_count_lt n hn)
  obtain ⟨x, hMiss⟩ := hardTruthTable_mismatch hCount c hSize
  apply hMiss
  apply Bool.eq_iff_iff.mpr
  have hx := hCorrect x
  change (c.eval x = true ↔ countingHardBit (List.ofFn x) = true) at hx
  simpa only [countingHardBit, List.length_ofFn] using hx

private theorem PolynomiallyBounded.not_eventually_dominates_pow_two
    {f : Nat → Nat} (hPoly : PolynomiallyBounded f) (cutoff : Nat) :
    ¬ ∀ n ≥ cutoff, 2 ^ n ≤ f n := by
  intro hTail
  apply pow_two_not_polynomiallyBounded
  refine (hPoly.add (PolynomiallyBounded.const (2 ^ cutoff))).mono ?_
  intro n
  by_cases hn : cutoff ≤ n
  · exact (hTail n hn).trans (Nat.le_add_right ..)
  · have hPow : 2 ^ n ≤ 2 ^ cutoff :=
      Nat.pow_le_pow_right (by decide) (Nat.le_of_lt (Nat.lt_of_not_ge hn))
    exact hPow.trans (Nat.le_add_left ..)

theorem countingHardLanguage_not_mem_PPoly : countingHardLanguage ∉ PPoly := by
  rintro ⟨circuit, hSize, hEval⟩
  have hPoly := hSize.comp ((PolynomiallyBounded.const 2).mul PolynomiallyBounded.id)
  apply hPoly.not_eventually_dominates_pow_two 8
  intro m hm
  exact (pow_two_le_countingBudget_double m hm).trans
    (Nat.le_of_lt (countingHardLanguage_size_gt (2 * m) (by omega) (circuit (2 * m))
      (hEval (2 * m))))

theorem exists_countingHardLanguage_of_one_le_budget (n : Nat) (hn : 5 ≤ n)
    (hOne : 1 ≤ countingBudget n) :
    ∃ w : BinaryWord, w.length = n ∧ w ∈ countingHardLanguage := by
  by_contra hNone
  let c := BooleanCircuit.const n false
  have hCorrect (x : Fin n → Bool) :
      c.eval x = true ↔ List.ofFn x ∈ countingHardLanguage := by
    constructor
    · simp [c]
    · intro hMem
      exact (hNone ⟨List.ofFn x, List.length_ofFn, hMem⟩).elim
  have hLarge := countingHardLanguage_size_gt n hn c hCorrect
  simp only [c, BooleanCircuit.size_const] at hLarge
  omega

theorem exists_countingHardLanguage_even_length (m : Nat) (hm : 8 ≤ m) :
    ∃ w : BinaryWord, w.length = 2 * m ∧ w ∈ countingHardLanguage := by
  apply exists_countingHardLanguage_of_one_le_budget (2 * m) (by omega)
  exact (Nat.succ_le_of_lt (show 0 < 2 ^ m from Nat.pow_pos (by decide))).trans
    (pow_two_le_countingBudget_double m hm)

/-- Using the entire selected table as the certificate violates Cook's length bound,
even when only accepted words must have certificates. -/
theorem countingHardTable_certificates_too_long :
    ¬ ∃ k : Nat, ∀ w ∈ countingHardLanguage,
      (hardTruthTable w.length (countingBudget w.length)).length ≤ w.length ^ k := by
  rintro ⟨k, hCert⟩
  have hPoly := ((PolynomiallyBounded.const 2).mul PolynomiallyBounded.id).pow k
  apply hPoly.not_eventually_dominates_pow_two 8
  intro m hm
  obtain ⟨word, hLength, hMem⟩ := exists_countingHardLanguage_even_length m hm
  have hBound := hCert word hMem
  rw [length_hardTruthTable, hLength] at hBound
  exact (Nat.pow_le_pow_right (by decide) (by omega : m ≤ 2 * m)).trans hBound

theorem p_ne_np_of_countingHardLanguage_mem_NP (h : countingHardLanguage ∈ NP) : P ≠ NP :=
  p_ne_np_of_CNFSAT_not_mem_PPoly
    (CNFSAT_not_mem_PPoly_of_mem_NP h countingHardLanguage_not_mem_PPoly)

end PvsNP
