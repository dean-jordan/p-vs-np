module

public import PvsNP.SAT.Assignment
public import PvsNP.SAT.AssignmentTraversal
public import PvsNP.SAT.DistinctVariableBound

import Init.Data.Nat.Sqrt.Lemmas

/-! # Deterministic search over the variables that occur in a binary CNF -/

public section

namespace PvsNP.SATAssignment

open CNFCode (encode decode literalIndex occurringIndices mem_occurringIndices_iff)

/-- Changing values outside the occurring variables preserves formula satisfaction. -/
theorem sat_congr_on_occurringIndices (F : CNF.Formula Nat) {σ τ : Nat → Bool}
    (h : ∀ i ∈ occurringIndices F, σ i = τ i) : CNF.Sat σ F ↔ CNF.Sat τ F := by
  have transfer {σ τ : Nat → Bool} (agree : ∀ i ∈ occurringIndices F, σ i = τ i)
      (hSat : CNF.Sat σ F) : CNF.Sat τ F := by
    intro c hc
    obtain ⟨l, hl, hs⟩ := hSat c hc
    have he := agree (literalIndex l) (mem_occurringIndices_iff.mpr ⟨c, hc, l, hl, rfl⟩)
    refine ⟨l, hl, ?_⟩
    cases l <;> simp only [literalIndex, CNF.Literal.sat_pos, CNF.Literal.sat_neg] at he hs ⊢ <;>
      exact he.symm.trans hs
  exact ⟨transfer h, transfer (fun i hi ↦ (h i hi).symm)⟩

private theorem checkFormula_ofAssignment_eq_true_iff (F : CNF.Formula Nat) (σ : Nat → Bool) :
    checkFormula F (ofAssignment σ (encode F).length) = true ↔ CNF.Sat σ F := by
  rw [checkFormula_eq_true_iff]
  apply sat_congr_on_occurringIndices F
  intro i hi
  obtain ⟨c, hc, l, hl, rfl⟩ := mem_occurringIndices_iff.mp hi
  exact lookup_ofAssignment σ (CNFCode.literalIndex_lt_length_encode hc hl)

/-- Decide a decoded formula and count the complete assignments it checks. -/
def searchFormula (F : CNF.Formula Nat) : Bool × Nat :=
  let length := (encode F).length
  searchAssignments (fun σ ↦ checkFormula F (ofAssignment σ length))
    (occurringIndices F) (fun _ ↦ false)

/-- Decide the binary language, rejecting malformed words with zero assignment checks. -/
def searchWord (word : BinaryWord) : Bool × Nat :=
  match decode word with
  | none => (false, 0)
  | some F => searchFormula F

theorem searchWord_encode (F : CNF.Formula Nat) : searchWord (encode F) = searchFormula F := by
  simp only [searchWord, CNFCode.decode_encode]

theorem searchFormula_accepts_iff (F : CNF.Formula Nat) :
    (searchFormula F).1 = true ↔ CNF.Satisfiable F := by
  rw [searchFormula, searchAssignments_accepts_iff]
  constructor
  · rintro ⟨σ, _, hCheck⟩
    exact ⟨σ, (checkFormula_ofAssignment_eq_true_iff F σ).mp hCheck⟩
  · rintro ⟨σ, hSat⟩
    let τ (i : Nat) := if i ∈ occurringIndices F then σ i else false
    refine ⟨τ, fun i hi ↦ ite_eq_right hi, (checkFormula_ofAssignment_eq_true_iff F τ).mpr ?_⟩
    exact (sat_congr_on_occurringIndices F (fun i hi ↦ (ite_eq_left hi).symm)).mp hSat

/-- The executable search agrees with the binary language on every input. -/
theorem searchWord_accepts_iff (word : BinaryWord) :
    (searchWord word).1 = true ↔ word ∈ CNFSAT := by
  change (searchWord word).1 = true ↔ ∃ F, decode word = some F ∧ CNF.Satisfiable F
  cases h : decode word <;> simp [searchWord, h, searchFormula_accepts_iff]

theorem searchFormula_checks_le (F : CNF.Formula Nat) :
    (searchFormula F).2 ≤ 2 ^ (occurringIndices F).length :=
  searchAssignments_checks_le ..

/-- On an unsatisfiable formula the traversal checks every assignment to the occurring names. -/
theorem searchFormula_checks_eq_of_unsatisfiable (F : CNF.Formula Nat)
    (h : ¬ CNF.Satisfiable F) : (searchFormula F).2 = 2 ^ (occurringIndices F).length := by
  have failed : (searchFormula F).1 = false := by
    cases hv : (searchFormula F).1
    · rfl
    · exact (h ((searchFormula_accepts_iff F).mp hv)).elim
  exact searchAssignments_checks_eq_of_rejected _ _ _ failed

private theorem le_sqrt_of_square_le {k n : Nat} (h : k ^ 2 ≤ n) : k ≤ n.sqrt := by
  by_contra! hn
  have hk : n.sqrt + 1 ≤ k := hn
  have hMul := Nat.mul_le_mul hk hk
  rw [Nat.pow_two] at h
  exact (Nat.not_lt_of_ge (Nat.le_trans hMul h)) (Nat.lt_succ_sqrt n)

/-- At most `2^⌊√(2n)⌋` complete assignments are checked on an `n`-bit input. -/
theorem searchWord_checks_le (word : BinaryWord) :
    (searchWord word).2 ≤ 2 ^ (2 * word.length).sqrt := by
  cases h : decode word with
  | none => simp [searchWord, h]
  | some F =>
    rw [searchWord, h, CNFCode.decode_eq_some_iff.mp h]
    exact (searchFormula_checks_le F).trans (Nat.pow_le_pow_right (by decide) <|
      le_sqrt_of_square_le (CNFCode.occurringIndices_length_sq_le F))

end PvsNP.SATAssignment
