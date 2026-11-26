module

public import PvsNP.SAT.CrossingFamily

import PvsNP.SAT.AssignmentSearch

/-! # Equal-width CNF blocks with fresh-variable padding -/

public section

namespace PvsNP.SATCrossing

open CNFCode (encode literalIndex)

/-- The code length of a clause block, excluding the formula terminator. -/
@[expose] def rawBlockLength (F : CNF.Formula Nat) : Nat := (encode F).dropLast.length

theorem rawBlockLength_eq (F : CNF.Formula Nat) :
    rawBlockLength F = 2 * F.length + (F.flatten.map fun l ↦ literalIndex l + 3).sum := by
  rw [rawBlockLength, List.length_dropLast, CNFCode.length_encode_eq]
  omega

theorem rawBlockLength_append (F G : CNF.Formula Nat) :
    rawBlockLength (F ++ G) = rawBlockLength F + rawBlockLength G := by
  rw [rawBlockLength, ← dropLast_encode_append F G,
    List.dropLast_append_of_ne_nil (encode_ne_nil G)]
  exact List.length_append

private theorem rawBlockLength_positive_unit (i : Nat) :
    rawBlockLength [[.pos i]] = i + 5 := by
  simp [rawBlockLength_eq, literalIndex]
  omega

/-- Complete a block to width `B` with a positive unit whose index fills the remaining space. -/
@[expose] def padFormula (B : Nat) (F : CNF.Formula Nat) : CNF.Formula Nat :=
  F ++ [[.pos (B - (rawBlockLength F + 5))]]

theorem rawBlockLength_padFormula (B : Nat) (F : CNF.Formula Nat)
    (hFit : rawBlockLength F + 5 ≤ B) : rawBlockLength (padFormula B F) = B := by
  rw [padFormula, rawBlockLength_append, rawBlockLength_positive_unit]
  omega

/-- Setting fresh variables true satisfies the added units and any middle
formula whose satisfaction is guaranteed by those values. -/
theorem satisfiable_padFormula_with_middle_iff (B m : Nat) (F G H : CNF.Formula Nat)
    (hMiddle : ∀ σ : Nat → Bool, (∀ i, m ≤ i → σ i = true) → CNF.Sat σ H)
    (hVarsF : ∀ c ∈ F, ∀ l ∈ c, literalIndex l < m)
    (hVarsG : ∀ c ∈ G, ∀ l ∈ c, literalIndex l < m)
    (hFitF : rawBlockLength F + 5 + m ≤ B) (hFitG : rawBlockLength G + 5 + m ≤ B) :
    CNF.Satisfiable (padFormula B F ++ H ++ padFormula B G) ↔
      CNF.Satisfiable (F ++ G) := by
  simp only [padFormula, List.append_assoc, CNF.Satisfiable, CNF.sat_append,
    CNF.sat_unit, CNF.Literal.sat_pos]
  constructor
  · rintro ⟨σ, hF, _, _, hG, _⟩
    exact ⟨σ, hF, hG⟩
  · rintro ⟨σ, hF, hG⟩
    let τ (i : Nat) : Bool := if i < m then σ i else true
    have hAgree (H : CNF.Formula Nat) (hVars : ∀ c ∈ H, ∀ l ∈ c, literalIndex l < m) :
        ∀ i ∈ CNFCode.occurringIndices H, σ i = τ i := by
      intro i hi
      obtain ⟨c, hc, l, hl, rfl⟩ := CNFCode.mem_occurringIndices_iff.mp hi
      exact (ite_eq_left (hVars c hc l hl)).symm
    have hF' := (SATAssignment.sat_congr_on_occurringIndices F (hAgree F hVarsF)).mp hF
    have hG' := (SATAssignment.sat_congr_on_occurringIndices G (hAgree G hVarsG)).mp hG
    refine ⟨τ, hF', ?_, hMiddle τ (fun i hi ↦ ite_eq_right (Nat.not_lt.mpr hi)), hG', ?_⟩
    · exact ite_eq_right (by omega)
    · exact ite_eq_right (by omega)

theorem satisfiable_padFormula_pair_iff (B p m : Nat) (F G : CNF.Formula Nat)
    (hVarsF : ∀ c ∈ F, ∀ l ∈ c, literalIndex l < m)
    (hVarsG : ∀ c ∈ G, ∀ l ∈ c, literalIndex l < m)
    (hFitF : rawBlockLength F + 5 + m ≤ B) (hFitG : rawBlockLength G + 5 + m ≤ B) :
    CNF.Satisfiable (padFormula B F ++ paddingFormula p ++ padFormula B G) ↔
      CNF.Satisfiable (F ++ G) :=
  satisfiable_padFormula_with_middle_iff B m F G (paddingFormula p)
    (fun σ _ ↦ paddingFormula_sat p σ) hVarsF hVarsG hFitF hFitG

end PvsNP.SATCrossing
