module

public import PvsNP.SAT.AssignmentSearch

import Init.Data.List.Perm

/-! # Unsatisfiable inputs for exhaustive assignment search

One negative unit clause contradicts a positive unit clause on index zero.
The other positive unit clauses bring the number of occurring indices to any
desired positive value while keeping the binary input length quadratic.
-/

@[expose] public section

namespace PvsNP.AssignmentSearch

open CNF CNFCode

/-- An unsatisfiable formula on the indices from zero to `k`, inclusive. -/
def unsatFamily (k : Nat) : Formula Nat :=
  [.neg 0] :: (List.range (k + 1)).map fun a ↦ [.pos a]

theorem unsatFamily_not_satisfiable (k : Nat) : ¬ Satisfiable (unsatFamily k) := by
  rintro ⟨σ, hσ⟩
  obtain ⟨hneg, hpos⟩ := (sat_cons ..).mp hσ
  have hfalse : σ 0 = false := (Clause.sat_singleton ..).mp hneg
  have htrue : σ 0 = true := by
    have h := (sat_map ..).mp hpos 0 (List.mem_range.mpr (Nat.zero_lt_succ k))
    exact (Clause.sat_singleton ..).mp h
  simp [hfalse] at htrue

theorem unsatFamily_noEmptyClause (k : Nat) : ([] : Clause Nat) ∉ unsatFamily k := by
  simp [unsatFamily, List.mem_map]

theorem unsatFamily_occurs_iff (k a : Nat) :
    (∃ c ∈ unsatFamily k, ∃ l ∈ c, literalIndex l = a) ↔ a < k + 1 := by
  constructor
  · rintro ⟨c, hc, l, hl, rfl⟩
    rcases List.mem_cons.mp hc with rfl | hc
    · obtain rfl := List.mem_singleton.mp hl
      exact Nat.zero_lt_succ k
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
      obtain rfl := List.mem_singleton.mp hl
      exact List.mem_range.mp hb
  · intro ha
    exact ⟨[.pos a], List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_range.mpr ha)),
      .pos a, List.mem_singleton_self _, rfl⟩

/-- The deduplicated list contains exactly one entry per index from zero to `k`. -/
theorem unsatFamily_occurringIndices_length (k : Nat) :
    (occurringIndices (unsatFamily k)).length = k + 1 := by
  have h (a : Nat) : a ∈ occurringIndices (unsatFamily k) ↔ a ∈ List.range (k + 1) :=
    mem_occurringIndices_iff.trans ((unsatFamily_occurs_iff k a).trans List.mem_range.symm)
  have hle : (occurringIndices (unsatFamily k)).length ≤ (List.range (k + 1)).length :=
    (occurringIndices_nodup _).length_le_of_subset fun {a} ↦ (h a).mp
  have hge : (List.range (k + 1)).length ≤ (occurringIndices (unsatFamily k)).length :=
    List.nodup_range.length_le_of_subset fun {a} ↦ (h a).mpr
  simpa only [List.length_range] using Nat.le_antisymm hle hge

/-- The bit length of the unsatisfiable family is bounded quadratically. -/
theorem length_encode_unsatFamily_le (k : Nat) :
    (encode (unsatFamily k)).length ≤ 1 + (k + 3) * (2 + (k + 1) * 2) := by
  have hSize : size (unsatFamily k) = 2 + (k + 1) * 2 := by
    rw [unsatFamily, size_cons, size_map_of_length _ _ 1 (fun _ _ ↦ rfl), List.length_range]
    rfl
  rw [← hSize]
  refine length_encode_le _ _ fun c hc l hl ↦ ?_
  exact Nat.le_of_lt_succ ((unsatFamily_occurs_iff k (literalIndex l)).mp ⟨c, hc, l, hl, rfl⟩)

theorem length_encode_unsatFamily_polynomiallyBounded :
    PolynomiallyBounded (fun k ↦ (encode (unsatFamily k)).length) :=
  let c := PolynomiallyBounded.const
  let n := PolynomiallyBounded.id
  ((c 1).add ((n.add (c 3)).mul ((c 2).add ((n.add (c 1)).mul (c 2))))).mono
    length_encode_unsatFamily_le

theorem encode_unsatFamily_not_mem_CNFSAT (k : Nat) : encode (unsatFamily k) ∉ CNFSAT :=
  fun h ↦ unsatFamily_not_satisfiable k ((encode_mem_CNFSAT_iff _).mp h)

/-- Exhaustively trying the assignments on this family cannot have a polynomial
bound in the binary lengths. The count here is of complete assignments. -/
theorem no_polynomial_bound_for_unsatFamily_trials :
    ¬ ∃ f : Nat → Nat, PolynomiallyBounded f ∧
      ∀ k, 2 ^ (k + 1) ≤ f (encode (unsatFamily k)).length := by
  rintro ⟨f, hf, hTrials⟩
  apply pow_two_not_polynomiallyBounded
  apply (hf.comp length_encode_unsatFamily_polynomiallyBounded).mono
  intro k
  exact (Nat.pow_le_pow_right (by decide) (Nat.le_succ k)).trans (hTrials k)

theorem searchWord_checks_encode_unsatFamily (k : Nat) :
    (SATAssignment.searchWord (encode (unsatFamily k))).2 = 2 ^ (k + 1) := by
  simp only [SATAssignment.searchWord_encode,
    SATAssignment.searchFormula_checks_eq_of_unsatisfiable _ (unsatFamily_not_satisfiable k),
    unsatFamily_occurringIndices_length]

/-- No polynomial in the input length bounds the assignment checks of this search. -/
theorem no_polynomial_bound_for_searchWord_checks :
    ¬ ∃ f : Nat → Nat, PolynomiallyBounded f ∧
      ∀ word : BinaryWord, (SATAssignment.searchWord word).2 ≤ f word.length := by
  rintro ⟨f, hf, hSearch⟩
  apply no_polynomial_bound_for_unsatFamily_trials
  refine ⟨f, hf, fun k ↦ ?_⟩
  simpa only [searchWord_checks_encode_unsatFamily] using hSearch (encode (unsatFamily k))

end PvsNP.AssignmentSearch
