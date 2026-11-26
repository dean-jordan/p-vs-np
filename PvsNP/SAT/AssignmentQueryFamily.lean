module

public import PvsNP.SAT.AssignmentSearchFamily

/-! # Matched binary CNF words for complete-assignment queries

The satisfiable members force one assignment each. Their clause sizes and
ordered variable occurrences agree with the unsatisfiable family.
-/

@[expose] public section

namespace PvsNP.AssignmentQueryFamily

open CNF CNFCode

/-- The unit literal requiring an index to have the supplied value. -/
def setting (i : Nat) (value : Bool) : Literal Nat :=
  if value then .pos i else .neg i

@[simp] private theorem literalIndex_setting (i : Nat) (value : Bool) :
    literalIndex (setting i value) = i := by
  cases value <;> rfl

private theorem setting_sat_iff (τ : Nat → Bool) (i : Nat) (value : Bool) :
    (setting i value).Sat τ ↔ τ i = value := by
  cases value <;> rfl

/-- Force each value by a unit clause, with the clause on zero repeated first. -/
def uniqueFormula {k : Nat} (σ : Fin (k + 1) → Bool) : Formula Nat :=
  [setting 0 (σ 0)] :: List.ofFn (fun i ↦ [setting i.val (σ i)])

/-- Encode the complete CNF for a particular assignment. -/
def uniqueWord {k : Nat} (σ : Fin (k + 1) → Bool) : BinaryWord := encode (uniqueFormula σ)

/-- Encode the unsatisfiable formula with conflicting unit clauses on index zero. -/
def impossibleWord (k : Nat) : BinaryWord := encode (AssignmentSearch.unsatFamily k)

/-- Supply exactly one bit for each index from zero through `k`. -/
def assignmentWord {k : Nat} (u : Fin (k + 1) → Bool) : BinaryWord := List.ofFn u

theorem lookup_assignmentWord {k : Nat} (u : Fin (k + 1) → Bool) (i : Fin (k + 1)) :
    SATAssignment.lookup (assignmentWord u) i.val = u i := by
  simp only [SATAssignment.lookup, assignmentWord, List.getElem?_ofFn, dite_eq_left i.isLt,
    Option.getD_some]

/-- Satisfying assignments agree with the chosen values on every occurring name. -/
theorem sat_uniqueFormula_iff {k : Nat} (σ : Fin (k + 1) → Bool) (τ : Nat → Bool) :
    Sat τ (uniqueFormula σ) ↔ ∀ i : Fin (k + 1), τ i.val = σ i := by
  simp only [uniqueFormula, sat_cons, Clause.sat_singleton, setting_sat_iff]
  constructor
  · intro h i
    have hUnit := h.2 [setting i.val (σ i)] (List.mem_ofFn.mpr ⟨i, rfl⟩)
    exact (setting_sat_iff ..).mp ((Clause.sat_singleton ..).mp hUnit)
  · intro h
    refine ⟨h 0, ?_⟩
    intro c hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    exact (Clause.sat_singleton ..).mpr ((setting_sat_iff ..).mpr (h i))

/-- The binary checker answers true exactly at the assignment used for this word. -/
theorem checkWord_uniqueWord_eq_true_iff {k : Nat} (σ u : Fin (k + 1) → Bool) :
    SATAssignment.checkWord (uniqueWord σ) (assignmentWord u) = true ↔ u = σ := by
  simp only [uniqueWord, SATAssignment.checkWord, decode_encode,
    SATAssignment.checkFormula_eq_true_iff, sat_uniqueFormula_iff, lookup_assignmentWord]
  exact ⟨funext, fun h i ↦ congrFun h i⟩

/-- The impossible word answers false at every tested assignment. -/
theorem checkWord_impossibleWord (k : Nat) (u : Fin (k + 1) → Bool) :
    SATAssignment.checkWord (impossibleWord k) (assignmentWord u) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  simp only [impossibleWord, SATAssignment.checkWord, decode_encode,
    SATAssignment.checkFormula_eq_true_iff] at h
  exact AssignmentSearch.unsatFamily_not_satisfiable k ⟨_, h⟩

theorem uniqueWord_mem_CNFSAT {k : Nat} (σ : Fin (k + 1) → Bool) : uniqueWord σ ∈ CNFSAT := by
  apply (encode_mem_CNFSAT_iff _).mpr
  exact ⟨SATAssignment.lookup (assignmentWord σ),
    (sat_uniqueFormula_iff ..).mpr (lookup_assignmentWord σ)⟩

theorem impossibleWord_not_mem_CNFSAT (k : Nat) : impossibleWord k ∉ CNFSAT :=
  AssignmentSearch.encode_unsatFamily_not_mem_CNFSAT k

private theorem flatten_map_singletons {α β : Type} (xs : List α) (f : α → β) :
    (xs.map fun x ↦ [f x]).flatten = xs.map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

private theorem flatten_ofFn_singletons {α : Type} {n : Nat} (f : Fin n → α) :
    (List.ofFn fun i ↦ [f i]).flatten = List.ofFn f := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.ofFn_succ, List.flatten_cons, List.singleton_append, ih]

private theorem ofFn_val_eq_range (n : Nat) :
    (List.ofFn fun i : Fin n ↦ i.val) = List.range n := by
  apply List.ext_getElem <;> simp

private theorem literalIndices_uniqueFormula {k : Nat} (σ : Fin (k + 1) → Bool) :
    (uniqueFormula σ).flatten.map literalIndex = 0 :: List.range (k + 1) := by
  simp only [uniqueFormula, List.flatten_cons, List.singleton_append, flatten_ofFn_singletons,
    List.map_cons, literalIndex_setting, List.map_ofFn, Function.comp_def, ofFn_val_eq_range]

private theorem literalIndices_unsatFamily (k : Nat) :
    (AssignmentSearch.unsatFamily k).flatten.map literalIndex = 0 :: List.range (k + 1) := by
  have h : (literalIndex ∘ Literal.pos : Nat → Nat) = id := rfl
  simp [AssignmentSearch.unsatFamily, flatten_map_singletons, literalIndex, h]

/-- Both kinds of formula expose the same ordered list of occurring indices. -/
theorem occurringIndices_uniqueFormula_eq_unsatFamily {k : Nat} (σ : Fin (k + 1) → Bool) :
    occurringIndices (uniqueFormula σ) = occurringIndices (AssignmentSearch.unsatFamily k) := by
  simp only [occurringIndices, literalIndices_uniqueFormula, literalIndices_unsatFamily]

/-- Changing the signs of the unit clauses leaves the bit length unchanged. -/
theorem uniqueWord_length_eq_impossibleWord_length {k : Nat} (σ : Fin (k + 1) → Bool) :
    (uniqueWord σ).length = (impossibleWord k).length := by
  have costs (F : Formula Nat) :
      (F.flatten.map fun l ↦ literalIndex l + 3) = (F.flatten.map literalIndex).map (· + 3) := by
    rw [List.map_map]
    rfl
  rw [uniqueWord, impossibleWord, length_encode_eq, length_encode_eq, costs, costs,
    literalIndices_uniqueFormula, literalIndices_unsatFamily]
  simp only [uniqueFormula, AssignmentSearch.unsatFamily, List.length_cons, List.length_ofFn,
    List.length_map, List.length_range]

theorem impossibleWord_length_polynomiallyBounded :
    PolynomiallyBounded (fun k ↦ (impossibleWord k).length) :=
  AssignmentSearch.length_encode_unsatFamily_polynomiallyBounded

end PvsNP.AssignmentQueryFamily
