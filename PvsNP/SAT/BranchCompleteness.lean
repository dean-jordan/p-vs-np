module

public import PvsNP.SAT.BranchRefutation

/-! # Completeness of conflict branching for finite CNFs -/

@[expose] public section

namespace PvsNP.SATBranching

open CNF (Formula Literal)

variable {α : Type}

/-- The variable of a literal, independent of its sign. -/
def literalVariable : Literal α → α
  | .pos v => v
  | .neg v => v

/-- Every variable occurring in the formula is already assigned or remains to be queried. -/
def Covers (F : Formula α) (p : PartialAssignment α) (pending : List α) : Prop :=
  ∀ c ∈ F, ∀ l ∈ c, p (literalVariable l) ≠ none ∨ literalVariable l ∈ pending

/-- Traverse both values of each pending fresh variable. -/
def exhaustiveTree [DecidableEq α] : List α → PartialAssignment α → Tree α
  | [], _ => .leaf
  | v :: pending, p =>
    match p v with
    | some _ => exhaustiveTree pending p
    | none => .branch v (exhaustiveTree pending (assign p v false))
        (exhaustiveTree pending (assign p v true))

private theorem falsified_of_not_sat {p : PartialAssignment α} (l : Literal α)
    (hAssigned : p (literalVariable l) ≠ none)
    (hFalse : ¬ l.Sat (fun v ↦ (p v).getD false)) : LiteralFalsified p l := by
  cases l <;> rename_i v <;> cases h : p v
  all_goals
    simp only [literalVariable] at hAssigned
    first
    | exact (hAssigned h).elim
    | rename_i b
      cases b <;> simp_all [LiteralFalsified]

/-- A covering search tree refutes the formula when the partial assignment has no
satisfying extension. -/
theorem refutes_exhaustiveTree [DecidableEq α] (pending : List α) {F : Formula α}
    {p : PartialAssignment α} (hCover : Covers F p pending)
    (hUnsat : ∀ σ, Extends σ p → ¬ CNF.Sat σ F) : Refutes F p (exhaustiveTree pending p) := by
  induction pending generalizing p with
  | nil =>
    let σ (v : α) := (p v).getD false
    have hExt : Extends σ p := by
      intro v b h
      simp [σ, h]
    have hConflict : ∃ c ∈ F, ¬ CNF.Clause.Sat σ c := by
      apply Classical.byContradiction
      intro hNone
      apply hUnsat σ hExt
      intro c hc
      exact Classical.byContradiction fun hFalse ↦ hNone ⟨c, hc, hFalse⟩
    obtain ⟨c, hc, hFalse⟩ := hConflict
    exact .leaf ⟨c, hc, fun l hl ↦
      falsified_of_not_sat l ((hCover c hc l hl).resolve_right List.not_mem_nil)
        (fun hSat ↦ hFalse ⟨l, hl, hSat⟩)⟩
  | cons v pending ih =>
    cases hv : p v with
    | some b =>
      rw [exhaustiveTree, hv]
      apply ih _ hUnsat
      intro c hc l hl
      by_cases e : literalVariable l = v
      · simp [e, hv]
      · simpa only [List.mem_cons, e, false_or] using hCover c hc l hl
    | none =>
      have hChild (b : Bool) : Refutes F (assign p v b) (exhaustiveTree pending (assign p v b)) := by
        apply ih
        · intro c hc l hl
          by_cases e : literalVariable l = v
          · simp [e]
          · simpa only [List.mem_cons, e, false_or, assign_other p b e] using hCover c hc l hl
        · intro σ hExt
          apply hUnsat σ
          intro u bit h
          have e : u ≠ v := by
            rintro rfl
            simp [hv] at h
          exact hExt u bit ((assign_other p b e).trans h)
      rw [exhaustiveTree, hv]
      exact .branch hv (hChild false) (hChild true)

/-- A list of every variable occurrence, in formula order. -/
def formulaVariables (F : Formula α) : List α := F.flatten.map literalVariable

theorem formulaVariables_covers (F : Formula α) (p : PartialAssignment α) :
    Covers F p (formulaVariables F) := by
  intro c hc l hl
  exact Or.inr (List.mem_map_of_mem (List.mem_flatten.mpr ⟨c, hc, hl⟩))

/-- The exhaustive tree starting with no assignments refutes every unsatisfiable formula. -/
theorem refutes_formulaVariables [DecidableEq α] {F : Formula α}
    (h : ¬ CNF.Satisfiable F) : Refutes F (fun _ ↦ none)
      (exhaustiveTree (formulaVariables F) (fun _ ↦ none)) :=
  refutes_exhaustiveTree _ (formulaVariables_covers _ _) (fun σ _ hSat ↦ h ⟨σ, hSat⟩)

/-- Conflict branching is sound and complete for finite CNFs. -/
theorem exists_refutation_iff_not_satisfiable [DecidableEq α] (F : Formula α) :
    (∃ tree, Refutes F (fun _ ↦ none) tree) ↔ ¬ CNF.Satisfiable F := by
  constructor
  · rintro ⟨_, h⟩ ⟨σ, hSat⟩
    have hExt : Extends σ (fun _ ↦ none) := fun _ _ hValue ↦ by cases hValue
    exact h.no_satisfying_extension hExt hSat
  · intro h
    exact ⟨_, refutes_formulaVariables h⟩

end PvsNP.SATBranching
