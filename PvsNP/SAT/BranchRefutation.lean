module

public import PvsNP.SAT.CNF

/-! # Refutation trees with clause conflicts at leaves

The variable at each branch may depend on the formula and the entire current
path. Both children must refute the formula under their corresponding values.
A path can end as soon as its partial assignment falsifies an input clause.
-/

@[expose] public section

namespace PvsNP.SATBranching

open CNF (Clause Formula Literal)

variable {α : Type}

/-- Assigned variables have a Boolean value, and the remaining variables have `none`. -/
abbrev PartialAssignment (α : Type) := α → Option Bool

/-- Give one variable a value and preserve every other assignment. -/
def assign [DecidableEq α] (p : PartialAssignment α) (v : α) (b : Bool) :
    PartialAssignment α :=
  fun u ↦ if u = v then some b else p u

@[simp] theorem assign_same [DecidableEq α] (p : PartialAssignment α) (v : α) (b : Bool) :
    assign p v b v = some b := by simp [assign]

@[simp] theorem assign_other [DecidableEq α] (p : PartialAssignment α) {u v : α} (b : Bool)
    (h : u ≠ v) : assign p v b u = p u := by simp [assign, h]

/-- A literal is falsified when its variable is assigned the opposite truth value. -/
def LiteralFalsified (p : PartialAssignment α) : Literal α → Prop
  | .pos a => p a = some false
  | .neg a => p a = some true

/-- A clause is falsified when every literal has been assigned and is false. -/
def Falsified (p : PartialAssignment α) (c : Clause α) : Prop :=
  ∀ l ∈ c, LiteralFalsified p l

/-- A binary tree of decisions and terminal conflicts. -/
inductive Tree (α : Type) where
  | leaf
  | branch (v : α) (onFalse onTrue : Tree α)

/-- The number of terminal leaves in the tree. -/
def Tree.leaves : Tree α → Nat
  | .leaf => 1
  | .branch _ onFalse onTrue => onFalse.leaves + onTrue.leaves

theorem Tree.leaves_pos (tree : Tree α) : 0 < tree.leaves := by
  induction tree with
  | leaf => exact Nat.zero_lt_succ 0
  | branch _ onFalse onTrue ihFalse _ =>
    exact Nat.lt_of_lt_of_le ihFalse (Nat.le_add_right onFalse.leaves onTrue.leaves)

/-- Every branch assigns a fresh variable and every leaf has an input-clause conflict. -/
inductive Refutes [DecidableEq α] (F : Formula α) : PartialAssignment α → Tree α → Prop where
  | leaf {p} (conflict : ∃ c ∈ F, Falsified p c) : Refutes F p .leaf
  | branch {p v onFalse onTrue} (fresh : p v = none)
      (onFalse_refutes : Refutes F (assign p v false) onFalse)
      (onTrue_refutes : Refutes F (assign p v true) onTrue) :
      Refutes F p (.branch v onFalse onTrue)

/-- A Boolean assignment agrees with every defined value of a partial assignment. -/
def Extends (σ : α → Bool) (p : PartialAssignment α) : Prop :=
  ∀ v b, p v = some b → σ v = b

private theorem extends_assign [DecidableEq α] {σ : α → Bool} {p : PartialAssignment α}
    (h : Extends σ p) (v : α) : Extends σ (assign p v (σ v)) := by
  intro u b hValue
  by_cases e : u = v
  · subst u
    exact Option.some.inj (by simpa only [assign_same] using hValue)
  · exact h u b (by simpa only [assign_other p (σ v) e] using hValue)

/-- A refutation rules out every satisfying assignment extending its initial values. -/
theorem Refutes.no_satisfying_extension [DecidableEq α] {F : Formula α}
    {p : PartialAssignment α} {tree : Tree α} {σ : α → Bool}
    (h : Refutes F p tree) (hExt : Extends σ p) : ¬ CNF.Sat σ F := by
  induction h with
  | leaf hConflict =>
    intro hSat
    obtain ⟨c, hc, hFalsified⟩ := hConflict
    obtain ⟨l, hl, hLiteral⟩ := hSat c hc
    have hf := hFalsified l hl
    cases l with
    | pos v =>
      have hv := hExt v false hf
      simp [hv] at hLiteral
    | neg v =>
      have hv := hExt v true hf
      simp [hv] at hLiteral
  | @branch p v _ _ _ _ _ ihFalse ihTrue =>
    have hNext := extends_assign hExt v
    cases e : σ v with
    | false => exact ihFalse (e ▸ hNext)
    | true => exact ihTrue (e ▸ hNext)

/-- All literals except the indicated fresh literal have already been falsified. -/
def UnitForces (p : PartialAssignment α) (c : Clause α) (v : α) (b : Bool) : Prop :=
  let unit : Literal α := if b then .pos v else .neg v
  p v = none ∧ unit ∈ c ∧ ∀ l ∈ c, l ≠ unit → LiteralFalsified p l

private theorem falsified_assign_fresh [DecidableEq α] {p : PartialAssignment α}
    {v : α} {b : Bool} {l : Literal α} (hFresh : p v = none)
    (h : LiteralFalsified p l) : LiteralFalsified (assign p v b) l := by
  have hAssign (u : α) (x : Bool) (hu : p u = some x) : assign p v b u = some x := by
    by_cases e : u = v
    · subst u
      simp [hFresh] at hu
    · exact (assign_other p b e).trans hu
  cases l <;> exact hAssign _ _ h

/-- The value opposite to a forced unit immediately falsifies its clause. -/
theorem UnitForces.falsified_on_opposite [DecidableEq α] {p : PartialAssignment α}
    {c : Clause α} {v : α} {b : Bool} (h : UnitForces p c v b) :
    Falsified (assign p v (!b)) c := by
  intro l hl
  by_cases e : l = if b then .pos v else .neg v
  · subst l
    cases b <;> simp [LiteralFalsified]
  · exact falsified_assign_fresh h.1 (h.2.2 l hl e)

/-- Expand one unit inference into a branch with an immediate conflict on one side. -/
def Tree.force (v : α) : Bool → Tree α → Tree α
  | false, child => .branch v child .leaf
  | true, child => .branch v .leaf child

@[simp] theorem Tree.leaves_force (v : α) (b : Bool) (child : Tree α) :
    (Tree.force v b child).leaves = child.leaves + 1 := by
  cases b <;> simp [Tree.force, Tree.leaves, Nat.add_comm]

/-- Unit propagation preserves a refutation and adds one conflict leaf. -/
theorem Refutes.of_unit [DecidableEq α] {F : Formula α} {p : PartialAssignment α}
    {c : Clause α} {v : α} {b : Bool} {tree : Tree α} (hc : c ∈ F) (hUnit : UnitForces p c v b)
    (h : Refutes F (assign p v b) tree) : Refutes F p (Tree.force v b tree) := by
  have contra : Refutes F (assign p v (!b)) .leaf := .leaf ⟨c, hc, hUnit.falsified_on_opposite⟩
  cases b with
  | false => exact .branch hUnit.1 h contra
  | true => exact .branch hUnit.1 contra h

/-- A forced response need not spend score. Two supported responses may each spend one point.
No input clause is falsified below the target score `n`. -/
structure Strategy [DecidableEq α] (F : Formula α) (n : Nat) where
  State : Type
  value : State → PartialAssignment α
  score : State → Nat
  noConflict : ∀ s, score s < n → ¬ ∃ c ∈ F, Falsified (value s) c
  respond : ∀ s v, value s v = none →
    (∃ b t, value t = assign (value s) v b ∧ score t ≤ score s) ∨
    ((∃ t, value t = assign (value s) v false ∧ score t ≤ score s + 1) ∧
      (∃ t, value t = assign (value s) v true ∧ score t ≤ score s + 1))

/-- Each unit of remaining score doubles the leaf lower bound for a refutation. -/
theorem Strategy.leaves_lower_bound [DecidableEq α] {F : Formula α} {n : Nat}
    (strategy : Strategy F n) (s : strategy.State) {tree : Tree α}
    (h : Refutes F (strategy.value s) tree) : 2 ^ (n - strategy.score s) ≤ tree.leaves := by
  induction tree generalizing s with
  | leaf =>
    cases h with
    | leaf hConflict =>
      have hs : n ≤ strategy.score s :=
        Nat.le_of_not_gt (fun hScore ↦ strategy.noConflict s hScore hConflict)
      simp [Tree.leaves, Nat.sub_eq_zero_of_le hs]
  | branch v onFalse onTrue ihFalse ihTrue =>
    by_cases hs : n ≤ strategy.score s
    · simpa only [Nat.sub_eq_zero_of_le hs, Nat.pow_zero] using
        Nat.succ_le_of_lt (Tree.leaves_pos (.branch v onFalse onTrue))
    cases h with
    | branch fresh hFalse hTrue =>
      rcases strategy.respond s v fresh with ⟨b, t, hValues, hScore⟩ | ⟨hNextFalse, hNextTrue⟩
      · have hPower : 2 ^ (n - strategy.score s) ≤ 2 ^ (n - strategy.score t) :=
          Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_left hScore n)
        cases b with
        | false =>
          exact Nat.le_trans (Nat.le_trans hPower (ihFalse t (hValues.symm ▸ hFalse)))
            (Nat.le_add_right ..)
        | true =>
          exact Nat.le_trans (Nat.le_trans hPower (ihTrue t (hValues.symm ▸ hTrue)))
            (Nat.le_add_left ..)
      · obtain ⟨tFalse, hValuesFalse, hScoreFalse⟩ := hNextFalse
        obtain ⟨tTrue, hValuesTrue, hScoreTrue⟩ := hNextTrue
        have hPow (t : strategy.State) (hScore : strategy.score t ≤ strategy.score s + 1) :
            2 ^ (n - (strategy.score s + 1)) ≤ 2 ^ (n - strategy.score t) :=
          Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_left hScore n)
        have hExponent : n - strategy.score s = n - (strategy.score s + 1) + 1 := by omega
        rw [hExponent, Nat.pow_succ, Nat.mul_two, Tree.leaves]
        exact Nat.add_le_add
          (Nat.le_trans (hPow tFalse hScoreFalse) (ihFalse tFalse (hValuesFalse.symm ▸ hFalse)))
          (Nat.le_trans (hPow tTrue hScoreTrue) (ihTrue tTrue (hValuesTrue.symm ▸ hTrue)))

end PvsNP.SATBranching
