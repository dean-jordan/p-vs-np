module

public import PvsNP.SAT.BranchCompleteness

/-! # Refutation traces with unit propagation

A trace records both branches of a decision and the surviving branch of a
unit propagation. Unit propagation expands to a decision whose discarded
branch ends in a conflict with the clause that forced the assignment.
-/

@[expose] public section

namespace PvsNP.SATBranching

variable {α : Type}

/-- A trace records decisions, unit propagations, and terminal conflicts. -/
inductive PropagationTree (α : Type) where
  | leaf
  | branch (v : α) (onFalse onTrue : PropagationTree α)
  | unit (v : α) (b : Bool) (next : PropagationTree α)

/-- Count the events in a trace. -/
def PropagationTree.nodes : PropagationTree α → Nat
  | .leaf => 1
  | .branch _ onFalse onTrue => onFalse.nodes + onTrue.nodes + 1
  | .unit _ _ next => next.nodes + 1

/-- Expose the discarded branch of each unit propagation as a conflict leaf. -/
def PropagationTree.toTree : PropagationTree α → Tree α
  | .leaf => .leaf
  | .branch v onFalse onTrue => .branch v onFalse.toTree onTrue.toTree
  | .unit v b next => Tree.force v b next.toTree

theorem PropagationTree.leaves_toTree_le_nodes (trace : PropagationTree α) :
    trace.toTree.leaves ≤ trace.nodes := by
  induction trace with
  | leaf => exact Nat.le_refl 1
  | branch v onFalse onTrue ihFalse ihTrue =>
    exact Nat.le_trans (Nat.add_le_add ihFalse ihTrue) (Nat.le_add_right ..)
  | unit v b next ih =>
    simp only [toTree, Tree.leaves_force, nodes]
    exact Nat.add_le_add_right ih 1

/-- Each decision covers both values of a fresh variable. Each unit propagation has
an input clause forcing its chosen value, and each leaf has an input-clause conflict. -/
inductive PropagationRefutes [DecidableEq α] (F : CNF.Formula α) :
    PartialAssignment α → PropagationTree α → Prop where
  | leaf {p} (conflict : ∃ c ∈ F, Falsified p c) : PropagationRefutes F p .leaf
  | branch {p v onFalse onTrue} (fresh : p v = none)
      (hFalse : PropagationRefutes F (assign p v false) onFalse)
      (hTrue : PropagationRefutes F (assign p v true) onTrue) :
      PropagationRefutes F p (.branch v onFalse onTrue)
  | unit {p c v b next} (reason : c ∈ F) (forced : UnitForces p c v b)
      (hNext : PropagationRefutes F (assign p v b) next) :
      PropagationRefutes F p (.unit v b next)

/-- Expanding a valid propagation trace yields a valid binary conflict tree. -/
theorem PropagationRefutes.toTree [DecidableEq α] {F : CNF.Formula α}
    {p : PartialAssignment α} {trace : PropagationTree α} (h : PropagationRefutes F p trace) :
    Refutes F p trace.toTree := by
  induction h with
  | leaf hConflict => exact .leaf hConflict
  | branch hFresh _ _ ihFalse ihTrue => exact .branch hFresh ihFalse ihTrue
  | unit hReason hForced _ ih => exact Refutes.of_unit hReason hForced ih

/-- Ordinary branching refutations are traces with only decision and conflict events. -/
theorem Refutes.exists_propagation_trace [DecidableEq α] {F : CNF.Formula α}
    {p : PartialAssignment α} {tree : Tree α} (h : Refutes F p tree) :
    ∃ trace, PropagationRefutes F p trace := by
  induction h with
  | leaf hConflict => exact ⟨.leaf, .leaf hConflict⟩
  | branch hFresh _ _ ihFalse ihTrue =>
    obtain ⟨onFalse, hFalse⟩ := ihFalse
    obtain ⟨onTrue, hTrue⟩ := ihTrue
    exact ⟨.branch _ onFalse onTrue, .branch hFresh hFalse hTrue⟩

/-- Exactly the unsatisfiable formulas admit a complete propagation refutation. -/
theorem exists_propagation_refutation_iff_not_satisfiable [DecidableEq α] (F : CNF.Formula α) :
    (∃ trace, PropagationRefutes F (fun _ ↦ none) trace) ↔ ¬ CNF.Satisfiable F := by
  rw [← exists_refutation_iff_not_satisfiable F]
  constructor
  · rintro ⟨trace, h⟩
    exact ⟨trace.toTree, h.toTree⟩
  · rintro ⟨_, h⟩
    exact h.exists_propagation_trace

/-- The conflict-tree lower bound is also a lower bound on propagation trace events. -/
theorem Strategy.propagation_nodes_lower_bound [DecidableEq α] {F : CNF.Formula α} {n : Nat}
    (strategy : Strategy F n) (s : strategy.State) {trace : PropagationTree α}
    (h : PropagationRefutes F (strategy.value s) trace) :
    2 ^ (n - strategy.score s) ≤ trace.nodes :=
  Nat.le_trans (strategy.leaves_lower_bound s h.toTree) trace.leaves_toTree_le_nodes

end PvsNP.SATBranching
