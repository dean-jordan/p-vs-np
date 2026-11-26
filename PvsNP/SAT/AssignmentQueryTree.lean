module

public import Init.Data.Fin.Lemmas
public import Init.Data.List.Lemmas

import Init.Data.List.Perm

/-! # Adaptive queries to a Boolean assignment checker

A tree branches only on the answers to assignment queries. The all-false
transcript determines its answer for every oracle agreeing on those queries.
-/

@[expose] public section

namespace PvsNP

/-- A finite deterministic algorithm with access to a Boolean oracle. -/
inductive AssignmentQueryTree (α : Type) where
  | done (accepts : Bool)
  | query (assignment : α) (onFalse onTrue : AssignmentQueryTree α)

namespace AssignmentQueryTree

variable {α : Type}

/-- Evaluate the query tree against the supplied oracle. -/
def run (oracle : α → Bool) : AssignmentQueryTree α → Bool
  | .done accepts => accepts
  | .query assignment onFalse onTrue =>
    if oracle assignment then run oracle onTrue else run oracle onFalse

/-- The queries made when every oracle response is false, including repetitions. -/
def falseQueries : AssignmentQueryTree α → List α
  | .done _ => []
  | .query assignment onFalse _ => assignment :: falseQueries onFalse

/-- Query each assignment in order and accept on the first true answer. -/
def firstSuccess : List α → AssignmentQueryTree α
  | [] => .done false
  | assignment :: rest => .query assignment (firstSuccess rest) (.done true)

theorem run_firstSuccess_eq_true_iff (oracle : α → Bool) (assignments : List α) :
    (firstSuccess assignments).run oracle = true ↔
      ∃ assignment ∈ assignments, oracle assignment = true := by
  induction assignments with
  | nil => simp [firstSuccess, run]
  | cons assignment rest ih =>
    cases h : oracle assignment <;> simp [firstSuccess, run, h, List.mem_cons, ih]

@[simp] theorem falseQueries_firstSuccess (assignments : List α) :
    (firstSuccess assignments).falseQueries = assignments := by
  induction assignments with
  | nil => rfl
  | cons _ _ ih => simp only [firstSuccess, falseQueries, ih]

/-- Agreement along the all-false transcript forces the same result. -/
theorem run_eq_of_falseQueries (tree : AssignmentQueryTree α) (oracle : α → Bool)
    (hFalse : ∀ assignment ∈ tree.falseQueries, oracle assignment = false) :
    tree.run oracle = tree.run (fun _ ↦ false) := by
  induction tree with
  | done => rfl
  | query assignment onFalse _ ih _ =>
    have hHead : oracle assignment = false := hFalse _ (List.mem_cons_self ..)
    have hTail : ∀ a ∈ onFalse.falseQueries, oracle a = false :=
      fun a ha ↦ hFalse a (List.mem_cons_of_mem _ ha)
    simpa only [run, hHead, Bool.false_eq_true, ite_false] using ih hTail

/-- To distinguish a single-point true oracle, the all-false run must query that point. -/
theorem mem_falseQueries_of_accepts_singlePoint (tree : AssignmentQueryTree α)
    (target : α) (oracle : α → Bool)
    (hPoint : ∀ assignment, oracle assignment = true ↔ assignment = target)
    (hReject : tree.run (fun _ ↦ false) = false) (hAccept : tree.run oracle = true) :
    target ∈ tree.falseQueries := by
  apply Classical.byContradiction
  intro hMiss
  have hFalse (assignment : α) (hMem : assignment ∈ tree.falseQueries) :
      oracle assignment = false := by
    cases h : oracle assignment with
    | false => rfl
    | true => exact (hMiss ((hPoint assignment).mp h ▸ hMem)).elim
  have hRun := tree.run_eq_of_falseQueries oracle hFalse
  rw [hAccept, hReject] at hRun
  cases hRun

/-- Enumerate the Boolean assignments to `Fin k`, with the false first bit first. -/
def allAssignments : (k : Nat) → List (Fin k → Bool)
  | 0 => [Fin.elim0]
  | k + 1 =>
    (allAssignments k).map (fun a i ↦ Fin.cases false a i) ++
      (allAssignments k).map (fun a i ↦ Fin.cases true a i)

theorem mem_allAssignments {k : Nat} (assignment : Fin k → Bool) :
    assignment ∈ allAssignments k := by
  induction k with
  | zero =>
    rw [allAssignments, List.mem_singleton]
    exact funext fun i ↦ i.elim0
  | succ k ih =>
    let tail (i : Fin k) := assignment i.succ
    have hPrefix : (fun i ↦ Fin.cases (assignment 0) tail i) = assignment :=
      funext (fun i ↦ Fin.cases rfl (fun _ ↦ rfl) i)
    rw [allAssignments, List.mem_append]
    cases h : assignment 0 with
    | false => exact Or.inl (List.mem_map.mpr ⟨tail, ih tail, h ▸ hPrefix⟩)
    | true => exact Or.inr (List.mem_map.mpr ⟨tail, ih tail, h ▸ hPrefix⟩)

theorem nodup_allAssignments (k : Nat) : (allAssignments k).Nodup := by
  induction k with
  | zero => simp [allAssignments]
  | succ k ih =>
    have hMap (bit : Bool) :
        ((allAssignments k).map (fun a i ↦ Fin.cases (motive := fun _ ↦ Bool) bit a i)).Nodup := by
      apply List.Pairwise.map _ ?_ ih
      intro f g h hEq
      exact h (funext fun i ↦ congrFun hEq i.succ)
    rw [allAssignments, List.nodup_append]
    refine ⟨hMap false, hMap true, ?_⟩
    intro a ha b hb hEq
    obtain ⟨f, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨g, _, rfl⟩ := List.mem_map.mp hb
    have hHead := congrFun hEq 0
    cases hHead

theorem length_allAssignments (k : Nat) : (allAssignments k).length = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [allAssignments, List.length_append, List.length_map, ih,
      Nat.pow_succ, Nat.mul_two]

/-- Rejecting the false oracle while accepting every single-point oracle costs at least `2^k`
queries on the false oracle, even when the choice of query is adaptive. -/
theorem pow_two_le_falseQueries_length {k : Nat} (tree : AssignmentQueryTree (Fin k → Bool))
    (oracles : (Fin k → Bool) → (Fin k → Bool) → Bool)
    (hPoint : ∀ target assignment, oracles target assignment = true ↔ assignment = target)
    (hReject : tree.run (fun _ ↦ false) = false)
    (hAccept : ∀ target, tree.run (oracles target) = true) :
    2 ^ k ≤ tree.falseQueries.length := by
  rw [← length_allAssignments]
  exact (nodup_allAssignments k).length_le_of_subset fun {target} _ ↦
    tree.mem_falseQueries_of_accepts_singlePoint target (oracles target) (hPoint target) hReject
      (hAccept target)

end AssignmentQueryTree

end PvsNP
