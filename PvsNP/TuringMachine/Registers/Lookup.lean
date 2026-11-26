module

public import PvsNP.TuringMachine.Registers.InputAt
public import PvsNP.TuringMachine.Registers.ValueRuns

import Mathlib.Basic.Finite.Prod

/-! # Linking a reverse input lookup to its branches

The lookup consumes the index and clears the cursor before entering one of
three branch bodies. An empty branch goes directly to the shared exit.
-/

@[expose] public section

namespace PvsNP.RegisterMachine.Fragment

variable {R K : Type}

/-- Local control for the lookup, carrying the bit at the two labels that need it. -/
inductive LookupPhase where
  | entry | inspect (b : Bool) | advance | reset (b : Bool) | pastEnd

private def lookupPhaseCode : LookupPhase → Fin 5 × Bool
  | .entry => (0, false)
  | .inspect b => (1, b)
  | .advance => (2, false)
  | .reset b => (3, b)
  | .pastEnd => (4, false)

instance : Finite LookupPhase :=
  Finite.of_injective lookupPhaseCode (by
    intro a b h
    cases a <;> cases b <;> simp_all [lookupPhaseCode])

/-- Separate the lookup labels from the three branch label spaces. -/
abbrev LookupLabel (branches : Option Bool → Fragment R) :=
  LookupPhase ⊕ ((branches none).Label ⊕
    ((branches (some false)).Label ⊕ (branches (some true)).Label))

instance (branches : Option Bool → Fragment R) : Finite (LookupLabel branches) := by
  unfold LookupLabel
  let _ : Finite ((branches (some false)).Label ⊕ (branches (some true)).Label) :=
    inferInstance
  let _ : Finite ((branches none).Label ⊕
      ((branches (some false)).Label ⊕ (branches (some true)).Label)) := inferInstance
  infer_instance

/-- Embed a branch label in the shared program. -/
def lookupBranchLabel (branches : Option Bool → Fragment R) :
    (result : Option Bool) → (branches result).Label → LookupLabel branches
  | none, label => .inr (.inl label)
  | some false, label => .inr (.inr (.inl label))
  | some true, label => .inr (.inr (.inr label))

/-- A branch's live exit maps to the shared exit. -/
abbrev lookupBranchMap (branches : Option Bool → Fragment R) (result : Option Bool) :
    Option (branches result).Label → Option (LookupLabel branches) :=
  Option.map (lookupBranchLabel branches result)

/-- Read `x.reverse[index]?` and enter the corresponding branch. -/
abbrev lookup (index : R) (branches : Option Bool → Fragment R) : Fragment R where
  Label := LookupLabel branches
  entry := some (.inl .entry)
  code
    | .inl .entry => .readFirst
        (inputAtBranch (fun b ↦ some (.inl (.inspect b))) (some (.inl .pastEnd)))
    | .inl (.inspect b) => .dec index (some (.inl (.reset b))) (some (.inl .advance))
    | .inl .advance => .readNext
        (inputAtBranch (fun b ↦ some (.inl (.inspect b))) (some (.inl .pastEnd)))
    | .inl (.reset b) => .resetInput (lookupBranchMap branches (some b) (branches (some b)).entry)
    | .inl .pastEnd => .dec index (lookupBranchMap branches none (branches none).entry)
        (some (.inl .pastEnd))
    | .inr (.inl label) => ((branches none).code label).map (lookupBranchMap branches none)
    | .inr (.inr (.inl label)) =>
      ((branches (some false)).code label).map (lookupBranchMap branches (some false))
    | .inr (.inr (.inr label)) =>
      ((branches (some true)).code label).map (lookupBranchMap branches (some true))

private def lookupRules (index : R) (branches : Option Bool → Fragment R) :
    InputAtRules (lookup index branches).close index where
  entry := some (.inl .entry)
  inspect b := some (.inl (.inspect b))
  advance := some (.inl .advance)
  reset b := some (.inl (.reset b))
  pastEnd := some (.inl .pastEnd)
  next result := lookupBranchMap branches result (branches result).entry
  read_first := rfl
  inspect_index _ := rfl
  read_next := rfl
  reset_mark _ := rfl
  clear_pastEnd := rfl

variable [DecidableEq R]

/-- The data supplied to the selected branch after clearing the index and cursor. -/
def lookupBranchInput (index : R) (cfg : Config R K) : Config R Unit :=
  ⟨none, clearInputAtIndex index cfg.values, none, cfg.output⟩

/-- The lookup reaches the branch entry in the exact lookup cost, preserving
the output and all registers except the consumed index. -/
theorem run_lookup_start (index : R) (branches : Option Bool → Fragment R)
    (x : BinaryWord) (cfg : Config R K) (hCursor : cfg.cursor = none) :
    let result := x.reverse[cfg.values index]?
    (lookup index branches).run x (inputAtCost (cfg.values index) x.length)
        ((lookup index branches).enter cfg) =
      some (((branches result).enter (lookupBranchInput index cfg)).map
        (lookupBranchMap branches result)) :=
  run_inputAt (lookupRules index branches) x (cfg := (lookup index branches).enter cfg)
    rfl hCursor

omit [DecidableEq R] in
private theorem lookupCode_branch (index : R) (branches : Option Bool → Fragment R)
    (result : Option Bool) (label : (branches result).Label) :
    (lookup index branches).close (lookupBranchMap branches result (some label)) =
      ((branches result).code label).map (lookupBranchMap branches result) := by
  cases result with
  | none => rfl
  | some b => cases b <;> rfl

/-- Link the lookup and the successful selected branch without a boundary instruction. -/
theorem run_lookup (index : R) (branches : Option Bool → Fragment R) (x : BinaryWord)
    (cfg : Config R K) (hCursor : cfg.cursor = none) {n : Nat}
    {next : (branches (x.reverse[cfg.values index]?)).Cfg}
    (hRun : (branches (x.reverse[cfg.values index]?)).run x n
      ((branches (x.reverse[cfg.values index]?)).enter (lookupBranchInput index cfg)) = some next)
    (hExit : next.pc = some none) :
    (lookup index branches).run x (inputAtCost (cfg.values index) x.length + n)
        ((lookup index branches).enter cfg) =
      some (next.map (lookupBranchMap branches (x.reverse[cfg.values index]?))) := by
  let result := x.reverse[cfg.values index]?
  have start := run_lookup_start index branches x cfg hCursor
  have branch := run_link (lookupBranchMap branches result)
    (target := (lookup index branches).close) (lookupCode_branch index branches result) hRun hExit
  change RegisterMachine.run (lookup index branches).close x _ _ = _ at start
  change RegisterMachine.run (lookup index branches).close x _ _ = _
  rw [RegisterMachine.run_add, start, Option.bind_some]
  exact branch

/-- Compose a lookup with an exact run of the selected branch on the cleared valuation. -/
theorem runsValues_lookup (index : R) (branches : Option Bool → Fragment R) (x : BinaryWord)
    (before : R → Nat) {n : Nat} {after : R → Nat}
    (hRun : (branches (x.reverse[before index]?)).RunsValues x n
      (clearInputAtIndex index before) after) :
    (lookup index branches).RunsValues x (inputAtCost (before index) x.length + n)
      before after := by
  intro output
  let cfg : Config R Unit := ⟨none, before, none, output⟩
  exact run_lookup index branches x cfg rfl (hRun output) rfl

end PvsNP.RegisterMachine.Fragment
