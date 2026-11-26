module

public import PvsNP.TuringMachine.Registers.Fragments
public import PvsNP.TuringMachine.Registers.Compare

/-! # Linking conditional register fragments -/

@[expose] public section

namespace PvsNP.RegisterMachine.Fragment

variable {R K : Type}

/-- The comparison instructions and both disjoint branch label sets. -/
abbrev IfEqualLabel (equal different : Fragment R) :=
  Fin 15 ⊕ (equal.Label ⊕ different.Label)

/-- Embed the equal branch, retaining its exit as the shared exit. -/
def ifEqualThenLabel (equal different : Fragment R) :
    Option equal.Label → Option (IfEqualLabel equal different) :=
  Option.map fun label ↦ .inr (.inl label)

/-- Embed the different branch, retaining its exit as the shared exit. -/
def ifEqualElseLabel (equal different : Fragment R) :
    Option different.Label → Option (IfEqualLabel equal different) :=
  Option.map fun label ↦ .inr (.inr label)

/-- Label one of the finite comparison instructions. -/
abbrev ifEqualTestLabel {equal different : Fragment R} (i : Fin 15) :
    Option (IfEqualLabel equal different) :=
  some (.inl i)

/-- Copy both operands and compare their copies. -/
def ifEqualTestCode (left right leftCopy rightCopy scratch : R)
    {equal different : Fragment R} (onEqual onDifferent : Option (IfEqualLabel equal different)) :
    Nat → Instruction R (Option (IfEqualLabel equal different))
  | 0 => .dec left (ifEqualTestLabel 3) (ifEqualTestLabel 1)
  | 1 => .inc leftCopy (ifEqualTestLabel 2)
  | 2 => .inc scratch (ifEqualTestLabel 0)
  | 3 => .dec scratch (ifEqualTestLabel 5) (ifEqualTestLabel 4)
  | 4 => .inc left (ifEqualTestLabel 3)
  | 5 => .dec right (ifEqualTestLabel 8) (ifEqualTestLabel 6)
  | 6 => .inc rightCopy (ifEqualTestLabel 7)
  | 7 => .inc scratch (ifEqualTestLabel 5)
  | 8 => .dec scratch (ifEqualTestLabel 10) (ifEqualTestLabel 9)
  | 9 => .inc right (ifEqualTestLabel 8)
  | 10 => .dec leftCopy (ifEqualTestLabel 11) (ifEqualTestLabel 12)
  | 11 => .dec rightCopy onEqual (ifEqualTestLabel 14)
  | 12 => .dec rightCopy (ifEqualTestLabel 13) (ifEqualTestLabel 10)
  | 13 => .dec leftCopy onDifferent (ifEqualTestLabel 13)
  | _ => .dec rightCopy onDifferent (ifEqualTestLabel 14)

/-- Compare the two register values, restore the scratch registers, and run
the selected fragment. An empty branch jumps directly to the exit. -/
abbrev ifEqual (left right leftCopy rightCopy scratch : R) (equal different : Fragment R) :
    Fragment R where
  Label := IfEqualLabel equal different
  entry := ifEqualTestLabel 0
  code
    | .inl i => ifEqualTestCode left right leftCopy rightCopy scratch
        (ifEqualThenLabel equal different equal.entry)
        (ifEqualElseLabel equal different different.entry) i.val
    | .inr (.inl label) => (equal.code label).map (ifEqualThenLabel equal different)
    | .inr (.inr label) => (different.code label).map (ifEqualElseLabel equal different)

/-- Instructions spent on comparison before entering either branch. -/
def ifEqualTime (leftValue rightValue : Nat) : Nat :=
  6 * (leftValue + rightValue) + 6

variable {left right leftCopy rightCopy scratch : R} {equal different : Fragment R}

local notation "test" => ifEqual left right leftCopy rightCopy scratch equal different

private def compareRules (left right leftCopy rightCopy scratch : R)
    (equal different : Fragment R) :
    CompareRules (ifEqual left right leftCopy rightCopy scratch equal different).close
      left right leftCopy rightCopy scratch where
  copyLeft := {
    entry := ifEqualTestLabel 0
    addTarget := ifEqualTestLabel 1
    addScratch := ifEqualTestLabel 2
    restore := ifEqualTestLabel 3
    addSource := ifEqualTestLabel 4
    next := ifEqualTestLabel 5
    takeSource := rfl
    writeTarget := rfl
    writeScratch := rfl
    takeScratch := rfl
    writeSource := rfl }
  copyRight := {
    entry := ifEqualTestLabel 5
    addTarget := ifEqualTestLabel 6
    addScratch := ifEqualTestLabel 7
    restore := ifEqualTestLabel 8
    addSource := ifEqualTestLabel 9
    next := ifEqualTestLabel 10
    takeSource := rfl
    writeTarget := rfl
    writeScratch := rfl
    takeScratch := rfl
    writeSource := rfl }
  compareCopies := {
    entry := ifEqualTestLabel 10
    inspectZero := ifEqualTestLabel 11
    inspectPositive := ifEqualTestLabel 12
    clearLeft := ifEqualTestLabel 13
    clearRight := ifEqualTestLabel 14
    branch := fun order ↦ if order = .eq then ifEqualThenLabel equal different equal.entry
      else ifEqualElseLabel equal different different.entry
    takeLeft := rfl
    takeRightAfterZero := rfl
    takeRightAfterPositive := rfl
    clearLeftRule := rfl
    clearRightRule := rfl }
  afterLeft := rfl
  afterRight := rfl

variable [DecidableEq R] (x : BinaryWord)
    (hLeftCopy : left ≠ leftCopy) (hLeftScratch : left ≠ scratch)
    (hRightLeft : right ≠ leftCopy) (hRightCopy : right ≠ rightCopy)
    (hRightScratch : right ≠ scratch)
    (hCopies : leftCopy ≠ rightCopy) (hLeftCopyScratch : leftCopy ≠ scratch)
    (hRightCopyScratch : rightCopy ≠ scratch)
    (cfg : Config R K)
    (hLeftZero : cfg.values leftCopy = 0) (hRightZero : cfg.values rightCopy = 0)
    (hScratchZero : cfg.values scratch = 0)

include hLeftCopy hLeftScratch hRightLeft hRightCopy hRightScratch hCopies
  hLeftCopyScratch hRightCopyScratch hLeftZero hRightZero hScratchZero in
/-- The comparison alone reaches the selected entry, preserving all data. -/
theorem run_ifEqual_test :
    (test).run x (ifEqualTime (cfg.values left) (cfg.values right)) ((test).enter cfg) =
      some ⟨some (if cfg.values left = cfg.values right then
        ifEqualThenLabel equal different equal.entry
        else ifEqualElseLabel equal different different.entry),
        cfg.values, cfg.cursor, cfg.output⟩ := by
  have hRun := run_compare (compareRules left right leftCopy rightCopy scratch equal different)
    x hLeftCopy hLeftScratch hRightLeft hRightCopy hRightScratch hCopies hLeftCopyScratch
    hRightCopyScratch (cfg := (test).enter cfg) rfl hLeftZero hRightZero hScratchZero
  simpa only [compareRules, enter, Nat.compare_eq_eq, ifEqualTime] using hRun

include hLeftCopy hLeftScratch hRightLeft hRightCopy hRightScratch hCopies
  hLeftCopyScratch hRightCopyScratch hLeftZero hRightZero hScratchZero in
/-- Equal values select the equal branch after the exact comparison count. -/
theorem run_ifEqual_eq {n : Nat} {next : equal.Cfg}
    (hEq : cfg.values left = cfg.values right)
    (hRun : equal.run x n (equal.enter cfg) = some next) (hExit : next.pc = some none) :
    (test).run x (ifEqualTime (cfg.values left) (cfg.values right) + n) ((test).enter cfg) =
      some ⟨some none, next.values, next.cursor, next.output⟩ := by
  have hTest := run_ifEqual_test (equal := equal) (different := different) x
    hLeftCopy hLeftScratch hRightLeft hRightCopy hRightScratch hCopies hLeftCopyScratch
    hRightCopyScratch cfg hLeftZero hRightZero hScratchZero
  have hBranch := run_link (ifEqualThenLabel equal different)
    (target := (test).close) (fun _ ↦ rfl) hRun hExit
  change RegisterMachine.run (test).close x _ ((test).enter cfg) = _ at hTest ⊢
  rw [ite_eq_left hEq] at hTest
  rw [RegisterMachine.run_add, hTest, Option.bind_some]
  simpa only [Config.map, enter, hExit, Option.map_some, ifEqualThenLabel, Option.map_none]
    using hBranch

include hLeftCopy hLeftScratch hRightLeft hRightCopy hRightScratch hCopies
  hLeftCopyScratch hRightCopyScratch hLeftZero hRightZero hScratchZero in
/-- Different values select the different branch after the exact comparison count. -/
theorem run_ifEqual_ne {n : Nat} {next : different.Cfg}
    (hNe : cfg.values left ≠ cfg.values right)
    (hRun : different.run x n (different.enter cfg) = some next) (hExit : next.pc = some none) :
    (test).run x (ifEqualTime (cfg.values left) (cfg.values right) + n) ((test).enter cfg) =
      some ⟨some none, next.values, next.cursor, next.output⟩ := by
  have hTest := run_ifEqual_test (equal := equal) (different := different) x
    hLeftCopy hLeftScratch hRightLeft hRightCopy hRightScratch hCopies hLeftCopyScratch
    hRightCopyScratch cfg hLeftZero hRightZero hScratchZero
  have hBranch := run_link (ifEqualElseLabel equal different)
    (target := (test).close) (fun _ ↦ rfl) hRun hExit
  change RegisterMachine.run (test).close x _ ((test).enter cfg) = _ at hTest ⊢
  rw [ite_eq_right hNe] at hTest
  rw [RegisterMachine.run_add, hTest, Option.bind_some]
  simpa only [Config.map, enter, hExit, Option.map_some, ifEqualElseLabel, Option.map_none]
    using hBranch

end PvsNP.RegisterMachine.Fragment
