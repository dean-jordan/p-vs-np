module

public import PvsNP.TuringMachine.Registers.Conditional
public import PvsNP.TuringMachine.Registers.OutputRuns

/-! # Branches selected by register comparison -/

@[expose] public section

namespace PvsNP.RegisterMachine.Fragment

variable {R K : Type}

/-- Link each comparison result to the chosen branch entry. -/
def orderingBranch (matching otherwise : Fragment R) (select : Ordering → Bool)
    (order : Ordering) : Option (IfEqualLabel matching otherwise) :=
  if select order then ifEqualThenLabel matching otherwise matching.entry
  else ifEqualElseLabel matching otherwise otherwise.entry

/-- Reuse the finite comparison code with independently selected exits for `<`, `=`, and `>`. -/
def orderingTestCode (left right leftCopy rightCopy scratch : R)
    {matching otherwise : Fragment R}
    (branch : Ordering → Option (IfEqualLabel matching otherwise)) :
    Nat → Instruction R (Option (IfEqualLabel matching otherwise))
  | 11 => .dec rightCopy (branch .eq) (ifEqualTestLabel 14)
  | 13 => .dec leftCopy (branch .gt) (ifEqualTestLabel 13)
  | 14 => .dec rightCopy (branch .lt) (ifEqualTestLabel 14)
  | n => ifEqualTestCode left right leftCopy rightCopy scratch (branch .eq) (branch .lt) n

/-- Compare two preserved registers and run the branch selected on the ordering. -/
abbrev ifOrdering (left right leftCopy rightCopy scratch : R) (select : Ordering → Bool)
    (matching otherwise : Fragment R) : Fragment R where
  Label := IfEqualLabel matching otherwise
  entry := ifEqualTestLabel 0
  code
    | .inl i => orderingTestCode left right leftCopy rightCopy scratch
      (orderingBranch matching otherwise select) i.val
    | .inr (.inl label) => (matching.code label).map (ifEqualThenLabel matching otherwise)
    | .inr (.inr label) => (otherwise.code label).map (ifEqualElseLabel matching otherwise)

/-- Run the first fragment exactly when the left register is smaller. -/
abbrev ifLess (left right leftCopy rightCopy scratch : R) (less otherwise : Fragment R) :
    Fragment R := ifOrdering left right leftCopy rightCopy scratch (· == .lt) less otherwise

private def orderingCompareRules (left right leftCopy rightCopy scratch : R)
    (select : Ordering → Bool) (matching otherwise : Fragment R) :
    CompareRules (ifOrdering left right leftCopy rightCopy scratch select matching otherwise).close
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
    branch := orderingBranch matching otherwise select
    takeLeft := rfl
    takeRightAfterZero := rfl
    takeRightAfterPositive := rfl
    clearLeftRule := rfl
    clearRightRule := rfl }
  afterLeft := rfl
  afterRight := rfl

variable [DecidableEq R] {left right leftCopy rightCopy scratch : R}
  {matching otherwise : Fragment R}

private theorem run_ifOrdering_test (select : Ordering → Bool) (x : BinaryWord) (cfg : Config R K)
    (hLeft : [left, leftCopy, rightCopy, scratch].Nodup)
    (hRight : [right, leftCopy, rightCopy, scratch].Nodup)
    (hLeftZero : cfg.values leftCopy = 0) (hRightZero : cfg.values rightCopy = 0)
    (hScratch : cfg.values scratch = 0) :
    let test := ifOrdering left right leftCopy rightCopy scratch select matching otherwise
    test.run x (ifEqualTime (cfg.values left) (cfg.values right)) (test.enter cfg) = some
      ⟨some (if select (compare (cfg.values left) (cfg.values right)) then
        ifEqualThenLabel matching otherwise matching.entry
        else ifEqualElseLabel matching otherwise otherwise.entry),
        cfg.values, cfg.cursor, cfg.output⟩ := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or,
    not_false_eq_true, List.nodup_nil, and_true] at hLeft hRight
  obtain ⟨⟨hLeftCopy, _, hLeftScratch⟩, ⟨hCopies, hLeftCopyScratch⟩, hRightCopyScratch⟩ := hLeft
  obtain ⟨⟨hRightLeft, hRightCopy, hRightScratch⟩, _, _⟩ := hRight
  let test := ifOrdering left right leftCopy rightCopy scratch select matching otherwise
  have hRun := run_compare (orderingCompareRules left right leftCopy rightCopy scratch select
    matching otherwise) x hLeftCopy hLeftScratch hRightLeft hRightCopy hRightScratch hCopies
    hLeftCopyScratch hRightCopyScratch (cfg := test.enter cfg) rfl hLeftZero hRightZero hScratch
  exact hRun

/-- A bounded output-producing branch adds only the exact comparison cost. -/
theorem runsOutput_ifOrdering (select : Ordering → Bool) (x : BinaryWord) (before after : R → Nat)
    (suffix output : BinaryWord) (bound : Nat)
    (hLeft : [left, leftCopy, rightCopy, scratch].Nodup)
    (hRight : [right, leftCopy, rightCopy, scratch].Nodup)
    (hLeftZero : before leftCopy = 0) (hRightZero : before rightCopy = 0)
    (hScratch : before scratch = 0)
    (hMatch : select (compare (before left) (before right)) = true →
      ∃ cost ≤ bound, matching.RunsOutput x cost before after suffix output)
    (hOther : select (compare (before left) (before right)) ≠ true →
      ∃ cost ≤ bound, otherwise.RunsOutput x cost before after suffix output) :
    ∃ cost ≤ ifEqualTime (before left) (before right) + bound,
      (ifOrdering left right leftCopy rightCopy scratch select matching otherwise).RunsOutput
        x cost before after suffix output := by
  let cfg : Config R Unit := ⟨none, before, none, suffix⟩
  let test := ifOrdering left right leftCopy rightCopy scratch select matching otherwise
  have hTest := run_ifOrdering_test (matching := matching) (otherwise := otherwise) select
    x cfg hLeft hRight hLeftZero hRightZero hScratch
  change RegisterMachine.run test.close x (ifEqualTime (before left) (before right))
    (test.enter cfg) = _ at hTest
  by_cases h : select (compare (before left) (before right)) = true
  · obtain ⟨cost, hCost, hRun⟩ := hMatch h
    change matching.run x cost (matching.enter cfg) = some ⟨some none, after, none, output⟩ at hRun
    have hBranch := run_link (ifEqualThenLabel matching otherwise) (target := test.close)
      (fun _ ↦ rfl) hRun rfl
    refine ⟨_, Nat.add_le_add_left hCost _, ?_⟩
    change RegisterMachine.run test.close x _ (test.enter cfg) = _
    simp only [cfg, ite_eq_left h] at hTest
    rw [RegisterMachine.run_add, hTest, Option.bind_some]
    exact hBranch
  · obtain ⟨cost, hCost, hRun⟩ := hOther h
    change otherwise.run x cost (otherwise.enter cfg) =
      some ⟨some none, after, none, output⟩ at hRun
    have hBranch := run_link (ifEqualElseLabel matching otherwise) (target := test.close)
      (fun _ ↦ rfl) hRun rfl
    refine ⟨_, Nat.add_le_add_left hCost _, ?_⟩
    change RegisterMachine.run test.close x _ (test.enter cfg) = _
    simp only [cfg, ite_eq_right h] at hTest
    rw [RegisterMachine.run_add, hTest, Option.bind_some]
    exact hBranch

/-- The ordered branch test with its natural-number `<` condition. -/
theorem runsOutput_ifLess (x : BinaryWord) (before after : R → Nat)
    (suffix output : BinaryWord) (bound : Nat)
    (hLeft : [left, leftCopy, rightCopy, scratch].Nodup)
    (hRight : [right, leftCopy, rightCopy, scratch].Nodup)
    (hLeftZero : before leftCopy = 0) (hRightZero : before rightCopy = 0)
    (hScratch : before scratch = 0)
    (hLess : before left < before right →
      ∃ cost ≤ bound, matching.RunsOutput x cost before after suffix output)
    (hNotLess : ¬ before left < before right →
      ∃ cost ≤ bound, otherwise.RunsOutput x cost before after suffix output) :
    ∃ cost ≤ ifEqualTime (before left) (before right) + bound,
      (ifLess left right leftCopy rightCopy scratch matching otherwise).RunsOutput
        x cost before after suffix output := by
  apply runsOutput_ifOrdering (· == .lt) x before after suffix output bound
    hLeft hRight hLeftZero hRightZero hScratch
  · intro h
    exact hLess (by simpa only [beq_iff_eq, Nat.compare_eq_lt] using h)
  · intro h
    exact hNotLess (fun hLt ↦ h (beq_iff_eq.mpr (Nat.compare_eq_lt.mpr hLt)))

variable {R : Type} [DecidableEq R] in
theorem runsValues_ifLess (lanes : Fin 5 → R) (hLanes : Function.Injective lanes)
    (less otherwise : Fragment R) (x : BinaryWord) (before : R → Nat)
    (hLeft : before (lanes 2) = 0) (hRight : before (lanes 3) = 0)
    (hScratch : before (lanes 4) = 0) {ticks : Nat} {after : R → Nat}
    (hRun : (if before (lanes 0) < before (lanes 1) then less else otherwise).RunsValues
      x ticks before after) :
    (ifLess (lanes 0) (lanes 1) (lanes 2) (lanes 3) (lanes 4) less otherwise).RunsValues
      x (ifEqualTime (before (lanes 0)) (before (lanes 1)) + ticks) before after := by
  intro output
  let test := ifLess (lanes 0) (lanes 1) (lanes 2) (lanes 3) (lanes 4) less otherwise
  let start : test.Cfg := test.enter (⟨none, before, none, output⟩ : Config R Unit)
  have hLeftNames : [lanes 0, lanes 2, lanes 3, lanes 4].Nodup :=
    List.Nodup.map hLanes (show ([0, 2, 3, 4] : List (Fin 5)).Nodup by decide)
  have hRightNames : [lanes 1, lanes 2, lanes 3, lanes 4].Nodup :=
    List.Nodup.map hLanes (show ([1, 2, 3, 4] : List (Fin 5)).Nodup by decide)
  have hTest := run_ifOrdering_test (matching := less) (otherwise := otherwise)
    (· == .lt) x (⟨none, before, none, output⟩ : Config R Unit)
    hLeftNames hRightNames hLeft hRight hScratch
  change RegisterMachine.run test.close x _ start = _
  have hTest' : RegisterMachine.run test.close x
      (ifEqualTime (before (lanes 0)) (before (lanes 1))) start = some
      ⟨some (if before (lanes 0) < before (lanes 1) then ifEqualThenLabel less otherwise less.entry
        else ifEqualElseLabel less otherwise otherwise.entry), before, none, output⟩ := by
    simpa only [start, test, ifLess, beq_iff_eq, Nat.compare_eq_lt] using hTest
  rw [RegisterMachine.run_add, hTest', Option.bind_some]
  by_cases hLt : before (lanes 0) < before (lanes 1)
  · simp only [ite_eq_left hLt] at hRun ⊢
    exact run_link (ifEqualThenLabel less otherwise) (target := test.close)
      (fun _ ↦ rfl) (hRun output) rfl
  · simp only [ite_eq_right hLt] at hRun ⊢
    exact run_link (ifEqualElseLabel less otherwise) (target := test.close)
      (fun _ ↦ rfl) (hRun output) rfl

end PvsNP.RegisterMachine.Fragment
