module

public import PvsNP.TuringMachine.Registers.Clear
public import PvsNP.TuringMachine.Registers.Copy

/-! # Counted register comparison

The destructive comparison decrements both lanes until one is zero and
clears any residue. Comparing two copies preserves the original lanes.
-/

@[expose] public section

namespace PvsNP.RegisterMachine

variable {R L : Type} [DecidableEq R]

/-- Program rules for comparing and clearing two registers. -/
structure DestructiveCompareRules (program : L → Instruction R L) (left right : R) where
  entry : L
  inspectZero : L
  inspectPositive : L
  clearLeft : L
  clearRight : L
  branch : Ordering → L
  takeLeft : program entry = .dec left inspectZero inspectPositive
  takeRightAfterZero : program inspectZero = .dec right (branch .eq) clearRight
  takeRightAfterPositive : program inspectPositive = .dec right clearLeft entry
  clearLeftRule : program clearLeft = .dec left (branch .gt) clearLeft
  clearRightRule : program clearRight = .dec right (branch .lt) clearRight

/-- Clear both comparison registers. -/
def clearCompareValues (left right : R) (values : R → Nat) : R → Nat :=
  fun r ↦ if r = left ∨ r = right then 0 else values r

private theorem run_after_two {program : L → Instruction R L} {x : BinaryWord}
    {cfg first second finished : Config R L} {n : Nat}
    (hFirst : step program x cfg = some first) (hSecond : step program x first = some second)
    (hRest : run program x n second = some finished) :
    run program x (2 + n) cfg = some finished := by
  rw [run_add]
  simp only [run, hFirst, hSecond, Option.bind_some]
  exact hRest

/-- Comparing two distinct lanes takes their sum plus two instructions and clears both. -/
theorem run_compare_destructive {program : L → Instruction R L} {left right : R}
    (rules : DestructiveCompareRules program left right) (x : BinaryWord) (hLR : left ≠ right)
    {cfg : Config R L} (hPC : cfg.pc = some rules.entry) :
    run program x (cfg.values left + cfg.values right + 2) cfg = some
      { cfg with
        pc := some (rules.branch (compare (cfg.values left) (cfg.values right)))
        values := clearCompareValues left right cfg.values } := by
  generalize hLeft : cfg.values left = count
  induction count generalizing cfg with
  | zero =>
    let first := { cfg with pc := some rules.inspectZero }
    have hFirst : step program x cfg = some first := step_dec_zero hPC rules.takeLeft hLeft
    by_cases hRight : cfg.values right = 0
    · let second := { cfg with pc := some (rules.branch .eq) }
      have hSecond : step program x first = some second :=
        step_dec_zero rfl rules.takeRightAfterZero hRight
      have hCompare : compare 0 (cfg.values right) = .eq := Nat.compare_eq_eq.mpr hRight.symm
      have hValues : clearCompareValues left right cfg.values = cfg.values := by
        funext r
        by_cases hl : r = left <;> by_cases hr : r = right <;>
          simp [clearCompareValues, hl, hr, hLeft, hRight]
      rw [hCompare, hRight, hValues]
      exact run_after_two hFirst hSecond (run_zero program x second)
    · have hPos : 0 < cfg.values right := Nat.pos_of_ne_zero hRight
      let second := { cfg with
        pc := some rules.clearRight
        values := decrementValues right cfg.values }
      have hSecond : step program x first = some second :=
        step_dec_pos rfl rules.takeRightAfterZero hPos
      have hClear := run_clear x rules.clearRightRule (cfg := second) rfl
      have hCompare : compare 0 (cfg.values right) = .lt := Nat.compare_eq_lt.mpr hPos
      have hValues : clearValues right second.values =
          clearCompareValues left right cfg.values := by
        funext r
        by_cases hl : r = left <;> by_cases hr : r = right <;>
          simp [clearValues, clearCompareValues, second, decrementValues, hl, hr, hLeft]
      have hTime : 0 + cfg.values right + 2 = 2 + (second.values right + 1) := by
        have hSecondValue : second.values right = cfg.values right - 1 := by
          simp [second, decrementValues]
        omega
      rw [hTime, hCompare, ← hValues]
      exact run_after_two hFirst hSecond hClear
  | succ count ih =>
    have hPos : 0 < cfg.values left := hLeft ▸ Nat.succ_pos count
    let first := { cfg with
      pc := some rules.inspectPositive
      values := decrementValues left cfg.values }
    have hFirst : step program x cfg = some first := step_dec_pos hPC rules.takeLeft hPos
    have hFirstRight : first.values right = cfg.values right := by
      simp [first, decrementValues, hLR.symm]
    by_cases hRight : cfg.values right = 0
    · let second := { first with pc := some rules.clearLeft }
      have hSecond : step program x first = some second :=
        step_dec_zero rfl rules.takeRightAfterPositive (hFirstRight.trans hRight)
      have hClear := run_clear x rules.clearLeftRule (cfg := second) rfl
      have hCompare : compare (count + 1) (cfg.values right) = .gt := by
        apply Nat.compare_eq_gt.mpr
        omega
      have hValues : clearValues left second.values =
          clearCompareValues left right cfg.values := by
        funext r
        by_cases hl : r = left <;> by_cases hr : r = right <;>
          simp [clearValues, clearCompareValues, first, second, decrementValues, hl, hr, hRight]
      have hTime : count + 1 + cfg.values right + 2 = 2 + (second.values left + 1) := by
        have hSecondValue : second.values left = count := by
          simp [second, first, decrementValues, hLeft]
        omega
      rw [hTime, hCompare, ← hValues]
      exact run_after_two hFirst hSecond hClear
    · have hRightPos : 0 < cfg.values right := Nat.pos_of_ne_zero hRight
      let second := { first with
        pc := some rules.entry
        values := decrementValues right first.values }
      have hSecond : step program x first = some second := by
        apply step_dec_pos rfl rules.takeRightAfterPositive
        rwa [hFirstRight]
      have hSecondLeft : second.values left = count := by
        simp [second, first, decrementValues, hLR, hLeft]
      have hSecondRight : second.values right = cfg.values right - 1 := by
        simp [second, decrementValues, hFirstRight]
      have hRest := ih (cfg := second) rfl hSecondLeft
      rw [hSecondRight] at hRest
      have hCompare : compare count (cfg.values right - 1) =
          compare (count + 1) (cfg.values right) := by
        have hlt : (count < cfg.values right - 1) ↔ count + 1 < cfg.values right := by omega
        have hgt : (cfg.values right - 1 < count) ↔ cfg.values right < count + 1 := by omega
        simp only [Nat.compare_eq_ite_lt, hlt, hgt]
      have hValues : clearCompareValues left right second.values =
          clearCompareValues left right cfg.values := by
        funext r
        by_cases hl : r = left <;> by_cases hr : r = right <;>
          simp [clearCompareValues, second, first, decrementValues, hl, hr]
      have hTime : count + 1 + cfg.values right + 2 =
          2 + (count + (cfg.values right - 1) + 2) := by omega
      rw [hCompare, hValues] at hRest
      rw [hTime]
      exact run_after_two hFirst hSecond hRest

/-- Compose two copies and a destructive comparison on the copied lanes. -/
structure CompareRules (program : L → Instruction R L)
    (left right leftCopy rightCopy scratch : R) where
  copyLeft : CopyRules program left leftCopy scratch
  copyRight : CopyRules program right rightCopy scratch
  compareCopies : DestructiveCompareRules program leftCopy rightCopy
  afterLeft : copyLeft.next = copyRight.entry
  afterRight : copyRight.next = compareCopies.entry

/-- Compare two register values using three initially zero scratch registers. All register
values, the input cursor, and the output are restored at the selected successor label. -/
theorem run_compare {program : L → Instruction R L} {left right leftCopy rightCopy scratch : R}
    (rules : CompareRules program left right leftCopy rightCopy scratch) (x : BinaryWord)
    (hLeftCopy : left ≠ leftCopy) (hLeftScratch : left ≠ scratch)
    (hRightLeft : right ≠ leftCopy) (hRightCopy : right ≠ rightCopy)
    (hRightScratch : right ≠ scratch)
    (hCopies : leftCopy ≠ rightCopy) (hLeftCopyScratch : leftCopy ≠ scratch)
    (hRightCopyScratch : rightCopy ≠ scratch)
    {cfg : Config R L} (hPC : cfg.pc = some rules.copyLeft.entry)
    (hLeftZero : cfg.values leftCopy = 0) (hRightZero : cfg.values rightCopy = 0)
    (hScratchZero : cfg.values scratch = 0) :
    run program x (6 * (cfg.values left + cfg.values right) + 6) cfg = some
      { cfg with pc := some (rules.compareCopies.branch
        (compare (cfg.values left) (cfg.values right))) } := by
  let first := { cfg with
    pc := some rules.copyRight.entry
    values := copyValues left leftCopy cfg.values }
  have hFirst : run program x (5 * cfg.values left + 2) cfg = some first := by
    simpa only [rules.afterLeft] using
      run_copy rules.copyLeft x hLeftCopy hLeftScratch hLeftCopyScratch hPC hLeftZero hScratchZero
  have hFirstRight : first.values right = cfg.values right := by
    simp [first, copyValues, hRightLeft]
  have hFirstRightCopy : first.values rightCopy = 0 := by
    simp [first, copyValues, hCopies.symm, hRightZero]
  have hFirstScratch : first.values scratch = 0 := by
    simp [first, copyValues, hLeftCopyScratch.symm, hScratchZero]
  let second := { first with
    pc := some rules.compareCopies.entry
    values := copyValues right rightCopy first.values }
  have hSecond : run program x (5 * cfg.values right + 2) first = some second := by
    simpa only [rules.afterRight, hFirstRight] using
      run_copy rules.copyRight x hRightCopy hRightScratch hRightCopyScratch
        (cfg := first) rfl hFirstRightCopy hFirstScratch
  have hSecondLeft : second.values leftCopy = cfg.values left := by
    simp [second, first, copyValues, hCopies]
  have hSecondRight : second.values rightCopy = cfg.values right := by
    simp [second, copyValues, hFirstRight]
  have hFinish := run_compare_destructive rules.compareCopies x hCopies (cfg := second) rfl
  have hValues : clearCompareValues leftCopy rightCopy second.values = cfg.values := by
    funext r
    by_cases hl : r = leftCopy <;> by_cases hr : r = rightCopy <;>
      simp [clearCompareValues, second, first, copyValues, hl, hr, hLeftZero, hRightZero]
  have hTime : 6 * (cfg.values left + cfg.values right) + 6 =
      (5 * cfg.values left + 2) + (5 * cfg.values right + 2) +
        (cfg.values left + cfg.values right + 2) := by omega
  rw [hSecondLeft, hSecondRight, hValues] at hFinish
  rw [hTime, run_add, run_add, hFirst, Option.bind_some, hSecond, Option.bind_some, hFinish]

end PvsNP.RegisterMachine
