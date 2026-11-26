module

public import PvsNP.TuringMachine.Registers.StridedField

/-! # Compare little-endian fields at different strides

The two reverse input positions move by independent positive strides. The
comparison scans from least to most significant, keeping only the most
recent unequal bit pair. Its cost depends on field width and input offsets.
-/

public section

namespace PvsNP.RegisterMachine.Fragment

open Circuits (fieldValue)

variable {R : Type}

private def decrementBy (lane : R) : Nat → Fragment R
  | 0 => skip
  | amount + 1 => (decrementLane lane).seq (decrementBy lane amount)

private def stridedCompareIteration (leftStride rightStride : Nat) (lanes : Fin 6 → R) :
    Fragment R :=
  (compareIteration lanes).seq
    ((decrementBy (lanes 0) (leftStride - 1)).seq (decrementBy (lanes 1) (rightStride - 1)))

/-- Lanes 0 and 1 hold reverse positions, lane 2 holds the remaining width,
lanes 3 and 4 are scratch, and lane 5 records 0 for equality, 1 for less than,
or 2 for greater than. -/
def stridedCompare (leftStride rightStride : Nat) (lanes : Fin 6 → R) : Fragment R :=
  countdown (lanes 2) (stridedCompareIteration leftStride rightStride lanes)

/-- Instruction bound for comparing two in-range fields at positive strides. -/
@[expose] def stridedCompareTime (leftStride rightStride inputLength width : Nat) : Nat :=
  width * (14 * inputLength + 16 + leftStride + rightStride) + 1

theorem stridedCompareTime_polynomiallyBounded (leftStride rightStride : Nat)
    {inputLength width : Nat → Nat} (hInput : PolynomiallyBounded inputLength)
    (hWidth : PolynomiallyBounded width) :
    PolynomiallyBounded (fun n ↦ stridedCompareTime leftStride rightStride
      (inputLength n) (width n)) :=
  (hWidth.mul (((((PolynomiallyBounded.const 14).mul hInput).add
    (PolynomiallyBounded.const 16)).add (PolynomiallyBounded.const leftStride)).add
    (PolynomiallyBounded.const rightStride))).add (PolynomiallyBounded.const 1)

variable [DecidableEq R]

private theorem runsValues_decrementBy (lane : R) (amount : Nat) (x : BinaryWord)
    (before : R → Nat) :
    (decrementBy lane amount).RunsValues x amount before
      (setValue lane (before lane - amount) before) := by
  induction amount generalizing before with
  | zero =>
    have hValues : setValue lane (before lane - 0) before = before := by
      funext r
      by_cases h : r = lane <;> simp [setValue, h]
    simpa only [decrementBy, hValues] using runsValues_skip x before
  | succ amount ih =>
    have hValues : setValue lane (decrementValues lane before lane - amount)
        (decrementValues lane before) = setValue lane (before lane - (amount + 1)) before := by
      funext r
      by_cases h : r = lane
      · simp [setValue, decrementValues, h]
        omega
      · simp [setValue, decrementValues, h]
    simpa only [decrementBy, hValues, Nat.add_comm] using
      (runsValues_decrementLane lane x before).seq (ih (decrementValues lane before))

private def stridedCompareIterationValues (leftStride rightStride : Nat) (lanes : Fin 6 → R)
    (a b : Bool) (before : R → Nat) : R → Nat :=
  let compared := compareIterationValues lanes a b before
  let movedLeft := setValue (lanes 0) (compared (lanes 0) - (leftStride - 1)) compared
  setValue (lanes 1) (movedLeft (lanes 1) - (rightStride - 1)) movedLeft

private theorem runsValues_stridedCompareIteration (leftStride rightStride : Nat)
    (lanes : Fin 6 → R) (hLanes : Function.Injective lanes) (x : BinaryWord)
    (before : R → Nat) (a b : Bool) (hLeftStride : 0 < leftStride)
    (hRightStride : 0 < rightStride) (hLeft : x.reverse[before (lanes 0)]? = some a)
    (hRight : x.reverse[before (lanes 1)]? = some b)
    (hIndex : before (lanes 3) = 0) (hWork : before (lanes 4) = 0)
    (hOld : before (lanes 5) ≤ 2) :
    ∃ ticks ≤ 14 * x.length + 15 + leftStride + rightStride,
      (stridedCompareIteration leftStride rightStride lanes).RunsValues x ticks before
        (stridedCompareIterationValues leftStride rightStride lanes a b before) := by
  obtain ⟨ticks, hTicks, hRun⟩ := runsValues_compareIteration lanes hLanes x before a b
    hLeft hRight hIndex hWork hOld
  let compared := compareIterationValues lanes a b before
  let movedLeft := setValue (lanes 0) (compared (lanes 0) - (leftStride - 1)) compared
  have hMoves := (runsValues_decrementBy (lanes 0) (leftStride - 1) x compared).seq
    (runsValues_decrementBy (lanes 1) (rightStride - 1) x movedLeft)
  exact ⟨ticks + ((leftStride - 1) + (rightStride - 1)), by omega, hRun.seq hMoves⟩

private theorem runsValues_stridedCompare_words (leftStride rightStride : Nat)
    (lanes : Fin 6 → R) (hLanes : Function.Injective lanes) (x left right : BinaryWord)
    (before : R → Nat) (hLeftStride : 0 < leftStride) (hRightStride : 0 < rightStride)
    (hWidth : left.length = right.length) (hCount : before (lanes 2) = left.length)
    (hIndex : before (lanes 3) = 0) (hWork : before (lanes 4) = 0)
    (hOrder : before (lanes 5) ≤ 2)
    (hLeft : ∀ i, i < left.length → x.reverse[before (lanes 0) - leftStride * i]? = left[i]?)
    (hRight : ∀ i, i < right.length → x.reverse[before (lanes 1) - rightStride * i]? = right[i]?) :
    ∃ ticks ≤ stridedCompareTime leftStride rightStride x.length left.length, ∃ after : R → Nat,
      (stridedCompare leftStride rightStride lanes).RunsValues x ticks before after ∧
      after (lanes 2) = 0 ∧ after (lanes 5) = compareLittleEndian (before (lanes 5)) left right ∧
      after (lanes 0) = before (lanes 0) - leftStride * left.length ∧
      after (lanes 1) = before (lanes 1) - rightStride * left.length ∧
      ∀ r, r ≠ lanes 0 → r ≠ lanes 1 → r ≠ lanes 2 → r ≠ lanes 5 → after r = before r := by
  have hLane (i j : Fin 6) : lanes i = lanes j ↔ i = j := ⟨fun e ↦ hLanes e, congrArg lanes⟩
  let loop := stridedCompare leftStride rightStride lanes
  induction left generalizing right before with
  | nil =>
    have hNil : right = [] := List.length_eq_zero_iff.mp hWidth.symm
    subst right
    refine ⟨1, by simp [stridedCompareTime], before, ?_, hCount, rfl,
      by simp, by simp, fun _ _ _ _ _ ↦ rfl⟩
    intro output
    exact run_countdown_zero (body := stridedCompareIteration leftStride rightStride lanes)
      rfl hCount
  | cons a left ih =>
    cases right with
    | nil => simp at hWidth
    | cons b right =>
      have hSame : left.length = right.length := by
        simpa only [List.length_cons, Nat.add_right_cancel_iff] using hWidth
      let tested := decrementValues (lanes 2) before
      have hTestL : tested (lanes 0) = before (lanes 0) := by simp [tested, decrementValues, hLane]
      have hTestR : tested (lanes 1) = before (lanes 1) := by simp [tested, decrementValues, hLane]
      have hTestI : tested (lanes 3) = 0 := by simp [tested, decrementValues, hLane, hIndex]
      have hTestW : tested (lanes 4) = 0 := by simp [tested, decrementValues, hLane, hWork]
      have hTestO : tested (lanes 5) = before (lanes 5) := by simp [tested, decrementValues, hLane]
      have hThisL := hLeft 0 (by simp)
      have hThisR := hRight 0 (by simp)
      obtain ⟨bodyTicks, hBodyTicks, hBody⟩ := runsValues_stridedCompareIteration
        leftStride rightStride lanes hLanes x tested a b hLeftStride hRightStride
        (by simpa only [hTestL, Nat.mul_zero, Nat.sub_zero, List.getElem?_cons_zero] using hThisL)
        (by simpa only [hTestR, Nat.mul_zero, Nat.sub_zero, List.getElem?_cons_zero] using hThisR)
        hTestI hTestW (hTestO.symm ▸ hOrder)
      let advanced := stridedCompareIterationValues leftStride rightStride lanes a b tested
      have hNextL : advanced (lanes 0) = before (lanes 0) - leftStride := by
        simp [advanced, stridedCompareIterationValues, compareIterationValues, hTestL,
          decrementValues, setValue, hLane]
        omega
      have hNextR : advanced (lanes 1) = before (lanes 1) - rightStride := by
        simp [advanced, stridedCompareIterationValues, compareIterationValues, hTestR,
          decrementValues, setValue, hLane]
        omega
      have hNextCount : advanced (lanes 2) = left.length := by
        simp [advanced, stridedCompareIterationValues, compareIterationValues, tested,
          decrementValues, setValue, hLane, hCount]
      have hNextI : advanced (lanes 3) = 0 := by
        simp [advanced, stridedCompareIterationValues, compareIterationValues, hTestI,
          decrementValues, setValue, hLane]
      have hNextW : advanced (lanes 4) = 0 := by
        simp [advanced, stridedCompareIterationValues, compareIterationValues, hTestW,
          decrementValues, setValue, hLane]
      have hNextO : advanced (lanes 5) = setOrdering (before (lanes 5)) a b := by
        simp [advanced, stridedCompareIterationValues, compareIterationValues, hTestO,
          decrementValues, setValue, hLane]
      have hTailL (i : Nat) (hi : i < left.length) :
          x.reverse[advanced (lanes 0) - leftStride * i]? = left[i]? := by
        rw [hNextL, Nat.sub_sub, Nat.add_comm leftStride (leftStride * i), ← Nat.mul_succ]
        exact hLeft (i + 1) (by simpa using hi)
      have hTailR (i : Nat) (hi : i < right.length) :
          x.reverse[advanced (lanes 1) - rightStride * i]? = right[i]? := by
        rw [hNextR, Nat.sub_sub, Nat.add_comm rightStride (rightStride * i), ← Nat.mul_succ]
        exact hRight (i + 1) (by simpa using hi)
      obtain ⟨tailTicks, hTailTicks, after, hTail, hZero, hResult, hEndL, hEndR, hFrame⟩ :=
        ih right advanced hSame hNextCount hNextI hNextW
          (hNextO.symm ▸ setOrdering_le_two _ _ _ hOrder) hTailL hTailR
      refine ⟨1 + bodyTicks + tailTicks, ?_, after, ?_, hZero, ?_, ?_, ?_, ?_⟩
      · rw [stridedCompareTime, List.length_cons, Nat.succ_mul]
        unfold stridedCompareTime at hTailTicks
        omega
      · intro output
        let start := loop.enter (⟨none, before, none, output⟩ : Config R Unit)
        have hPos : 0 < before (lanes 2) := by rw [hCount]; simp
        have hStep := run_countdown_iteration (counter := lanes 2) (cfg := start)
          rfl hPos (hBody output) rfl
        let mid := loop.enter (⟨none, advanced, none, output⟩ : Config R Unit)
        change RegisterMachine.run loop.close x (1 + bodyTicks) start = some mid at hStep
        change RegisterMachine.run loop.close x _ start = _
        rw [RegisterMachine.run_add, hStep, Option.bind_some]
        exact hTail output
      · rw [hResult, hNextO, compareLittleEndian]
      · rw [hEndL, hNextL, Nat.sub_sub, List.length_cons, Nat.mul_succ]
        omega
      · rw [hEndR, hNextR, Nat.sub_sub, List.length_cons, Nat.mul_succ]
        omega
      · intro r hl hr hc ho
        rw [hFrame r hl hr hc ho]
        simp [advanced, stridedCompareIterationValues, compareIterationValues, tested,
          decrementValues, setValue, hl, hr, hc, ho]

/-- Compare two equal-width little-endian lists from their specified reverse reads. -/
theorem runsValues_stridedCompare_of_reads (leftStride rightStride : Nat)
    (lanes : Fin 6 → R) (hLanes : Function.Injective lanes) (x left right : BinaryWord)
    (before : R → Nat) (hLeftStride : 0 < leftStride) (hRightStride : 0 < rightStride)
    (hWidth : left.length = right.length) (hCount : before (lanes 2) = left.length)
    (hIndex : before (lanes 3) = 0) (hWork : before (lanes 4) = 0)
    (hOrder : before (lanes 5) = 0)
    (hLeft : ∀ i, i < left.length → x.reverse[before (lanes 0) - leftStride * i]? = left[i]?)
    (hRight : ∀ i, i < right.length → x.reverse[before (lanes 1) - rightStride * i]? = right[i]?) :
    ∃ ticks ≤ stridedCompareTime leftStride rightStride x.length left.length, ∃ after : R → Nat,
      (stridedCompare leftStride rightStride lanes).RunsValues x ticks before after ∧
      after (lanes 2) = 0 ∧
      after (lanes 5) = (if fieldValue left < fieldValue right then 1
        else if fieldValue right < fieldValue left then 2 else 0) ∧
      after (lanes 0) = before (lanes 0) - leftStride * left.length ∧
      after (lanes 1) = before (lanes 1) - rightStride * left.length ∧
      ∀ r, r ≠ lanes 0 → r ≠ lanes 1 → r ≠ lanes 2 → r ≠ lanes 5 → after r = before r := by
  obtain ⟨ticks, hTicks, after, hRun, hZero, hResult, hEndL, hEndR, hFrame⟩ :=
    runsValues_stridedCompare_words leftStride rightStride lanes hLanes x left right before
      hLeftStride hRightStride hWidth hCount hIndex hWork (by rw [hOrder]; decide) hLeft hRight
  rw [compareLittleEndian_eq _ _ _ hWidth, hOrder] at hResult
  exact ⟨ticks, hTicks, after, hRun, hZero, hResult, hEndL, hEndR, hFrame⟩

/-- Compare in-range fields at ordinary input positions `start + stride * i`. -/
theorem runsValues_stridedCompare (leftStride rightStride : Nat)
    (lanes : Fin 6 → R) (hLanes : Function.Injective lanes) (x : BinaryWord)
    (leftStart rightStart width : Nat) (before : R → Nat)
    (hLeftStride : 0 < leftStride) (hRightStride : 0 < rightStride)
    (hLeftRange : ∀ i, i < width → leftStart + leftStride * i < x.length)
    (hRightRange : ∀ i, i < width → rightStart + rightStride * i < x.length)
    (hLeftPos : before (lanes 0) = x.length - 1 - leftStart)
    (hRightPos : before (lanes 1) = x.length - 1 - rightStart)
    (hWidth : before (lanes 2) = width) (hIndex : before (lanes 3) = 0)
    (hWork : before (lanes 4) = 0) (hOrder : before (lanes 5) = 0) :
    ∃ ticks ≤ stridedCompareTime leftStride rightStride x.length width, ∃ after : R → Nat,
      (stridedCompare leftStride rightStride lanes).RunsValues x ticks before after ∧
      after (lanes 2) = 0 ∧
      after (lanes 5) =
        (let left := fieldValue (stridedBits x leftStart leftStride width)
         let right := fieldValue (stridedBits x rightStart rightStride width)
         if left < right then 1 else if right < left then 2 else 0) ∧
      after (lanes 0) = before (lanes 0) - leftStride * width ∧
      after (lanes 1) = before (lanes 1) - rightStride * width ∧
      ∀ r, r ≠ lanes 0 → r ≠ lanes 1 → r ≠ lanes 2 → r ≠ lanes 5 → after r = before r := by
  have hBit (start stride i : Nat) (hi : i < width) (hRange : start + stride * i < x.length) :
      x.reverse[x.length - 1 - start - stride * i]? = (stridedBits x start stride width)[i]? := by
    have hReverse : x.length - 1 - start - stride * i + (start + stride * i) + 1 =
        x.length := by omega
    rw [List.getElem?_reverse' hReverse, getElem?_stridedBits x start stride width i hi hRange]
  simpa only [length_stridedBits] using runsValues_stridedCompare_of_reads leftStride rightStride
    lanes hLanes x (stridedBits x leftStart leftStride width)
      (stridedBits x rightStart rightStride width) before hLeftStride hRightStride
      (by simp) (by rw [length_stridedBits]; exact hWidth) hIndex hWork hOrder
      (fun i hi ↦ by
        rw [hLeftPos]
        have hi' : i < width := by simpa only [length_stridedBits] using hi
        exact hBit leftStart leftStride i hi' (hLeftRange i hi'))
      (fun i hi ↦ by
        rw [hRightPos]
        have hi' : i < width := by simpa only [length_stridedBits] using hi
        exact hBit rightStart rightStride i hi' (hRightRange i hi'))

end PvsNP.RegisterMachine.Fragment
