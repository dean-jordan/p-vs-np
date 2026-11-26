module

public import PvsNP.Circuits.Description
public import PvsNP.TuringMachine.Registers.Countdown
public import PvsNP.TuringMachine.Registers.Lookup
public import PvsNP.TuringMachine.Registers.Clear

/-! # Compare binary fields directly in the input

The two position registers index the reversed input. Each loop reads one
bit per field, beginning at the least significant bits, and replaces the
comparison whenever the two bits differ. Only input offsets and the loop
count are represented in unary.
-/

public section

namespace PvsNP.RegisterMachine.Fragment

open Circuits (fieldValue)

variable {R : Type}

/-- Later, more significant unequal bits replace the previous result. -/
@[expose] def setOrdering (old : Nat) (a b : Bool) : Nat :=
  if a = b then old else if a then 2 else 1

/-- Compare two equally wide fields starting at their least significant bits. -/
@[expose] def compareLittleEndian (old : Nat) : BinaryWord → BinaryWord → Nat
  | a :: as, b :: bs => compareLittleEndian (setOrdering old a b) as bs
  | _, _ => old

private def clearLane (lane : R) : Fragment R where
  Label := Unit
  entry := some ()
  code _ := .dec lane none (some ())

/-- Decrement a lane once, leaving zero unchanged. -/
def decrementLane (lane : R) : Fragment R where
  Label := Unit
  entry := some ()
  code _ := .dec lane none none

private def writeOrdering (lane : R) (a b : Bool) : Fragment R :=
  if a = b then skip else (clearLane lane).seq (incrementBy lane (setOrdering 0 a b))

/-- Read at a reverse position while preserving the position register. -/
@[expose] def readRegisterBit (position index work : R) (branches : Option Bool → Fragment R) :
    Fragment R :=
  (add position index work).seq (lookup index branches)

private def readRight (lanes : Fin 6 → R) (a : Option Bool) : Fragment R :=
  readRegisterBit (lanes 1) (lanes 3) (lanes 4) fun b ↦
    writeOrdering (lanes 5) (a.getD false) (b.getD false)

private def comparePair (lanes : Fin 6 → R) : Fragment R :=
  readRegisterBit (lanes 0) (lanes 3) (lanes 4) (readRight lanes)

/-- Compare one bit pair, then move both reversed positions one step left. -/
def compareIteration (lanes : Fin 6 → R) : Fragment R :=
  (comparePair lanes).seq ((decrementLane (lanes 0)).seq (decrementLane (lanes 1)))

/-- Lanes 0 and 1 hold reverse input positions, lane 2 holds the number of
bits, lanes 3 and 4 are scratch, and lane 5 stores 0, 1, or 2 for equality,
less than, or greater than. -/
def binaryCompare (lanes : Fin 6 → R) : Fragment R :=
  countdown (lanes 2) (compareIteration lanes)

theorem setOrdering_le_two (old : Nat) (a b : Bool) (hOld : old ≤ 2) :
    setOrdering old a b ≤ 2 := by
  cases a <;> cases b <;> simp [setOrdering, hOld]

theorem compareLittleEndian_eq (old : Nat) (left right : BinaryWord)
    (hWidth : left.length = right.length) :
    compareLittleEndian old left right =
      if fieldValue left < fieldValue right then 1
      else if fieldValue right < fieldValue left then 2 else old := by
  induction left generalizing old right with
  | nil =>
    cases right with
    | nil => simp [compareLittleEndian, fieldValue]
    | cons b bs => simp at hWidth
  | cons a as ih =>
    cases right with
    | nil => simp at hWidth
    | cons b bs =>
      have hSame : as.length = bs.length := by
        simpa only [List.length_cons, Nat.add_right_cancel_iff] using hWidth
      simp only [compareLittleEndian, ih _ _ hSame, fieldValue]
      rcases lt_trichotomy (fieldValue as) (fieldValue bs) with hLt | hEq | hGt
      · have hAll : a.toNat + 2 * fieldValue as < b.toNat + 2 * fieldValue bs := by
          have ha := Bool.toNat_le a
          omega
        simp [hLt, hAll]
      · cases a <;> cases b <;> simp [hEq, setOrdering, Bool.toNat]
      · have hAll : b.toNat + 2 * fieldValue bs < a.toNat + 2 * fieldValue as := by
          have hb := Bool.toNat_le b
          omega
        simp [hGt, Nat.not_lt.mpr hGt.le, hAll, Nat.not_lt.mpr hAll.le]

variable [DecidableEq R]

private theorem runsValues_clearLane (lane : R) (x : BinaryWord) (before : R → Nat) :
    (clearLane lane).RunsValues x (before lane + 1) before (clearValues lane before) := by
  intro output
  exact run_clear x (program := (clearLane lane).close) rfl
    (cfg := (clearLane lane).enter (⟨none, before, none, output⟩ : Config R Unit)) rfl

theorem runsValues_decrementLane (lane : R) (x : BinaryWord) (before : R → Nat) :
    (decrementLane lane).RunsValues x 1 before (decrementValues lane before) := by
  intro output
  let start := (decrementLane lane).enter (⟨none, before, none, output⟩ : Config R Unit)
  let program := (decrementLane lane).close
  change RegisterMachine.run program x 1 start = _
  rw [RegisterMachine.run_succ]
  by_cases hZero : before lane = 0
  · rw [step_dec_zero (program := program) (cfg := start) rfl rfl hZero]
    simp only [Option.bind_some, RegisterMachine.run_zero, Option.some.injEq]
    congr
    funext r
    by_cases h : r = lane <;> simp [start, decrementValues, h, hZero, enter]
  · rw [step_dec_pos (program := program) (cfg := start) rfl rfl (Nat.pos_of_ne_zero hZero)]
    rfl

private theorem runsValues_writeOrdering (lane : R) (a b : Bool) (x : BinaryWord)
    (before : R → Nat) (hOld : before lane ≤ 2) :
    ∃ ticks ≤ 5, (writeOrdering lane a b).RunsValues x ticks before
      (setValue lane (setOrdering (before lane) a b) before) := by
  by_cases hEq : a = b
  · have hValue : setValue lane (before lane) before = before := by
      funext r
      by_cases h : r = lane <;> simp [setValue, h]
    exact ⟨0, by decide, by
      simpa only [writeOrdering, setOrdering, ite_eq_left hEq, hValue] using
        runsValues_skip x before⟩
  · let value := setOrdering 0 a b
    have hValue : value = setOrdering (before lane) a b := by simp [value, setOrdering, hEq]
    have hBound := setOrdering_le_two 0 a b (by decide)
    have hRestore : setValue lane ((clearValues lane before) lane + value)
        (clearValues lane before) = setValue lane value before := by
      funext r
      by_cases h : r = lane <;> simp [setValue, clearValues, h]
    have hRun := (runsValues_clearLane lane x before).seq
      (runsValues_incrementBy lane value x (clearValues lane before))
    refine ⟨before lane + 1 + value, by omega, ?_⟩
    rw [writeOrdering, ite_eq_right hEq, ← hValue]
    simpa only [hRestore] using hRun

/-- Lookup restores both scratch registers before starting the selected branch. -/
theorem runsValues_readRegisterBit (position index work : R)
    (branches : Option Bool → Fragment R) (x : BinaryWord) (before : R → Nat)
    (hPI : position ≠ index) (hPW : position ≠ work) (hIW : index ≠ work)
    (hIndex : before index = 0) (hWork : before work = 0) {ticks : Nat} {after : R → Nat}
    (hBranch : (branches x.reverse[before position]?).RunsValues x ticks before after) :
    (readRegisterBit position index work branches).RunsValues x
      (5 * before position + 2 + (inputAtCost (before position) x.length + ticks))
      before after := by
  let copied := setValue index (before position) before
  have hCopy : (add position index work).RunsValues x (5 * before position + 2) before copied := by
    simpa only [hIndex, Nat.zero_add, copied] using
      runsValues_add position index work x before hPI hPW hIW hWork
  have hPos : copied index = before position := setValue_same ..
  have hClear : clearInputAtIndex index copied = before := by
    funext r
    by_cases h : r = index <;> simp [copied, clearInputAtIndex, setValue, h, hIndex]
  have hLookup := runsValues_lookup index branches x copied
    (by simpa only [hPos, hClear] using hBranch)
  simpa only [readRegisterBit, hPos] using hCopy.seq hLookup

/-- The register values after a comparison iteration. -/
@[expose] def compareIterationValues (lanes : Fin 6 → R) (a b : Bool) (before : R → Nat) :
    R → Nat :=
  decrementValues (lanes 1) (decrementValues (lanes 0)
    (setValue (lanes 5) (setOrdering (before (lanes 5)) a b) before))

theorem runsValues_compareIteration (lanes : Fin 6 → R) (hLanes : Function.Injective lanes)
    (x : BinaryWord) (before : R → Nat) (a b : Bool)
    (hLeft : x.reverse[before (lanes 0)]? = some a)
    (hRight : x.reverse[before (lanes 1)]? = some b)
    (hIndex : before (lanes 3) = 0) (hWork : before (lanes 4) = 0)
    (hOld : before (lanes 5) ≤ 2) :
    ∃ ticks ≤ 14 * x.length + 17,
      (compareIteration lanes).RunsValues x ticks before
        (compareIterationValues lanes a b before) := by
  have hDistinct (i j : Fin 6) (h : i ≠ j) : lanes i ≠ lanes j := fun e ↦ h (hLanes e)
  obtain ⟨writeTicks, hWriteTicks, hWrite⟩ := runsValues_writeOrdering (lanes 5) a b x before hOld
  have hReadR := runsValues_readRegisterBit (lanes 1) (lanes 3) (lanes 4)
    (fun bit ↦ writeOrdering (lanes 5) a (bit.getD false)) x before
    (hDistinct 1 3 (by decide)) (hDistinct 1 4 (by decide)) (hDistinct 3 4 (by decide))
    hIndex hWork (by simpa only [hRight, Option.getD_some] using hWrite)
  have hReadL := runsValues_readRegisterBit (lanes 0) (lanes 3) (lanes 4) (readRight lanes)
    x before (hDistinct 0 3 (by decide)) (hDistinct 0 4 (by decide)) (hDistinct 3 4 (by decide))
    hIndex hWork (by simpa only [hLeft, readRight, Option.getD_some] using hReadR)
  let ordered := setValue (lanes 5) (setOrdering (before (lanes 5)) a b) before
  have hDec := (runsValues_decrementLane (lanes 0) x ordered).seq
    (runsValues_decrementLane (lanes 1) x (decrementValues (lanes 0) ordered))
  have hRun := hReadL.seq hDec
  refine ⟨_, ?_, hRun⟩
  have hl := (List.getElem?_eq_some_iff.mp hLeft).choose
  have hr := (List.getElem?_eq_some_iff.mp hRight).choose
  simp only [List.length_reverse] at hl hr
  have hCostL := inputAtCost_le (before (lanes 0)) x.length
  have hCostR := inputAtCost_le (before (lanes 1)) x.length
  omega

/-- At most this many register instructions compare two in-range fields. -/
@[expose] def binaryCompareTime (inputLength width : Nat) : Nat :=
  width * (14 * inputLength + 18) + 1

theorem binaryCompareTime_le_input (input width : Nat) (hWidth : width ≤ input) :
    binaryCompareTime input width ≤ binaryCompareTime input input :=
  Nat.add_le_add_right (Nat.mul_le_mul_right _ hWidth) _

theorem binaryCompareTime_input_polynomiallyBounded :
    PolynomiallyBounded (fun n ↦ binaryCompareTime n n) :=
  (PolynomiallyBounded.id.mul
    (((PolynomiallyBounded.const 14).mul PolynomiallyBounded.id).add
      (PolynomiallyBounded.const 18))).add (PolynomiallyBounded.const 1)

private theorem runsValues_binaryCompare_words (lanes : Fin 6 → R)
    (hLanes : Function.Injective lanes) (x left right : BinaryWord) (before : R → Nat)
    (hWidth : left.length = right.length) (hCount : before (lanes 2) = left.length)
    (hIndex : before (lanes 3) = 0) (hWork : before (lanes 4) = 0)
    (hOrder : before (lanes 5) ≤ 2)
    (hLeft : ∀ i, i < left.length → x.reverse[before (lanes 0) - i]? = left[i]?)
    (hRight : ∀ i, i < right.length → x.reverse[before (lanes 1) - i]? = right[i]?) :
    ∃ ticks ≤ binaryCompareTime x.length left.length, ∃ after : R → Nat,
      (binaryCompare lanes).RunsValues x ticks before after ∧ after (lanes 2) = 0 ∧
      after (lanes 5) = compareLittleEndian (before (lanes 5)) left right ∧
      ∀ r, r ≠ lanes 0 → r ≠ lanes 1 → r ≠ lanes 2 → r ≠ lanes 5 → after r = before r := by
  have hLane (i j : Fin 6) : lanes i = lanes j ↔ i = j := ⟨fun e ↦ hLanes e, congrArg lanes⟩
  induction left generalizing right before with
  | nil =>
    have hNil : right = [] := List.length_eq_zero_iff.mp hWidth.symm
    subst right
    refine ⟨1, by simp [binaryCompareTime], before, ?_, hCount, rfl, fun _ _ _ _ _ ↦ rfl⟩
    intro output
    exact run_countdown_zero (body := compareIteration lanes) rfl hCount
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
      obtain ⟨bodyTicks, hBodyTicks, hBody⟩ := runsValues_compareIteration lanes hLanes x tested a b
        (by simpa only [hTestL, Nat.sub_zero, List.getElem?_cons_zero] using hThisL)
        (by simpa only [hTestR, Nat.sub_zero, List.getElem?_cons_zero] using hThisR)
        hTestI hTestW (hTestO.symm ▸ hOrder)
      let advanced := compareIterationValues lanes a b tested
      have hNextL : advanced (lanes 0) = before (lanes 0) - 1 := by
        simp [advanced, compareIterationValues, tested, decrementValues, setValue, hLane]
      have hNextR : advanced (lanes 1) = before (lanes 1) - 1 := by
        simp [advanced, compareIterationValues, tested, decrementValues, setValue, hLane]
      have hNextCount : advanced (lanes 2) = left.length := by
        simp [advanced, compareIterationValues, tested, decrementValues, setValue, hLane, hCount]
      have hNextI : advanced (lanes 3) = 0 := by
        simp [advanced, compareIterationValues, tested, decrementValues, setValue, hLane, hIndex]
      have hNextW : advanced (lanes 4) = 0 := by
        simp [advanced, compareIterationValues, tested, decrementValues, setValue, hLane, hWork]
      have hNextO : advanced (lanes 5) = setOrdering (before (lanes 5)) a b := by
        simp [advanced, compareIterationValues, tested, decrementValues, setValue, hLane]
      have hTailL (i : Nat) (hi : i < left.length) :
          x.reverse[advanced (lanes 0) - i]? = left[i]? := by
        rw [hNextL, Nat.sub_sub, Nat.add_comm 1 i]
        exact hLeft (i + 1) (by simpa using hi)
      have hTailR (i : Nat) (hi : i < right.length) :
          x.reverse[advanced (lanes 1) - i]? = right[i]? := by
        rw [hNextR, Nat.sub_sub, Nat.add_comm 1 i]
        exact hRight (i + 1) (by simpa using hi)
      obtain ⟨tailTicks, hTailTicks, after, hTail, hZero, hResult, hFrame⟩ :=
        ih right advanced hSame hNextCount hNextI hNextW
          (hNextO.symm ▸ setOrdering_le_two _ _ _ hOrder) hTailL hTailR
      refine ⟨1 + bodyTicks + tailTicks, ?_, after, ?_, hZero, ?_, ?_⟩
      · rw [binaryCompareTime, List.length_cons, Nat.succ_mul]
        unfold binaryCompareTime at hTailTicks
        omega
      · intro output
        let start := (binaryCompare lanes).enter (⟨none, before, none, output⟩ : Config R Unit)
        have hPos : 0 < before (lanes 2) := by rw [hCount]; simp
        have hStep := run_countdown_iteration (counter := lanes 2) (cfg := start)
          rfl hPos (hBody output) rfl
        let mid := (binaryCompare lanes).enter (⟨none, advanced, none, output⟩ : Config R Unit)
        change RegisterMachine.run (binaryCompare lanes).close x (1 + bodyTicks) start =
          some mid at hStep
        change RegisterMachine.run (binaryCompare lanes).close x _ start = _
        rw [RegisterMachine.run_add, hStep, Option.bind_some]
        exact hTail output
      · rw [hResult, hNextO]
        rfl
      · intro r hl hr hc ho
        rw [hFrame r hl hr hc ho]
        simp [advanced, compareIterationValues, tested, decrementValues, setValue, hl, hr, hc, ho]

/-- Compare equally wide little-endian fields at two ordinary input offsets.
The width lane is consumed and all lanes outside 0, 1, 2, and 5 are preserved. -/
theorem runsValues_binaryCompare (lanes : Fin 6 → R) (hLanes : Function.Injective lanes)
    (x : BinaryWord) (leftStart rightStart width : Nat) (before : R → Nat)
    (hLeft : leftStart + width ≤ x.length) (hRight : rightStart + width ≤ x.length)
    (hLeftPos : before (lanes 0) = x.length - 1 - leftStart)
    (hRightPos : before (lanes 1) = x.length - 1 - rightStart)
    (hWidth : before (lanes 2) = width) (hIndex : before (lanes 3) = 0)
    (hWork : before (lanes 4) = 0) (hOrder : before (lanes 5) = 0) :
    ∃ ticks ≤ binaryCompareTime x.length width, ∃ after : R → Nat,
      (binaryCompare lanes).RunsValues x ticks before after ∧ after (lanes 2) = 0 ∧
      after (lanes 5) =
        (let left := fieldValue ((x.drop leftStart).take width)
         let right := fieldValue ((x.drop rightStart).take width)
         if left < right then 1 else if right < left then 2 else 0) ∧
      ∀ r, r ≠ lanes 0 → r ≠ lanes 1 → r ≠ lanes 2 → r ≠ lanes 5 → after r = before r := by
  let left := (x.drop leftStart).take width
  let right := (x.drop rightStart).take width
  have hLen (start : Nat) (h : start + width ≤ x.length) :
      ((x.drop start).take width).length = width := by
    rw [List.length_take, List.length_drop, Nat.min_eq_left (by omega)]
  have hBit (start : Nat) (h : start + width ≤ x.length) (i : Nat) (hi : i < width) :
      x.reverse[x.length - 1 - start - i]? = ((x.drop start).take width)[i]? := by
    rw [List.getElem?_take_of_lt hi, List.getElem?_drop, Nat.sub_sub]
    exact List.getElem?_reverse' (by omega)
  have hLenL : left.length = width := hLen leftStart hLeft
  have hLenR : right.length = width := hLen rightStart hRight
  have hSame := hLenL.trans hLenR.symm
  obtain ⟨ticks, hTicks, after, hRun, hZero, hResult, hFrame⟩ :=
    runsValues_binaryCompare_words lanes hLanes x left right before hSame
      (hWidth.trans hLenL.symm) hIndex hWork (by rw [hOrder]; decide)
      (fun i hi ↦ by rw [hLeftPos]; exact hBit leftStart hLeft i (hLenL ▸ hi))
      (fun i hi ↦ by rw [hRightPos]; exact hBit rightStart hRight i (hLenR ▸ hi))
  refine ⟨ticks, hLenL ▸ hTicks, after, hRun, hZero, ?_, hFrame⟩
  rw [hResult, compareLittleEndian_eq _ _ _ hSame, hOrder]

end PvsNP.RegisterMachine.Fragment
