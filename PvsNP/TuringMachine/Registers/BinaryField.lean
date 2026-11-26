module

public import PvsNP.TuringMachine.Registers.BinaryCompare

import PvsNP.TuringMachine.Registers.OutputRuns

/-! # Decode a bounded binary field into a unary register

Reading from the reversed input presents a little-endian field most
significant bit first. Each iteration doubles the value already read and
adds the next bit. The bound charges this arithmetic to the decoded value.
-/

public section

namespace PvsNP.RegisterMachine.Fragment

open Circuits (circuitFieldWidth fieldValue)

variable {R : Type}

/-- Append a binary digit to a value read most-significant bit first. -/
@[expose] def pushBit (value : Nat) (bit : Bool) : Nat := 2 * value + bit.toNat

theorem le_foldl_pushBit (bits : BinaryWord) (value : Nat) :
    value ≤ bits.foldl pushBit value := by
  induction bits generalizing value with
  | nil => exact le_rfl
  | cons bit bits ih =>
    exact (show value ≤ pushBit value bit by unfold pushBit; omega).trans (ih _)

theorem foldl_reverse_pushBit_zero (bits : BinaryWord) :
    bits.reverse.foldl pushBit 0 = fieldValue bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    rw [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
    simp only [pushBit, fieldValue, Nat.add_comm]

/-- An arbitrary little-endian field of width `w` represents a value below `2^w`. -/
theorem fieldValue_lt_pow_length (bits : BinaryWord) : fieldValue bits < 2 ^ bits.length := by
  induction bits with
  | nil => decide
  | cons bit bits ih =>
    have hBit := Bool.toNat_le bit
    rw [fieldValue, List.length_cons, Nat.pow_succ]
    omega

/-- Descriptions with logarithmic field width have unary values bounded by twice
`n + s + 1`, including arbitrary bit patterns in malformed descriptions. -/
theorem fieldValue_le_circuitFieldWidth_cap (n s : Nat) (bits : BinaryWord)
    (hWidth : bits.length = circuitFieldWidth n s) : fieldValue bits ≤ 2 * (n + s + 1) := by
  have hValue := fieldValue_lt_pow_length bits
  rw [hWidth, circuitFieldWidth, Nat.pow_succ] at hValue
  by_cases hZero : n + s = 0
  · rw [hZero] at hValue ⊢
    have hTwo : 2 ^ (0 : Nat).log2 * 2 = 2 := by decide
    omega
  · have hPow := Nat.log2_self_le hZero
    omega

private def clearTemporary (lane : R) : Fragment R where
  Label := Unit
  entry := some ()
  code _ := .dec lane none (some ())

/-- Append a digit while restoring both temporary registers. -/
def pushRegisterBit (acc temporary scratch : R) (bit : Bool) : Fragment R :=
  (((add acc temporary scratch).seq (add temporary acc scratch)).seq
    (clearTemporary temporary)).seq (incrementBy acc bit.toNat)

private def fieldIteration (lanes : Fin 5 → R) : Fragment R :=
  (readRegisterBit (lanes 0) (lanes 3) (lanes 4) (fun result ↦
    pushRegisterBit (lanes 2) (lanes 3) (lanes 4) (result.getD false))).seq
    (incrementBy (lanes 0) 1)

/-- Lane 0 holds the reverse input offset and advances by the field width.
Lane 1 holds the width and is consumed. Lane 2 receives the field's value.
Lanes 3 and 4 are initially empty temporaries and are restored. -/
def binaryField (lanes : Fin 5 → R) : Fragment R :=
  countdown (lanes 1) (fieldIteration lanes)

/-- The instruction bound for an in-range field whose decoded value is at most `cap`. -/
@[expose] def binaryFieldCost (inputLength width cap : Nat) : Nat :=
  width * (7 * inputLength + 11 * cap + 13) + 1

/-- The bound is polynomial in the input length, field width, and unary value cap. -/
theorem binaryFieldCost_polynomiallyBounded {inputLength width cap : Nat → Nat}
    (hInput : PolynomiallyBounded inputLength) (hWidth : PolynomiallyBounded width)
    (hCap : PolynomiallyBounded cap) :
    PolynomiallyBounded (fun n ↦ binaryFieldCost (inputLength n) (width n) (cap n)) :=
  (hWidth.mul ((((PolynomiallyBounded.const 7).mul hInput).add
    ((PolynomiallyBounded.const 11).mul hCap)).add (PolynomiallyBounded.const 13))).add
    (PolynomiallyBounded.const 1)

/-- The description's field width and worst-case unary value cap are
polynomial whenever both the input wire count and gate cap are polynomial. -/
theorem binaryFieldCost_circuit_polynomiallyBounded {inputLength inputs gates : Nat → Nat}
    (hInput : PolynomiallyBounded inputLength) (hInputs : PolynomiallyBounded inputs)
    (hGates : PolynomiallyBounded gates) :
    PolynomiallyBounded (fun n ↦ binaryFieldCost (inputLength n)
      (circuitFieldWidth (inputs n) (gates n)) (2 * (inputs n + gates n + 1))) := by
  have hSum := (hInputs.add hGates).add (PolynomiallyBounded.const 1)
  exact binaryFieldCost_polynomiallyBounded hInput
    (hSum.mono fun n ↦ Nat.add_le_add_right (Nat.log2_le_self (inputs n + gates n)) 1)
    ((PolynomiallyBounded.const 2).mul hSum)

variable [DecidableEq R]

private theorem runsValues_clearTemporary (lane : R) (x : BinaryWord) (before : R → Nat) :
    (clearTemporary lane).RunsValues x (before lane + 1) before (clearValues lane before) := by
  intro output
  exact run_clear x (program := (clearTemporary lane).close) rfl
    (cfg := (clearTemporary lane).enter (⟨none, before, none, output⟩ : Config R Unit)) rfl

theorem runsValues_pushRegisterBit (acc temporary scratch : R)
    (x : BinaryWord) (before : R → Nat) (bit : Bool)
    (hAT : acc ≠ temporary) (hAS : acc ≠ scratch) (hTS : temporary ≠ scratch)
    (hTemporary : before temporary = 0) (hScratch : before scratch = 0) :
    (pushRegisterBit acc temporary scratch bit).RunsValues x
      (11 * before acc + 5 + bit.toNat) before
      (setValue acc (pushBit (before acc) bit) before) := by
  let copied := setValue temporary (before acc) before
  have hCopy : (add acc temporary scratch).RunsValues x (5 * before acc + 2) before copied := by
    simpa only [copied, hTemporary, Nat.zero_add] using
      runsValues_add acc temporary scratch x before hAT hAS hTS hScratch
  have hCopiedAcc : copied acc = before acc := setValue_other hAT ..
  have hCopiedTemp : copied temporary = before acc := setValue_same ..
  have hCopiedScratch : copied scratch = 0 := (setValue_other hTS.symm ..).trans hScratch
  let doubled := setValue acc (2 * before acc) copied
  have hDouble : (add temporary acc scratch).RunsValues x (5 * before acc + 2) copied doubled := by
    simpa only [doubled, hCopiedAcc, hCopiedTemp, Nat.two_mul] using
      runsValues_add temporary acc scratch x copied hAT.symm hTS hAS hCopiedScratch
  have hLength : doubled temporary = before acc :=
    (setValue_other hAT.symm ..).trans hCopiedTemp
  have hCleared : clearValues temporary doubled = setValue acc (2 * before acc) before := by
    funext r
    by_cases h : r = temporary <;> simp [clearValues, doubled, copied, setValue, h,
      hAT.symm, hTemporary]
  have hRun := ((hCopy.seq hDouble).seq
    (runsValues_clearTemporary temporary x doubled)).seq
    (runsValues_incrementBy acc bit.toNat x (clearValues temporary doubled))
  simpa only [pushRegisterBit, hLength, hCleared, setValue_same, setValue_replace, pushBit,
    show (5 * before acc + 2) + (5 * before acc + 2) + (before acc + 1) + bit.toNat =
      11 * before acc + 5 + bit.toNat by omega] using hRun

private def iterationValues (lanes : Fin 5 → R) (bit : Bool) (before : R → Nat) : R → Nat :=
  setValue (lanes 0) (before (lanes 0) + 1)
    (setValue (lanes 2) (pushBit (before (lanes 2)) bit) before)

private theorem runsValues_fieldIteration (lanes : Fin 5 → R) (hLanes : Function.Injective lanes)
    (x : BinaryWord) (before : R → Nat) (bit : Bool) (cap : Nat)
    (hRead : x.reverse[before (lanes 0)]? = some bit) (hCap : before (lanes 2) ≤ cap)
    (hIndex : before (lanes 3) = 0) (hScratch : before (lanes 4) = 0) :
    ∃ ticks ≤ 7 * x.length + 11 * cap + 12,
      (fieldIteration lanes).RunsValues x ticks before (iterationValues lanes bit before) := by
  have hDistinct (i j : Fin 5) (h : i ≠ j) : lanes i ≠ lanes j := fun e ↦ h (hLanes e)
  have hPush := runsValues_pushRegisterBit (lanes 2) (lanes 3) (lanes 4) x before bit
    (hDistinct 2 3 (by decide)) (hDistinct 2 4 (by decide)) (hDistinct 3 4 (by decide))
    hIndex hScratch
  have hReadRun := runsValues_readRegisterBit (lanes 0) (lanes 3) (lanes 4)
    (fun result ↦ pushRegisterBit (lanes 2) (lanes 3) (lanes 4) (result.getD false)) x before
    (hDistinct 0 3 (by decide)) (hDistinct 0 4 (by decide)) (hDistinct 3 4 (by decide))
    hIndex hScratch (by simpa only [hRead, Option.getD_some] using hPush)
  let pushed := setValue (lanes 2) (pushBit (before (lanes 2)) bit) before
  have hPos : pushed (lanes 0) = before (lanes 0) :=
    setValue_other (hDistinct 0 2 (by decide)) ..
  have hInc := runsValues_incrementBy (lanes 0) 1 x pushed
  have hRun := hReadRun.seq hInc
  refine ⟨_, ?_, by simpa only [fieldIteration, iterationValues, hPos] using hRun⟩
  have hInRange := (List.getElem?_eq_some_iff.mp hRead).choose
  simp only [List.length_reverse] at hInRange
  have hLookup := inputAtCost_le (before (lanes 0)) x.length
  have hBit := Bool.toNat_le bit
  omega

private theorem runsValues_binaryField_word (lanes : Fin 5 → R) (hLanes : Function.Injective lanes)
    (x bits : BinaryWord) (cap : Nat) (before : R → Nat)
    (hCount : before (lanes 1) = bits.length)
    (hIndex : before (lanes 3) = 0) (hScratch : before (lanes 4) = 0)
    (hCap : bits.foldl pushBit (before (lanes 2)) ≤ cap)
    (hRead : ∀ i, i < bits.length → x.reverse[before (lanes 0) + i]? = bits[i]?) :
    ∃ ticks ≤ binaryFieldCost x.length bits.length cap, ∃ after : R → Nat,
      (binaryField lanes).RunsValues x ticks before after ∧ after (lanes 1) = 0 ∧
      after (lanes 0) = before (lanes 0) + bits.length ∧
      after (lanes 2) = bits.foldl pushBit (before (lanes 2)) ∧
      ∀ r, r ≠ lanes 0 → r ≠ lanes 1 → r ≠ lanes 2 → after r = before r := by
  have hLane (i j : Fin 5) : lanes i = lanes j ↔ i = j := ⟨fun e ↦ hLanes e, congrArg lanes⟩
  induction bits generalizing before with
  | nil =>
    refine ⟨1, by simp [binaryFieldCost], before, ?_, hCount, by simp, rfl, fun _ _ _ _ ↦ rfl⟩
    intro output
    let start := (binaryField lanes).enter (⟨none, before, none, output⟩ : Config R Unit)
    exact run_countdown_zero (counter := lanes 1) (body := fieldIteration lanes)
      (cfg := start) rfl hCount
  | cons bit bits ih =>
    let tested := decrementValues (lanes 1) before
    have hTestPos : tested (lanes 0) = before (lanes 0) := by simp [tested, decrementValues, hLane]
    have hTestAcc : tested (lanes 2) = before (lanes 2) := by simp [tested, decrementValues, hLane]
    have hTestIndex : tested (lanes 3) = 0 := by simp [tested, decrementValues, hLane, hIndex]
    have hTestScratch : tested (lanes 4) = 0 := by simp [tested, decrementValues, hLane, hScratch]
    have hThis := hRead 0 (by simp)
    have hCurrent : tested (lanes 2) ≤ cap := by
      rw [hTestAcc]
      exact (le_foldl_pushBit _ _).trans hCap
    obtain ⟨bodyTicks, hBodyTicks, hBody⟩ := runsValues_fieldIteration lanes hLanes x tested bit cap
      (by simpa only [hTestPos, Nat.add_zero, List.getElem?_cons_zero] using hThis)
      hCurrent hTestIndex hTestScratch
    let advanced := iterationValues lanes bit tested
    have hNextPos : advanced (lanes 0) = before (lanes 0) + 1 := by
      simp [advanced, iterationValues, hTestPos]
    have hNextCount : advanced (lanes 1) = bits.length := by
      simp [advanced, iterationValues, tested, decrementValues, setValue, hLane, hCount]
    have hNextAcc : advanced (lanes 2) = pushBit (before (lanes 2)) bit := by
      simp [advanced, iterationValues, setValue, hLane, hTestAcc]
    have hNextIndex : advanced (lanes 3) = 0 := by
      simp [advanced, iterationValues, setValue, hLane, hTestIndex]
    have hNextScratch : advanced (lanes 4) = 0 := by
      simp [advanced, iterationValues, setValue, hLane, hTestScratch]
    have hNextCap : bits.foldl pushBit (advanced (lanes 2)) ≤ cap := by
      simpa only [hNextAcc, List.foldl_cons] using hCap
    have hTailBit (i : Nat) (hi : i < bits.length) :
        x.reverse[advanced (lanes 0) + i]? = bits[i]? := by
      rw [hNextPos, show before (lanes 0) + 1 + i = before (lanes 0) + (i + 1) by omega]
      exact hRead (i + 1) (by simpa using hi)
    obtain ⟨tailTicks, hTailTicks, after, hTail, hZero, hPos, hResult, hFrame⟩ :=
      ih advanced hNextCount hNextIndex hNextScratch hNextCap hTailBit
    refine ⟨1 + bodyTicks + tailTicks, ?_, after, ?_, hZero, ?_, ?_, ?_⟩
    · rw [binaryFieldCost, List.length_cons, Nat.succ_mul]
      unfold binaryFieldCost at hTailTicks
      omega
    · intro output
      let start := (binaryField lanes).enter (⟨none, before, none, output⟩ : Config R Unit)
      have hPositive : 0 < before (lanes 1) := by rw [hCount]; simp
      have hStep := run_countdown_iteration (counter := lanes 1) (cfg := start)
        rfl hPositive (hBody output) rfl
      let mid := (binaryField lanes).enter (⟨none, advanced, none, output⟩ : Config R Unit)
      change RegisterMachine.run (binaryField lanes).close x (1 + bodyTicks) start =
        some mid at hStep
      change RegisterMachine.run (binaryField lanes).close x _ start = _
      rw [RegisterMachine.run_add, hStep, Option.bind_some]
      exact hTail output
    · rw [hPos, hNextPos, List.length_cons]
      omega
    · rw [hResult, hNextAcc, List.foldl_cons]
    · intro r hp hc ha
      rw [hFrame r hp hc ha]
      simp [advanced, iterationValues, tested, decrementValues, setValue, hp, hc, ha]

/-- Decode an in-range field starting at an offset into `x.reverse`.
The value cap may be chosen from the field width, independently of its bits. -/
theorem runsValues_binaryField (lanes : Fin 5 → R) (hLanes : Function.Injective lanes)
    (x : BinaryWord) (start width cap : Nat) (before : R → Nat)
    (hRange : start + width ≤ x.length) (hStart : before (lanes 0) = start)
    (hWidth : before (lanes 1) = width) (hAccumulator : before (lanes 2) = 0)
    (hIndex : before (lanes 3) = 0) (hScratch : before (lanes 4) = 0)
    (hCap : fieldValue (((x.reverse.drop start).take width).reverse) ≤ cap) :
    ∃ ticks ≤ binaryFieldCost x.length width cap, ∃ after : R → Nat,
      (binaryField lanes).RunsValues x ticks before after ∧ after (lanes 1) = 0 ∧
      after (lanes 0) = start + width ∧
      after (lanes 2) = fieldValue (((x.reverse.drop start).take width).reverse) ∧
      ∀ r, r ≠ lanes 0 → r ≠ lanes 1 → r ≠ lanes 2 → after r = before r := by
  let bits := (x.reverse.drop start).take width
  have hLength : bits.length = width := by
    simp only [bits, List.length_take, List.length_drop, List.length_reverse]
    exact min_eq_left (by omega)
  have hBit (i : Nat) (hi : i < bits.length) : x.reverse[before (lanes 0) + i]? = bits[i]? := by
    rw [hStart, show bits[i]? = ((x.reverse.drop start).take width)[i]? by rfl,
      List.getElem?_take_of_lt (hLength ▸ hi), List.getElem?_drop]
  have hValue : bits.foldl pushBit (before (lanes 2)) = fieldValue bits.reverse := by
    simpa only [hAccumulator, List.reverse_reverse] using foldl_reverse_pushBit_zero bits.reverse
  obtain ⟨ticks, hTicks, after, hRun, hZero, hPos, hResult, hFrame⟩ :=
    runsValues_binaryField_word lanes hLanes x bits cap before (hWidth.trans hLength.symm)
      hIndex hScratch (by rwa [hValue]) hBit
  rw [hLength] at hTicks
  rw [hStart, hLength] at hPos
  rw [hValue] at hResult
  exact ⟨ticks, hTicks, after, hRun, hZero, hPos, hResult, hFrame⟩

/-- The reverse input offset of a complete little-endian field is the number
of bits after it. Reversing the bits read there recovers the ordinary slice. -/
theorem reverseField_eq_take_drop (x : BinaryWord) (start width : Nat)
    (hRange : start + width ≤ x.length) :
    ((x.reverse.drop (x.length - (start + width))).take width).reverse =
      (x.drop start).take width := by
  rw [List.drop_reverse, show x.length - (x.length - (start + width)) = start + width by omega,
    List.take_reverse, List.reverse_reverse, List.length_take_of_le hRange,
    show start + width - width = start by omega, List.take_drop]

/-- Decode a circuit-description field at an ordinary offset in the input.
This uses a unary value cap linear in the number of input wires and gates. -/
theorem runsValues_binaryField_circuit (lanes : Fin 5 → R) (hLanes : Function.Injective lanes)
    (x : BinaryWord) (n s start : Nat) (before : R → Nat)
    (hRange : start + circuitFieldWidth n s ≤ x.length)
    (hStart : before (lanes 0) = x.length - (start + circuitFieldWidth n s))
    (hWidth : before (lanes 1) = circuitFieldWidth n s) (hAccumulator : before (lanes 2) = 0)
    (hIndex : before (lanes 3) = 0) (hScratch : before (lanes 4) = 0) :
    ∃ ticks ≤ binaryFieldCost x.length (circuitFieldWidth n s) (2 * (n + s + 1)),
      ∃ after : R → Nat,
        (binaryField lanes).RunsValues x ticks before after ∧ after (lanes 1) = 0 ∧
        after (lanes 0) = x.length - start ∧
        after (lanes 2) = fieldValue ((x.drop start).take (circuitFieldWidth n s)) ∧
        ∀ r, r ≠ lanes 0 → r ≠ lanes 1 → r ≠ lanes 2 → after r = before r := by
  let width := circuitFieldWidth n s
  have hSlice := reverseField_eq_take_drop x start width hRange
  have hSliceLength : ((x.drop start).take width).length = width := by
    rw [List.length_take_of_le]
    simp only [List.length_drop]
    omega
  have hCap := fieldValue_le_circuitFieldWidth_cap n s _ hSliceLength
  obtain ⟨ticks, hTicks, after, hRun, hZero, hPos, hResult, hFrame⟩ :=
    runsValues_binaryField lanes hLanes x (x.length - (start + width))
      width (2 * (n + s + 1)) before (by omega) hStart hWidth hAccumulator hIndex hScratch
      (by rwa [hSlice])
  rw [hSlice] at hResult
  exact ⟨ticks, hTicks, after, hRun, hZero, hPos.trans (by omega), hResult, hFrame⟩

end PvsNP.RegisterMachine.Fragment
