module

public import PvsNP.TuringMachine.Registers.BinaryField

/-! # Counted reads of strided binary fields

A strided field stores consecutive digits a fixed number of input positions
apart. The reader scans a little-endian field through the reverse input cursor
and appends each digit using the bounded binary-field arithmetic.
-/

public section

namespace PvsNP.RegisterMachine.Fragment

open Circuits (circuitFieldWidth fieldValue)

variable {R : Type}

/-- Sample the indicated positions in their listed order. -/
@[expose] def stridedBits (x : BinaryWord) (start stride width : Nat) : BinaryWord :=
  List.ofFn fun i : Fin width ↦ (x[start + stride * i.val]?).getD false

@[simp] theorem length_stridedBits (x : BinaryWord) (start stride width : Nat) :
    (stridedBits x start stride width).length = width :=
  List.length_ofFn

theorem getElem?_stridedBits (x : BinaryWord) (start stride width i : Nat)
    (hWidth : i < width) (hPosition : start + stride * i < x.length) :
    (stridedBits x start stride width)[i]? = x[start + stride * i]? := by
  simp only [stridedBits, List.getElem?_ofFn, dite_eq_left hWidth,
    List.getElem?_eq_getElem hPosition, Option.getD_some]

/-- Read at a reverse position, run the selected branch, then advance by `stride`. -/
@[expose] def readRegisterBitAdvance (stride : Nat) (position index work : R)
    (branches : Option Bool → Fragment R) : Fragment R :=
  (readRegisterBit position index work branches).seq (incrementBy position stride)

private def stridedIteration (stride : Nat) (lanes : Fin 5 → R) : Fragment R :=
  readRegisterBitAdvance stride (lanes 0) (lanes 3) (lanes 4) fun result ↦
    pushRegisterBit (lanes 2) (lanes 3) (lanes 4) (result.getD false)

/-- Lane 0 holds the reverse position, lane 1 is the remaining width, and
lane 2 accumulates the value. Lanes 3 and 4 are restored scratch registers. -/
def stridedField (stride : Nat) (lanes : Fin 5 → R) : Fragment R :=
  countdown (lanes 1) (stridedIteration stride lanes)

/-- Instruction bound for a field decoded within the unary value cap. -/
@[expose] def stridedFieldCost (stride inputLength width cap : Nat) : Nat :=
  width * (7 * inputLength + 11 * cap + 12 + stride) + 1

theorem stridedFieldCost_polynomiallyBounded (stride : Nat)
    {inputLength width cap : Nat → Nat} (hInput : PolynomiallyBounded inputLength)
    (hWidth : PolynomiallyBounded width) (hCap : PolynomiallyBounded cap) :
    PolynomiallyBounded (fun n ↦ stridedFieldCost stride (inputLength n) (width n) (cap n)) :=
  (hWidth.mul (((((PolynomiallyBounded.const 7).mul hInput).add
    ((PolynomiallyBounded.const 11).mul hCap)).add (PolynomiallyBounded.const 12)).add
    (PolynomiallyBounded.const stride))).add (PolynomiallyBounded.const 1)

theorem stridedFieldCost_circuit_polynomiallyBounded (stride : Nat)
    {inputLength inputs gates : Nat → Nat} (hInput : PolynomiallyBounded inputLength)
    (hInputs : PolynomiallyBounded inputs) (hGates : PolynomiallyBounded gates) :
    PolynomiallyBounded (fun n ↦ stridedFieldCost stride (inputLength n)
      (circuitFieldWidth (inputs n) (gates n)) (2 * (inputs n + gates n + 1))) := by
  have hSum := (hInputs.add hGates).add (PolynomiallyBounded.const 1)
  exact stridedFieldCost_polynomiallyBounded stride hInput
    (hSum.mono fun n ↦ Nat.add_le_add_right (Nat.log2_le_self (inputs n + gates n)) 1)
    ((PolynomiallyBounded.const 2).mul hSum)

variable [DecidableEq R]

theorem runsValues_readRegisterBitAdvance (stride : Nat) (position index work : R)
    (branches : Option Bool → Fragment R) (x : BinaryWord) (before : R → Nat)
    (hPI : position ≠ index) (hPW : position ≠ work) (hIW : index ≠ work)
    (hIndex : before index = 0) (hWork : before work = 0) {ticks : Nat} {after : R → Nat}
    (hBranch : (branches x.reverse[before position]?).RunsValues x ticks before after) :
    (readRegisterBitAdvance stride position index work branches).RunsValues x
      (5 * before position + 2 + (inputAtCost (before position) x.length + ticks) + stride)
      before (setValue position (after position + stride) after) :=
  (runsValues_readRegisterBit position index work branches x before
    hPI hPW hIW hIndex hWork hBranch).seq (runsValues_incrementBy position stride x after)

private def stridedIterationValues (stride : Nat) (lanes : Fin 5 → R) (bit : Bool)
    (before : R → Nat) : R → Nat :=
  setValue (lanes 0) (before (lanes 0) + stride)
    (setValue (lanes 2) (pushBit (before (lanes 2)) bit) before)

private theorem runsValues_stridedIteration (stride : Nat) (lanes : Fin 5 → R)
    (hLanes : Function.Injective lanes) (x : BinaryWord) (before : R → Nat) (bit : Bool)
    (cap : Nat) (hRead : x.reverse[before (lanes 0)]? = some bit)
    (hCap : before (lanes 2) ≤ cap) (hIndex : before (lanes 3) = 0)
    (hScratch : before (lanes 4) = 0) :
    ∃ ticks ≤ 7 * x.length + 11 * cap + 11 + stride,
      (stridedIteration stride lanes).RunsValues x ticks before
        (stridedIterationValues stride lanes bit before) := by
  have hDistinct (i j : Fin 5) (h : i ≠ j) : lanes i ≠ lanes j := fun e ↦ h (hLanes e)
  have hPush := runsValues_pushRegisterBit (lanes 2) (lanes 3) (lanes 4) x before bit
    (hDistinct 2 3 (by decide)) (hDistinct 2 4 (by decide)) (hDistinct 3 4 (by decide))
    hIndex hScratch
  have hRun := runsValues_readRegisterBitAdvance stride (lanes 0) (lanes 3) (lanes 4)
    (fun result ↦ pushRegisterBit (lanes 2) (lanes 3) (lanes 4) (result.getD false)) x before
    (hDistinct 0 3 (by decide)) (hDistinct 0 4 (by decide)) (hDistinct 3 4 (by decide))
    hIndex hScratch (by simpa only [hRead, Option.getD_some] using hPush)
  have hPos : setValue (lanes 2) (pushBit (before (lanes 2)) bit) before (lanes 0) =
      before (lanes 0) :=
    setValue_other (hDistinct 0 2 (by decide)) ..
  refine ⟨_, ?_, by simpa only [stridedIteration, stridedIterationValues, hPos] using hRun⟩
  have hInRange := (List.getElem?_eq_some_iff.mp hRead).choose
  simp only [List.length_reverse] at hInRange
  have hLookup := inputAtCost_le (before (lanes 0)) x.length
  have hBit := Bool.toNat_le bit
  omega

private theorem runsValues_stridedField_word (stride : Nat) (lanes : Fin 5 → R)
    (hLanes : Function.Injective lanes) (x bits : BinaryWord) (cap : Nat) (before : R → Nat)
    (hCount : before (lanes 1) = bits.length)
    (hIndex : before (lanes 3) = 0) (hScratch : before (lanes 4) = 0)
    (hCap : bits.foldl pushBit (before (lanes 2)) ≤ cap)
    (hRead : ∀ i, i < bits.length → x.reverse[before (lanes 0) + stride * i]? = bits[i]?) :
    ∃ ticks ≤ stridedFieldCost stride x.length bits.length cap, ∃ after : R → Nat,
      (stridedField stride lanes).RunsValues x ticks before after ∧ after (lanes 1) = 0 ∧
      after (lanes 0) = before (lanes 0) + stride * bits.length ∧
      after (lanes 2) = bits.foldl pushBit (before (lanes 2)) ∧
      ∀ r, r ≠ lanes 0 → r ≠ lanes 1 → r ≠ lanes 2 → after r = before r := by
  have hLane (i j : Fin 5) : lanes i = lanes j ↔ i = j := ⟨fun e ↦ hLanes e, congrArg lanes⟩
  induction bits generalizing before with
  | nil =>
    refine ⟨1, by simp [stridedFieldCost], before, ?_, hCount, by simp, rfl, fun _ _ _ _ ↦ rfl⟩
    intro output
    let start := (stridedField stride lanes).enter (⟨none, before, none, output⟩ : Config R Unit)
    exact run_countdown_zero (counter := lanes 1) (body := stridedIteration stride lanes)
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
    obtain ⟨bodyTicks, hBodyTicks, hBody⟩ :=
      runsValues_stridedIteration stride lanes hLanes x tested bit cap
        (by simpa only [hTestPos, Nat.mul_zero, Nat.add_zero, List.getElem?_cons_zero] using hThis)
        hCurrent hTestIndex hTestScratch
    let advanced := stridedIterationValues stride lanes bit tested
    have hNextPos : advanced (lanes 0) = before (lanes 0) + stride := by
      simp [advanced, stridedIterationValues, hTestPos]
    have hNextCount : advanced (lanes 1) = bits.length := by
      simp [advanced, stridedIterationValues, tested, decrementValues, setValue, hLane, hCount]
    have hNextAcc : advanced (lanes 2) = pushBit (before (lanes 2)) bit := by
      simp [advanced, stridedIterationValues, setValue, hLane, hTestAcc]
    have hNextIndex : advanced (lanes 3) = 0 := by
      simp [advanced, stridedIterationValues, setValue, hLane, hTestIndex]
    have hNextScratch : advanced (lanes 4) = 0 := by
      simp [advanced, stridedIterationValues, setValue, hLane, hTestScratch]
    have hNextCap : bits.foldl pushBit (advanced (lanes 2)) ≤ cap := by
      simpa only [hNextAcc, List.foldl_cons] using hCap
    have hTailBit (i : Nat) (hi : i < bits.length) :
        x.reverse[advanced (lanes 0) + stride * i]? = bits[i]? := by
      have hOffset : before (lanes 0) + stride + stride * i =
          before (lanes 0) + stride * (i + 1) := by rw [Nat.mul_succ]; omega
      rw [hNextPos, hOffset]
      exact hRead (i + 1) (by simpa using hi)
    obtain ⟨tailTicks, hTailTicks, after, hTail, hZero, hPos, hResult, hFrame⟩ :=
      ih advanced hNextCount hNextIndex hNextScratch hNextCap hTailBit
    refine ⟨1 + bodyTicks + tailTicks, ?_, after, ?_, hZero, ?_, ?_, ?_⟩
    · rw [stridedFieldCost, List.length_cons, Nat.succ_mul]
      unfold stridedFieldCost at hTailTicks
      omega
    · intro output
      let start := (stridedField stride lanes).enter (⟨none, before, none, output⟩ : Config R Unit)
      have hPositive : 0 < before (lanes 1) := by rw [hCount]; simp
      have hStep := run_countdown_iteration (counter := lanes 1) (cfg := start)
        rfl hPositive (hBody output) rfl
      let mid := (stridedField stride lanes).enter (⟨none, advanced, none, output⟩ : Config R Unit)
      change RegisterMachine.run (stridedField stride lanes).close x (1 + bodyTicks) start =
        some mid at hStep
      change RegisterMachine.run (stridedField stride lanes).close x _ start = _
      rw [RegisterMachine.run_add, hStep, Option.bind_some]
      exact hTail output
    · rw [hPos, hNextPos, List.length_cons, Nat.mul_succ]
      omega
    · rw [hResult, hNextAcc, List.foldl_cons]
    · intro r hp hc ha
      rw [hFrame r hp hc ha]
      simp [advanced, stridedIterationValues, tested, decrementValues, setValue, hp, hc, ha]

/-- Decode a little-endian word from its specified reverse-input reads. -/
theorem runsValues_stridedField_of_reads (stride : Nat) (lanes : Fin 5 → R)
    (hLanes : Function.Injective lanes) (x bits : BinaryWord) (cap : Nat) (before : R → Nat)
    (hWidth : before (lanes 1) = bits.length) (hAccumulator : before (lanes 2) = 0)
    (hIndex : before (lanes 3) = 0) (hScratch : before (lanes 4) = 0)
    (hCap : fieldValue bits ≤ cap)
    (hRead : ∀ i, i < bits.length →
      x.reverse[before (lanes 0) + stride * i]? = bits.reverse[i]?) :
    ∃ ticks ≤ stridedFieldCost stride x.length bits.length cap, ∃ after : R → Nat,
      (stridedField stride lanes).RunsValues x ticks before after ∧ after (lanes 1) = 0 ∧
      after (lanes 0) = before (lanes 0) + stride * bits.length ∧
      after (lanes 2) = fieldValue bits ∧
      ∀ r, r ≠ lanes 0 → r ≠ lanes 1 → r ≠ lanes 2 → after r = before r := by
  have hValue : bits.reverse.foldl pushBit (before (lanes 2)) = fieldValue bits := by
    rw [hAccumulator, foldl_reverse_pushBit_zero]
  simpa only [List.length_reverse, hValue] using
    runsValues_stridedField_word stride lanes hLanes x bits.reverse cap before
      (by simpa only [List.length_reverse] using hWidth) hIndex hScratch
      (hValue.symm ▸ hCap) (fun i hi ↦ hRead i (by simpa only [List.length_reverse] using hi))

/-- Decode from the supplied first reverse-input position. -/
theorem runsValues_stridedField_reverse (stride : Nat) (lanes : Fin 5 → R)
    (hLanes : Function.Injective lanes) (x : BinaryWord) (start width cap : Nat) (before : R → Nat)
    (hRange : ∀ i, i < width → start + stride * i < x.length) (hStart : before (lanes 0) = start)
    (hWidth : before (lanes 1) = width) (hAccumulator : before (lanes 2) = 0)
    (hIndex : before (lanes 3) = 0) (hScratch : before (lanes 4) = 0)
    (hCap : fieldValue (stridedBits x.reverse start stride width).reverse ≤ cap) :
    ∃ ticks ≤ stridedFieldCost stride x.length width cap, ∃ after : R → Nat,
      (stridedField stride lanes).RunsValues x ticks before after ∧ after (lanes 1) = 0 ∧
      after (lanes 0) = before (lanes 0) + stride * width ∧
      after (lanes 2) = fieldValue (stridedBits x.reverse start stride width).reverse ∧
      ∀ r, r ≠ lanes 0 → r ≠ lanes 1 → r ≠ lanes 2 → after r = before r := by
  let bits := (stridedBits x.reverse start stride width).reverse
  have hLength : bits.length = width := by simp [bits]
  have hRead (i : Nat) (hi : i < bits.length) :
      x.reverse[before (lanes 0) + stride * i]? = bits.reverse[i]? := by
    have hi' := hLength ▸ hi
    have hPosition : start + stride * i < x.reverse.length := by
      simpa only [List.length_reverse] using hRange i hi'
    rw [hStart]
    simpa only [bits, List.reverse_reverse] using
      (getElem?_stridedBits x.reverse start stride width i hi' hPosition).symm
  simpa only [hLength, bits] using
    runsValues_stridedField_of_reads stride lanes hLanes x bits cap before
      (hWidth.trans hLength.symm) hAccumulator hIndex hScratch hCap hRead

/-- Decode an in-range little-endian field at positions `start + stride * i`.
The prepared reverse position is the location of its most significant digit. -/
theorem runsValues_stridedField (stride : Nat) (lanes : Fin 5 → R)
    (hLanes : Function.Injective lanes) (x : BinaryWord) (start width cap : Nat) (before : R → Nat)
    (hRange : ∀ i, i < width → start + stride * i < x.length)
    (hStart : before (lanes 0) = x.length - 1 - (start + stride * (width - 1)))
    (hWidth : before (lanes 1) = width) (hAccumulator : before (lanes 2) = 0)
    (hIndex : before (lanes 3) = 0) (hScratch : before (lanes 4) = 0)
    (hCap : fieldValue (stridedBits x start stride width) ≤ cap) :
    ∃ ticks ≤ stridedFieldCost stride x.length width cap, ∃ after : R → Nat,
      (stridedField stride lanes).RunsValues x ticks before after ∧ after (lanes 1) = 0 ∧
      after (lanes 0) = before (lanes 0) + stride * width ∧
      after (lanes 2) = fieldValue (stridedBits x start stride width) ∧
      ∀ r, r ≠ lanes 0 → r ≠ lanes 1 → r ≠ lanes 2 → after r = before r := by
  let bits := stridedBits x start stride width
  have hLength : bits.length = width := length_stridedBits ..
  have hRead (i : Nat) (hi : i < bits.length) :
      x.reverse[before (lanes 0) + stride * i]? = bits.reverse[i]? := by
    let j := width - 1 - i
    have hi' := hLength ▸ hi
    have hj : j < width := by omega
    have hPair : i + j + 1 = bits.length := by omega
    have hSum : i + j = width - 1 := by omega
    have hMul : stride * i + stride * j = stride * (width - 1) := by
      rw [← Nat.mul_add, hSum]
    have hPosition := hRange j hj
    have hLast := hRange (width - 1) (by omega)
    have hRaw : before (lanes 0) + stride * i + (start + stride * j) + 1 = x.length := by
      rw [hStart]
      omega
    rw [List.getElem?_reverse' hPair, List.getElem?_reverse' hRaw]
    exact (getElem?_stridedBits x start stride width j hj hPosition).symm
  simpa only [hLength, bits] using
    runsValues_stridedField_of_reads stride lanes hLanes x bits cap before
      (hWidth.trans hLength.symm) hAccumulator hIndex hScratch hCap hRead

/-- Circuit description fields have a linear unary value cap for every bit pattern. -/
theorem runsValues_stridedField_circuit (stride : Nat) (lanes : Fin 5 → R)
    (hLanes : Function.Injective lanes) (x : BinaryWord) (n s start : Nat) (before : R → Nat)
    (hRange : ∀ i, i < circuitFieldWidth n s → start + stride * i < x.length)
    (hStart : before (lanes 0) = x.length - 1 - (start + stride * (circuitFieldWidth n s - 1)))
    (hWidth : before (lanes 1) = circuitFieldWidth n s) (hAccumulator : before (lanes 2) = 0)
    (hIndex : before (lanes 3) = 0) (hScratch : before (lanes 4) = 0) :
    ∃ ticks ≤ stridedFieldCost stride x.length (circuitFieldWidth n s) (2 * (n + s + 1)),
      ∃ after : R → Nat,
        (stridedField stride lanes).RunsValues x ticks before after ∧ after (lanes 1) = 0 ∧
        after (lanes 0) = before (lanes 0) + stride * circuitFieldWidth n s ∧
        after (lanes 2) = fieldValue (stridedBits x start stride (circuitFieldWidth n s)) ∧
        ∀ r, r ≠ lanes 0 → r ≠ lanes 1 → r ≠ lanes 2 → after r = before r :=
  runsValues_stridedField stride lanes hLanes x start (circuitFieldWidth n s)
    (2 * (n + s + 1)) before hRange hStart hWidth hAccumulator hIndex hScratch
    (fieldValue_le_circuitFieldWidth_cap n s _ (length_stridedBits ..))

end PvsNP.RegisterMachine.Fragment
