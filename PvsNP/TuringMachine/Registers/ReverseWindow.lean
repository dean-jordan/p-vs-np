module

public import PvsNP.Complexity.PackedOffsets
public import PvsNP.TuringMachine.Registers.Affine
public import PvsNP.TuringMachine.Registers.BinaryCompare
public import PvsNP.TuringMachine.Registers.Subtract

/-! # Prepare the reverse offset of a strided window -/

public section

namespace PvsNP.RegisterMachine.Fragment

/-- The three input registers, result register and temporary workspace. -/
inductive ReverseWindowLane where
  | inputLength | base | width | position | widthCopy | address | multiplier | scratch
  deriving DecidableEq

variable {R : Type}

private def reverseCopyDecrement (source target scratch : R) : Fragment R :=
  (add source target scratch).seq (decrementLane target)

private def clearReverseLane (lane : R) : Fragment R where
  Label := Unit
  entry := some ()
  code _ := .dec lane none (some ())

/-- Compute the reverse offset, preserving the input length, base, and width. -/
def reverseWindowRegister (stride : Nat) (lanes : ReverseWindowLane → R) : Fragment R :=
  let length := reverseCopyDecrement (lanes .inputLength) (lanes .position) (lanes .scratch)
  let width := reverseCopyDecrement (lanes .width) (lanes .widthCopy) (lanes .scratch)
  let base := add (lanes .base) (lanes .address) (lanes .scratch)
  let last := accumulateAffine (lanes .widthCopy) (lanes .address)
    (lanes .multiplier) (lanes .scratch) stride 0
  let reverse := subtract (lanes .address) (lanes .position) (lanes .multiplier) (lanes .scratch)
  ((((((length.seq width).seq base).seq last).seq reverse).seq
    (clearReverseLane (lanes .widthCopy))).seq (clearReverseLane (lanes .address)))

/-- A linear instruction bound in the unary inputs at fixed stride. -/
@[expose] def reverseWindowRegisterCost (stride length base width : Nat) : Nat :=
  5 * length + 13 * base + 6 * width + 13 * stride * width + 4 * stride + 14

theorem reverseWindowRegisterCost_polynomiallyBounded (stride : Nat)
    {length base width : Nat → Nat} (hLength : PolynomiallyBounded length)
    (hBase : PolynomiallyBounded base) (hWidth : PolynomiallyBounded width) :
    PolynomiallyBounded (fun n ↦ reverseWindowRegisterCost stride (length n) (base n) (width n)) :=
  ((((((PolynomiallyBounded.const 5).mul hLength).add
    ((PolynomiallyBounded.const 13).mul hBase)).add ((PolynomiallyBounded.const 6).mul hWidth)).add
      ((PolynomiallyBounded.const (13 * stride)).mul hWidth)).add
      (PolynomiallyBounded.const (4 * stride))).add (PolynomiallyBounded.const 14)

variable [DecidableEq R]

private theorem runsValues_reverseCopyDecrement (source target scratch : R) (x : BinaryWord)
    (v : R → Nat) (hST : source ≠ target) (hSS : source ≠ scratch) (hTS : target ≠ scratch)
    (hTarget : v target = 0) (hScratch : v scratch = 0) :
    (reverseCopyDecrement source target scratch).RunsValues x (5 * v source + 3) v
      (setValue target (v source - 1) v) := by
  let copied := setValue target (v source) v
  have hCopy : (add source target scratch).RunsValues x (5 * v source + 2) v copied := by
    simpa only [hTarget, Nat.zero_add, copied] using
      runsValues_add source target scratch x v hST hSS hTS hScratch
  have hDecrement : decrementValues target copied = setValue target (v source - 1) v := by
    funext r
    by_cases hr : r = target <;> simp [copied, decrementValues, setValue, hr]
  simpa only [reverseCopyDecrement, hDecrement,
    show 5 * v source + 2 + 1 = 5 * v source + 3 by omega] using
    hCopy.seq (runsValues_decrementLane target x copied)

private theorem runsValues_clearReverseLane (lane : R) (x : BinaryWord) (v : R → Nat) :
    (clearReverseLane lane).RunsValues x (v lane + 1) v (setValue lane 0 v) := by
  intro output
  exact run_clear x (program := (clearReverseLane lane).close) rfl
    (cfg := (clearReverseLane lane).enter (⟨none, v, none, output⟩ : Config R Unit)) rfl

/-- Run the offset calculation with natural subtraction, including empty and
out-of-range windows. The exact final valuation changes only the result. -/
theorem runsValues_reverseWindowRegister (stride : Nat) (lanes : ReverseWindowLane → R)
    (hLanes : Function.Injective lanes) (x : BinaryWord) (before : R → Nat)
    (hZero : ∀ lane, lane ≠ .inputLength → lane ≠ .base → lane ≠ .width →
      before (lanes lane) = 0) :
    let length := before (lanes .inputLength)
    let base := before (lanes .base)
    let width := before (lanes .width)
    ∃ ticks ≤ reverseWindowRegisterCost stride length base width,
      (reverseWindowRegister stride lanes).RunsValues x ticks before
        (setValue (lanes .position) (reverseWindowStart length base stride width) before) := by
  let length := before (lanes .inputLength)
  let base := before (lanes .base)
  let width := before (lanes .width)
  let last := width - 1
  let address := base + stride * last
  let result := reverseWindowStart length base stride width
  have hNe {a b : ReverseWindowLane} (h : a ≠ b) : lanes a ≠ lanes b := fun e ↦ h (hLanes e)
  have hLane (a b : ReverseWindowLane) : lanes a = lanes b ↔ a = b :=
    ⟨fun e ↦ hLanes e, congrArg lanes⟩
  have hPositionZero := hZero .position (by decide) (by decide) (by decide)
  have hWidthCopyZero := hZero .widthCopy (by decide) (by decide) (by decide)
  have hAddressZero := hZero .address (by decide) (by decide) (by decide)
  have hMultiplierZero := hZero .multiplier (by decide) (by decide) (by decide)
  have hScratchZero := hZero .scratch (by decide) (by decide) (by decide)
  let positioned := setValue (lanes .position) (length - 1) before
  have hPosition : (reverseCopyDecrement (lanes .inputLength) (lanes .position)
      (lanes .scratch)).RunsValues x (5 * length + 3) before positioned :=
    runsValues_reverseCopyDecrement (lanes .inputLength) (lanes .position) (lanes .scratch)
      x before (hNe (by decide)) (hNe (by decide)) (hNe (by decide)) hPositionZero hScratchZero
  have hPositionedWidth : positioned (lanes .width) = width :=
    setValue_other (hNe (by decide)) ..
  have hPositionedCopy : positioned (lanes .widthCopy) = 0 :=
    (setValue_other (hNe (by decide)) ..).trans hWidthCopyZero
  have hPositionedScratch : positioned (lanes .scratch) = 0 :=
    (setValue_other (hNe (by decide)) ..).trans hScratchZero
  let copied := setValue (lanes .widthCopy) last positioned
  have hWidth : (reverseCopyDecrement (lanes .width) (lanes .widthCopy)
      (lanes .scratch)).RunsValues x (5 * width + 3) positioned copied := by
    simpa only [hPositionedWidth, last, copied] using
      runsValues_reverseCopyDecrement (lanes .width) (lanes .widthCopy) (lanes .scratch)
        x positioned (hNe (by decide)) (hNe (by decide)) (hNe (by decide))
        hPositionedCopy hPositionedScratch
  have hCopiedBase : copied (lanes .base) = base := by
    simp [copied, positioned, setValue, hLane, base]
  have hCopiedAddress : copied (lanes .address) = 0 := by
    simp [copied, positioned, setValue, hLane, hAddressZero]
  have hCopiedScratch : copied (lanes .scratch) = 0 :=
    (setValue_other (hNe (by decide)) ..).trans hPositionedScratch
  let based := setValue (lanes .address) base copied
  have hBase : (add (lanes .base) (lanes .address) (lanes .scratch)).RunsValues
      x (5 * base + 2) copied based := by
    simpa only [hCopiedBase, hCopiedAddress, Nat.zero_add, based] using
      runsValues_add (lanes .base) (lanes .address) (lanes .scratch) x copied
        (hNe (by decide)) (hNe (by decide)) (hNe (by decide)) hCopiedScratch
  have hBasedLast : based (lanes .widthCopy) = last := by simp [based, copied, setValue, hLane]
  have hBasedAddress : based (lanes .address) = base := setValue_same ..
  have hBasedMultiplier : based (lanes .multiplier) = 0 := by
    simp [based, copied, positioned, setValue, hLane, hMultiplierZero]
  have hBasedScratch : based (lanes .scratch) = 0 :=
    (setValue_other (hNe (by decide)) ..).trans hCopiedScratch
  have hAffineLanes : [lanes .widthCopy, lanes .address, lanes .multiplier, lanes .scratch].Nodup :=
    ((by decide : ([.widthCopy, .address, .multiplier, .scratch] :
      List ReverseWindowLane).Nodup)).map hLanes
  let addressed := setValue (lanes .address) address copied
  have hAddress : (accumulateAffine (lanes .widthCopy) (lanes .address) (lanes .multiplier)
      (lanes .scratch) stride 0).RunsValues x (affineTime stride 0 last) based addressed := by
    simpa only [hBasedLast, hBasedAddress, Nat.add_zero, based, addressed, address,
      setValue_replace] using runsValues_accumulateAffine (lanes .widthCopy) (lanes .address)
        (lanes .multiplier) (lanes .scratch) stride 0 x based hAffineLanes
        hBasedMultiplier hBasedScratch
  have hAddressedAddress : addressed (lanes .address) = address := setValue_same ..
  have hAddressedPosition : addressed (lanes .position) = length - 1 := by
    simp [addressed, copied, positioned, setValue, hLane]
  have hAddressedMultiplier : addressed (lanes .multiplier) = 0 := by
    simp [addressed, copied, positioned, setValue, hLane, hMultiplierZero]
  have hAddressedScratch : addressed (lanes .scratch) = 0 :=
    (setValue_other (hNe (by decide)) ..).trans hCopiedScratch
  let subtracted := setValue (lanes .position) result addressed
  have hSubtract : (subtract (lanes .address) (lanes .position) (lanes .multiplier)
      (lanes .scratch)).RunsValues x (7 * address + 3) addressed subtracted := by
    simpa only [hAddressedAddress, hAddressedPosition, subtracted, result, address, last,
      reverseWindowStart] using runsValues_subtract (lanes .address) (lanes .position)
        (lanes .multiplier) (lanes .scratch) x addressed (hNe (by decide)) (hNe (by decide))
        (hNe (by decide)) (hNe (by decide)) hAddressedMultiplier hAddressedScratch
  let cleared := setValue (lanes .widthCopy) 0 subtracted
  have hSubtractedCopy : subtracted (lanes .widthCopy) = last := by
    simp [subtracted, addressed, copied, setValue, hLane]
  have hClearWidth : (clearReverseLane (lanes .widthCopy)).RunsValues x (last + 1)
      subtracted cleared := by
    simpa only [hSubtractedCopy, cleared] using runsValues_clearReverseLane (lanes .widthCopy)
      x subtracted
  have hClearedAddress : cleared (lanes .address) = address := by
    simp [cleared, subtracted, addressed, setValue, hLane]
  have hFinal : setValue (lanes .address) 0 cleared = setValue (lanes .position) result before := by
    funext r
    by_cases ha : r = lanes .address
    · subst r
      simp [setValue, hLane, hAddressZero]
    by_cases hw : r = lanes .widthCopy
    · subst r
      simp [cleared, setValue, hLane, hWidthCopyZero]
    by_cases hp : r = lanes .position
    · subst r
      simp [cleared, subtracted, setValue, hLane]
    simp [cleared, subtracted, addressed, copied, positioned, setValue, ha, hw, hp]
  have hClearAddress : (clearReverseLane (lanes .address)).RunsValues x (address + 1)
      cleared (setValue (lanes .position) result before) := by
    simpa only [hClearedAddress, hFinal] using
      runsValues_clearReverseLane (lanes .address) x cleared
  have hRun := (((((hPosition.seq hWidth).seq hBase).seq hAddress).seq hSubtract).seq
    hClearWidth).seq hClearAddress
  refine ⟨_, ?_, hRun⟩
  change _ ≤ reverseWindowRegisterCost stride length base width
  have hLast : last ≤ width := Nat.sub_le ..
  have hScaled := Nat.mul_le_mul_left stride hLast
  unfold reverseWindowRegisterCost affineTime
  dsimp only [address]
  simp only [Nat.mul_add, Nat.mul_left_comm stride 5, Nat.mul_assoc, Nat.add_zero]
  omega

end PvsNP.RegisterMachine.Fragment
