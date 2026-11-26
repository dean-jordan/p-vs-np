module

public import PvsNP.TuringMachine.Registers.Affine
public import PvsNP.TuringMachine.Registers.BinaryCompare
public import PvsNP.TuringMachine.Registers.Subtract

/-! # Arithmetic for the prepared windows of a padded circuit description -/

public section

namespace PvsNP.MCSP

open RegisterMachine RegisterMachine.Fragment

inductive DescriptionOffsetLane where
  | arity | count | width | span | paddedLength
  | codeLength | paddingWidth | wires | outputOffset | gateOffset | paddingOffset | destination
  | multiplier | work | scratch
  deriving DecidableEq

@[expose] def descriptionOffsetInputLanes : List DescriptionOffsetLane :=
  [.arity, .count, .width, .span, .paddedLength]

private abbrev copyTime (source : Nat) : Nat := 5 * source + 2
private abbrev productTime (count span : Nat) : Nat := count * (5 * span + 3) + 1

variable {R : Type}

private def copyPredecessor (source target scratch : R) : Fragment R :=
  (add source target scratch).seq (decrementLane target)

private def offsetCodeLength (lanes : DescriptionOffsetLane → R) : Fragment R :=
  ((accumulateAffine (lanes .width) (lanes .codeLength) (lanes .multiplier)
    (lanes .scratch) 2 0).seq (add (lanes .count) (lanes .multiplier) (lanes .scratch))).seq
    (multiply (lanes .multiplier) (lanes .span) (lanes .codeLength) (lanes .scratch))

private def offsetGateStart (lanes : DescriptionOffsetLane → R) : Fragment R :=
  (((copyPredecessor (lanes .span) (lanes .gateOffset) (lanes .scratch)).seq
    (add (lanes .width) (lanes .gateOffset) (lanes .scratch))).seq
      (copyPredecessor (lanes .count) (lanes .multiplier) (lanes .scratch))).seq
        (multiply (lanes .multiplier) (lanes .span) (lanes .gateOffset) (lanes .scratch))

/-- Calculate logical offsets before the separate conversion to reverse addresses. -/
def descriptionOffsetRegister (lanes : DescriptionOffsetLane → R) : Fragment R :=
  let code := offsetCodeLength lanes
  let padding := (add (lanes .paddedLength) (lanes .paddingWidth) (lanes .scratch)).seq
    (subtract (lanes .codeLength) (lanes .paddingWidth) (lanes .work) (lanes .scratch))
  let wires := (add (lanes .arity) (lanes .wires) (lanes .scratch)).seq
    (add (lanes .count) (lanes .wires) (lanes .scratch))
  let output := copyPredecessor (lanes .codeLength) (lanes .outputOffset) (lanes .scratch)
  let gate := offsetGateStart lanes
  let paddingStart := (copyPredecessor (lanes .paddingWidth) (lanes .paddingOffset)
    (lanes .scratch)).seq (add (lanes .codeLength) (lanes .paddingOffset) (lanes .scratch))
  let destination := copyPredecessor (lanes .wires) (lanes .destination) (lanes .scratch)
  ((((((code.seq padding).seq wires).seq output).seq gate).seq paddingStart).seq destination)

def descriptionOffsetRegisterCost (arity count width span paddedLength : Nat) : Nat :=
  let codeLength := 2 * width + count * span
  let paddingWidth := paddedLength - codeLength
  (affineTime 2 0 width + copyTime count + productTime count span) +
    (copyTime paddedLength + (7 * codeLength + 3)) +
    (copyTime arity + copyTime count) + (copyTime codeLength + 1) +
    (copyTime span + 1 + copyTime width + (copyTime count + 1) + productTime (count - 1) span) +
    (copyTime paddingWidth + 1 + copyTime codeLength) + (copyTime (arity + count) + 1)

theorem descriptionOffsetRegisterCost_polynomiallyBounded
    {arity count width span paddedLength : Nat → Nat}
    (hArity : PolynomiallyBounded arity) (hCount : PolynomiallyBounded count)
    (hWidth : PolynomiallyBounded width) (hSpan : PolynomiallyBounded span)
    (hPadded : PolynomiallyBounded paddedLength) :
    PolynomiallyBounded (fun n ↦
      descriptionOffsetRegisterCost (arity n) (count n) (width n) (span n) (paddedLength n)) := by
  let lit := PolynomiallyBounded.const
  have copy {f : Nat → Nat} (hf : PolynomiallyBounded f) :
      PolynomiallyBounded (fun n ↦ copyTime (f n)) := ((lit 5).mul hf).add (lit 2)
  have product {f : Nat → Nat} (hf : PolynomiallyBounded f) :
      PolynomiallyBounded (fun n ↦ productTime (f n) (span n)) :=
    (hf.mul (((lit 5).mul hSpan).add (lit 3))).add (lit 1)
  have hCode := ((lit 2).mul hWidth).add (hCount.mul hSpan)
  have hPadding := hPadded.mono (fun n ↦ Nat.sub_le (paddedLength n)
    (2 * width n + count n * span n))
  have hPred := hCount.mono (fun n ↦ Nat.sub_le (count n) 1)
  have h1 := ((affineTime_polynomiallyBounded 2 0 hWidth).add (copy hCount)).add (product hCount)
  have h2 := (copy hPadded).add (((lit 7).mul hCode).add (lit 3))
  have h3 := (copy hArity).add (copy hCount)
  have h4 := (copy hCode).add (lit 1)
  have h5 := ((((copy hSpan).add (lit 1)).add (copy hWidth)).add
    ((copy hCount).add (lit 1))).add (product hPred)
  have h6 := ((copy hPadding).add (lit 1)).add (copy hCode)
  have h7 := (copy (hArity.add hCount)).add (lit 1)
  exact (((((h1.add h2).add h3).add h4).add h5).add h6).add h7

/-- The arithmetic preserves all lanes except the seven listed destinations. -/
structure DescriptionOffsetRegisterResult (lanes : DescriptionOffsetLane → R)
    (before after : R → Nat) : Prop where
  codeLength : after (lanes .codeLength) =
    2 * before (lanes .width) + before (lanes .count) * before (lanes .span)
  paddingWidth : after (lanes .paddingWidth) =
    before (lanes .paddedLength) - after (lanes .codeLength)
  wires : after (lanes .wires) = before (lanes .arity) + before (lanes .count)
  outputOffset : after (lanes .outputOffset) = after (lanes .codeLength) - 1
  gateOffset : after (lanes .gateOffset) = before (lanes .width) +
    (before (lanes .count) - 1) * before (lanes .span) + (before (lanes .span) - 1)
  paddingOffset : after (lanes .paddingOffset) = after (lanes .codeLength) +
    (after (lanes .paddingWidth) - 1)
  destination : after (lanes .destination) = after (lanes .wires) - 1
  frame : ∀ r, r ≠ lanes .codeLength → r ≠ lanes .paddingWidth → r ≠ lanes .wires →
    r ≠ lanes .outputOffset → r ≠ lanes .gateOffset → r ≠ lanes .paddingOffset →
    r ≠ lanes .destination → after r = before r

variable [DecidableEq R]

private theorem runsValues_copyPredecessor (source target scratch : R) (x : BinaryWord)
    (v : R → Nat) (hST : source ≠ target) (hSS : source ≠ scratch) (hTS : target ≠ scratch)
    (hTarget : v target = 0) (hScratch : v scratch = 0) :
    (copyPredecessor source target scratch).RunsValues x (copyTime (v source) + 1) v
      (setValue target (v source - 1) v) := by
  let copied := setValue target (v source) v
  have hCopy := runsValues_add source target scratch x v hST hSS hTS hScratch
  rw [hTarget, Nat.zero_add] at hCopy
  have hDec := runsValues_decrementLane target x copied
  have hValues : decrementValues target copied = setValue target (v source - 1) v := by
    funext r
    by_cases hr : r = target <;> simp [decrementValues, setValue, copied, hr]
  exact hValues ▸ hCopy.seq hDec

private theorem runsValues_offsetProduct (lanes : DescriptionOffsetLane → R)
    (hLanes : Function.Injective lanes) (target : DescriptionOffsetLane)
    (hM : target ≠ .multiplier) (hP : target ≠ .span) (hS : target ≠ .scratch)
    (x : BinaryWord) (v : R → Nat) (amount : Nat)
    (hMultiplier : v (lanes .multiplier) = 0) (hScratch : v (lanes .scratch) = 0) :
    (multiply (lanes .multiplier) (lanes .span) (lanes target) (lanes .scratch)).RunsValues x
      (productTime amount (v (lanes .span))) (setValue (lanes .multiplier) amount v)
      (setValue (lanes target) (v (lanes target) + amount * v (lanes .span)) v) := by
  have hNe {a b : DescriptionOffsetLane} (h : a ≠ b) : lanes a ≠ lanes b := fun e ↦ h (hLanes e)
  let loaded := setValue (lanes .multiplier) amount v
  have hWork : loaded (lanes .scratch) = 0 := (setValue_other (hNe (by decide)) ..).trans hScratch
  have hSpan : loaded (lanes .span) = v (lanes .span) := setValue_other (hNe (by decide)) ..
  have hTarget : loaded (lanes target) = v (lanes target) := setValue_other (hNe hM) ..
  have hRestored : setValue (lanes .multiplier) 0 loaded = v := by
    dsimp only [loaded]
    rw [setValue_replace, ← hMultiplier, setValue_current]
  have hRun := runsValues_multiply (lanes .multiplier) (lanes .span) (lanes target)
    (lanes .scratch) x loaded (hNe (by decide)) (hNe hM.symm) (hNe (by decide))
      (hNe hP.symm) (hNe (by decide)) (hNe hS) hWork
  simpa only [show loaded (lanes .multiplier) = amount from setValue_same ..,
    hSpan, hTarget, hRestored] using hRun

private theorem runsValues_offsetCodeLength (lanes : DescriptionOffsetLane → R)
    (hLanes : Function.Injective lanes) (x : BinaryWord) (v : R → Nat)
    (hLength : v (lanes .codeLength) = 0) (hMultiplier : v (lanes .multiplier) = 0)
    (hScratch : v (lanes .scratch) = 0) :
    let width := v (lanes .width)
    let count := v (lanes .count)
    let span := v (lanes .span)
    (offsetCodeLength lanes).RunsValues x
      (affineTime 2 0 width + copyTime count + productTime count span) v
      (setValue (lanes .codeLength) (2 * width + count * span) v) := by
  have hNe {a b : DescriptionOffsetLane} (h : a ≠ b) : lanes a ≠ lanes b := fun e ↦ h (hLanes e)
  let width := v (lanes .width)
  let count := v (lanes .count)
  let span := v (lanes .span)
  let headed := setValue (lanes .codeLength) (2 * width) v
  have hDistinct : [lanes .width, lanes .codeLength, lanes .multiplier, lanes .scratch].Nodup :=
    ((by decide : ([.width, .codeLength, .multiplier, .scratch] :
      List DescriptionOffsetLane).Nodup)).map hLanes
  have hHeader : (accumulateAffine (lanes .width) (lanes .codeLength) (lanes .multiplier)
      (lanes .scratch) 2 0).RunsValues x (affineTime 2 0 width) v headed := by
    simpa only [headed, width, hLength, Nat.zero_add, Nat.add_zero] using
      runsValues_accumulateAffine (lanes .width) (lanes .codeLength) (lanes .multiplier)
        (lanes .scratch) 2 0 x v hDistinct hMultiplier hScratch
  have hHeadMultiplier : headed (lanes .multiplier) = 0 :=
    (setValue_other (hNe (by decide)) ..).trans hMultiplier
  have hHeadScratch : headed (lanes .scratch) = 0 :=
    (setValue_other (hNe (by decide)) ..).trans hScratch
  have hCount : headed (lanes .count) = count := setValue_other (hNe (by decide)) ..
  have hSpan : headed (lanes .span) = span := setValue_other (hNe (by decide)) ..
  have hHead : headed (lanes .codeLength) = 2 * width := setValue_same ..
  have hLoad : (add (lanes .count) (lanes .multiplier) (lanes .scratch)).RunsValues x
      (copyTime count) headed (setValue (lanes .multiplier) count headed) := by
    simpa only [hCount, hHeadMultiplier, Nat.zero_add] using
      runsValues_add (lanes .count) (lanes .multiplier) (lanes .scratch) x headed
        (hNe (by decide)) (hNe (by decide)) (hNe (by decide)) hHeadScratch
  have hMultiply := runsValues_offsetProduct lanes hLanes .codeLength (by decide) (by decide)
    (by decide) x headed count hHeadMultiplier hHeadScratch
  rw [hSpan, hHead] at hMultiply
  simpa only [offsetCodeLength, headed, setValue_replace] using (hHeader.seq hLoad).seq hMultiply

private theorem runsValues_offsetGateStart (lanes : DescriptionOffsetLane → R)
    (hLanes : Function.Injective lanes) (x : BinaryWord) (v : R → Nat)
    (hOffset : v (lanes .gateOffset) = 0) (hMultiplier : v (lanes .multiplier) = 0)
    (hScratch : v (lanes .scratch) = 0) :
    let width := v (lanes .width)
    let count := v (lanes .count)
    let span := v (lanes .span)
    (offsetGateStart lanes).RunsValues x
      (copyTime span + 1 + copyTime width + (copyTime count + 1) + productTime (count - 1) span) v
      (setValue (lanes .gateOffset) (span - 1 + width + (count - 1) * span) v) := by
  have hNe {a b : DescriptionOffsetLane} (h : a ≠ b) : lanes a ≠ lanes b := fun e ↦ h (hLanes e)
  let width := v (lanes .width)
  let count := v (lanes .count)
  let span := v (lanes .span)
  let pred := setValue (lanes .gateOffset) (span - 1) v
  let headed := setValue (lanes .gateOffset) (span - 1 + width) v
  have hPred := runsValues_copyPredecessor (lanes .span) (lanes .gateOffset) (lanes .scratch)
    x v (hNe (by decide)) (hNe (by decide)) (hNe (by decide)) hOffset hScratch
  have hPredScratch : pred (lanes .scratch) = 0 :=
    (setValue_other (hNe (by decide)) ..).trans hScratch
  have hPredWidth : pred (lanes .width) = width := setValue_other (hNe (by decide)) ..
  have hHead : (add (lanes .width) (lanes .gateOffset) (lanes .scratch)).RunsValues x
      (copyTime width) pred headed := by
    simpa only [hPredWidth, show pred (lanes .gateOffset) = span - 1 from setValue_same ..,
      pred, headed, setValue_replace] using
      runsValues_add (lanes .width) (lanes .gateOffset) (lanes .scratch) x pred
        (hNe (by decide)) (hNe (by decide)) (hNe (by decide)) hPredScratch
  have hHeadMultiplier : headed (lanes .multiplier) = 0 :=
    (setValue_other (hNe (by decide)) ..).trans hMultiplier
  have hHeadScratch : headed (lanes .scratch) = 0 :=
    (setValue_other (hNe (by decide)) ..).trans hScratch
  have hCount : headed (lanes .count) = count := setValue_other (hNe (by decide)) ..
  have hSpan : headed (lanes .span) = span := setValue_other (hNe (by decide)) ..
  have hLoad := runsValues_copyPredecessor (lanes .count) (lanes .multiplier) (lanes .scratch)
    x headed (hNe (by decide)) (hNe (by decide)) (hNe (by decide)) hHeadMultiplier hHeadScratch
  rw [hCount] at hLoad
  have hMultiply := runsValues_offsetProduct lanes hLanes .gateOffset (by decide) (by decide)
    (by decide) x headed (count - 1) hHeadMultiplier hHeadScratch
  rw [hSpan, show headed (lanes .gateOffset) = span - 1 + width from setValue_same ..]
    at hMultiply
  simpa only [offsetGateStart, headed, setValue_replace] using
    ((hPred.seq hHead).seq hLoad).seq hMultiply

/-- The arithmetic touches no input bits and works at every natural-valued seed.
Only the named inputs may be nonzero initially. The work lanes are restored. -/
theorem runsValues_descriptionOffsetRegister (lanes : DescriptionOffsetLane → R)
    (hLanes : Function.Injective lanes) (x : BinaryWord) (before : R → Nat)
    (hZero : ∀ lane, lane ∉ descriptionOffsetInputLanes → before (lanes lane) = 0) :
    ∃ after : R → Nat, (descriptionOffsetRegister lanes).RunsValues x
      (descriptionOffsetRegisterCost (before (lanes .arity)) (before (lanes .count))
        (before (lanes .width)) (before (lanes .span)) (before (lanes .paddedLength)))
      before after ∧
      DescriptionOffsetRegisterResult lanes before after := by
  have hNe {a b : DescriptionOffsetLane} (h : a ≠ b) : lanes a ≠ lanes b := fun e ↦ h (hLanes e)
  have hLane (a b : DescriptionOffsetLane) : lanes a = lanes b ↔ a = b :=
    ⟨fun h ↦ hLanes h, congrArg lanes⟩
  let arity := before (lanes .arity)
  let count := before (lanes .count)
  let width := before (lanes .width)
  let span := before (lanes .span)
  let padded := before (lanes .paddedLength)
  let codeLength := 2 * width + count * span
  let paddingWidth := padded - codeLength
  let wireCount := arity + count
  have scratch := hZero .scratch (by decide)
  let withCode := setValue (lanes .codeLength) codeLength before
  have hCode := runsValues_offsetCodeLength lanes hLanes x before
    (hZero .codeLength (by decide)) (hZero .multiplier (by decide)) scratch
  have hCodeKeep {r : DescriptionOffsetLane} (hr : r ≠ .codeLength) :
      withCode (lanes r) = before (lanes r) := setValue_other (hNe hr) ..
  let paddingSeed := setValue (lanes .paddingWidth) padded withCode
  let withPadding := setValue (lanes .paddingWidth) paddingWidth withCode
  have hPadSeed : (add (lanes .paddedLength) (lanes .paddingWidth) (lanes .scratch)).RunsValues x
      (copyTime padded) withCode paddingSeed := by
    have hPadZero := (hCodeKeep (r := .paddingWidth) (by decide)).trans
      (hZero .paddingWidth (by decide))
    simpa only [hPadZero, hCodeKeep (r := .paddedLength) (by decide), Nat.zero_add, paddingSeed,
      padded] using runsValues_add (lanes .paddedLength) (lanes .paddingWidth) (lanes .scratch)
        x withCode (hNe (by decide)) (hNe (by decide)) (hNe (by decide))
          ((hCodeKeep (by decide)).trans scratch)
  have hPadRest : (subtract (lanes .codeLength) (lanes .paddingWidth) (lanes .work)
      (lanes .scratch)).RunsValues x (7 * codeLength + 3) paddingSeed withPadding := by
    have hWork : paddingSeed (lanes .work) = 0 := by
      simp [paddingSeed, withCode, setValue, hLane, hZero .work (by decide)]
    have hScratch : paddingSeed (lanes .scratch) = 0 := by
      simp [paddingSeed, withCode, setValue, hLane, scratch]
    have hLength : paddingSeed (lanes .codeLength) = codeLength := by
      simp [paddingSeed, withCode, setValue, hLane]
    have hPadded : paddingSeed (lanes .paddingWidth) = padded := setValue_same ..
    simpa only [hLength, hPadded, paddingSeed, withPadding, paddingWidth, setValue_replace] using
      runsValues_subtract (lanes .codeLength) (lanes .paddingWidth) (lanes .work)
        (lanes .scratch) x paddingSeed (hNe (by decide)) (hNe (by decide)) (hNe (by decide))
        (hNe (by decide)) hWork hScratch
  have hPaddingKeep {r : DescriptionOffsetLane} (hc : r ≠ .codeLength) (hp : r ≠ .paddingWidth) :
      withPadding (lanes r) = before (lanes r) :=
    (setValue_other (hNe hp) ..).trans (hCodeKeep hc)
  let aritySeed := setValue (lanes .wires) arity withPadding
  let withWires := setValue (lanes .wires) wireCount withPadding
  have hArity : (add (lanes .arity) (lanes .wires) (lanes .scratch)).RunsValues x
      (copyTime arity) withPadding aritySeed := by
    have hWiresZero := (hPaddingKeep (r := .wires) (by decide) (by decide)).trans
      (hZero .wires (by decide))
    simpa only [hWiresZero, hPaddingKeep (r := .arity) (by decide) (by decide),
      Nat.zero_add, aritySeed, arity] using
      runsValues_add (lanes .arity) (lanes .wires) (lanes .scratch) x withPadding
        (hNe (by decide)) (hNe (by decide)) (hNe (by decide))
        ((hPaddingKeep (by decide) (by decide)).trans scratch)
  have hWireSum : (add (lanes .count) (lanes .wires) (lanes .scratch)).RunsValues x
      (copyTime count) aritySeed withWires := by
    have hCount : aritySeed (lanes .count) = count := by
      simp [aritySeed, withPadding, withCode, setValue, hLane, count]
    have hScratch : aritySeed (lanes .scratch) = 0 := by
      simp [aritySeed, withPadding, withCode, setValue, hLane, scratch]
    have hAritySeed : aritySeed (lanes .wires) = arity := setValue_same ..
    simpa only [hCount, hAritySeed, aritySeed, withWires, wireCount, setValue_replace] using
      runsValues_add (lanes .count) (lanes .wires) (lanes .scratch) x aritySeed
        (hNe (by decide)) (hNe (by decide)) (hNe (by decide)) hScratch
  let withOutput := setValue (lanes .outputOffset) (codeLength - 1) withWires
  have hOutput : RunsValues (copyPredecessor (lanes .codeLength) (lanes .outputOffset)
      (lanes .scratch)) x (copyTime codeLength + 1) withWires withOutput := by
    have hLen : withWires (lanes .codeLength) = codeLength := by
      simp [withWires, withPadding, withCode, setValue, hLane]
    have hOffset : withWires (lanes .outputOffset) = 0 := by
      simp [withWires, withPadding, withCode, setValue, hLane, hZero .outputOffset (by decide)]
    have hScratch : withWires (lanes .scratch) = 0 := by
      simp [withWires, withPadding, withCode, setValue, hLane, scratch]
    simpa only [hLen, withOutput] using runsValues_copyPredecessor (lanes .codeLength)
      (lanes .outputOffset) (lanes .scratch) x withWires (hNe (by decide)) (hNe (by decide))
        (hNe (by decide)) hOffset hScratch
  let withGate := setValue (lanes .gateOffset) (span - 1 + width + (count - 1) * span) withOutput
  have hGateZero : withOutput (lanes .gateOffset) = 0 := by
    simp [withOutput, withWires, withPadding, withCode, setValue, hLane,
      hZero .gateOffset (by decide)]
  have hGateMult : withOutput (lanes .multiplier) = 0 := by
    simp [withOutput, withWires, withPadding, withCode, setValue, hLane,
      hZero .multiplier (by decide)]
  have hGateScratch : withOutput (lanes .scratch) = 0 := by
    simp [withOutput, withWires, withPadding, withCode, setValue, hLane, scratch]
  have hWidth : withOutput (lanes .width) = width := by
    simp [withOutput, withWires, withPadding, withCode, setValue, hLane, width]
  have hCount : withOutput (lanes .count) = count := by
    simp [withOutput, withWires, withPadding, withCode, setValue, hLane, count]
  have hSpan : withOutput (lanes .span) = span := by
    simp [withOutput, withWires, withPadding, withCode, setValue, hLane, span]
  have hGate :=
    runsValues_offsetGateStart lanes hLanes x withOutput hGateZero hGateMult hGateScratch
  dsimp only at hGate
  rw [hWidth, hCount, hSpan] at hGate
  let paddingStartSeed := setValue (lanes .paddingOffset) (paddingWidth - 1) withGate
  let withPaddingStart := setValue (lanes .paddingOffset) (paddingWidth - 1 + codeLength) withGate
  have hPadPred : RunsValues (copyPredecessor (lanes .paddingWidth) (lanes .paddingOffset)
      (lanes .scratch)) x (copyTime paddingWidth + 1) withGate paddingStartSeed := by
    have hPadWidth : withGate (lanes .paddingWidth) = paddingWidth := by
      simp [withGate, withOutput, withWires, withPadding, setValue, hLane]
    have hPadOffset : withGate (lanes .paddingOffset) = 0 := by
      simp [withGate, withOutput, withWires, withPadding, withCode, setValue, hLane,
        hZero .paddingOffset (by decide)]
    have hScratch : withGate (lanes .scratch) = 0 := by
      simp [withGate, withOutput, withWires, withPadding, withCode, setValue, hLane, scratch]
    simpa only [hPadWidth, paddingStartSeed] using runsValues_copyPredecessor (lanes .paddingWidth)
      (lanes .paddingOffset) (lanes .scratch) x withGate (hNe (by decide)) (hNe (by decide))
        (hNe (by decide)) hPadOffset hScratch
  have hPadStart : (add (lanes .codeLength) (lanes .paddingOffset) (lanes .scratch)).RunsValues x
      (copyTime codeLength) paddingStartSeed withPaddingStart := by
    have hLen : paddingStartSeed (lanes .codeLength) = codeLength := by
      simp [paddingStartSeed, withGate, withOutput, withWires, withPadding, withCode,
        setValue, hLane]
    have hStart : paddingStartSeed (lanes .paddingOffset) = paddingWidth - 1 := setValue_same ..
    have hScratch : paddingStartSeed (lanes .scratch) = 0 := by
      simp [paddingStartSeed, withGate, withOutput, withWires, withPadding, withCode, setValue,
        hLane, scratch]
    simpa only [hLen, hStart, paddingStartSeed, withPaddingStart, setValue_replace] using
      runsValues_add (lanes .codeLength) (lanes .paddingOffset) (lanes .scratch) x paddingStartSeed
        (hNe (by decide)) (hNe (by decide)) (hNe (by decide)) hScratch
  let after := setValue (lanes .destination) (wireCount - 1) withPaddingStart
  have hDestination : RunsValues (copyPredecessor (lanes .wires) (lanes .destination)
      (lanes .scratch)) x (copyTime wireCount + 1) withPaddingStart after := by
    have hWireCount : withPaddingStart (lanes .wires) = wireCount := by
      simp [withPaddingStart, withGate, withOutput, withWires, setValue, hLane]
    have hDest : withPaddingStart (lanes .destination) = 0 := by
      simp [withPaddingStart, withGate, withOutput, withWires, withPadding, withCode,
        setValue, hLane, hZero .destination (by decide)]
    have hScratch : withPaddingStart (lanes .scratch) = 0 := by
      simp [withPaddingStart, withGate, withOutput, withWires, withPadding, withCode,
        setValue, hLane, scratch]
    simpa only [hWireCount, after] using runsValues_copyPredecessor (lanes .wires)
      (lanes .destination) (lanes .scratch) x withPaddingStart (hNe (by decide)) (hNe (by decide))
        (hNe (by decide)) hDest hScratch
  have hRun := (((((hCode.seq (hPadSeed.seq hPadRest)).seq (hArity.seq hWireSum)).seq hOutput).seq
    hGate).seq (hPadPred.seq hPadStart)).seq hDestination
  refine ⟨after, hRun, ?_⟩
  have hFrame (r : R) (hc : r ≠ lanes .codeLength) (hp : r ≠ lanes .paddingWidth)
      (hw : r ≠ lanes .wires) (ho : r ≠ lanes .outputOffset) (hg : r ≠ lanes .gateOffset)
      (hs : r ≠ lanes .paddingOffset) (hd : r ≠ lanes .destination) : after r = before r := by
    simp only [after, withPaddingStart, withGate, withOutput, withWires, withPadding, withCode,
      setValue_other hc, setValue_other hp, setValue_other hw, setValue_other ho,
      setValue_other hg, setValue_other hs, setValue_other hd]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hFrame⟩ <;>
    simp [after, withPaddingStart, withGate, withOutput, withWires, withPadding, withCode, setValue,
      hLane, codeLength, paddingWidth, wireCount, arity, count, width, span, padded] <;> omega

end PvsNP.MCSP
