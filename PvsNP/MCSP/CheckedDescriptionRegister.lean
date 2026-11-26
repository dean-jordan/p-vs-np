module

public import PvsNP.MCSP.DescriptionCountRegister
public import PvsNP.MCSP.DescriptionOffsetRegister
public import PvsNP.MCSP.PaddedDescriptionRegister

import all PvsNP.TuringMachine.Registers.ReverseWindow

/-! # Prepare and check a padded description without materializing its fields -/

public section

namespace PvsNP.MCSP

open Circuits RegisterMachine RegisterMachine.Fragment

inductive CheckedDescriptionLane where
  | arity | cap | width | span | paddedLength | inputLength | base | count
  | offset (lane : DescriptionOffsetLane)
  | validation (lane : PaddedDescriptionLane)
  | reverse (lane : ReverseWindowLane)
  | guardLeft | guardRight | guardScratch | failures
  deriving DecidableEq

@[expose] def checkedDescriptionInputLanes : List CheckedDescriptionLane :=
  [.arity, .cap, .width, .span, .paddedLength, .inputLength, .base]

variable {R : Type}

structure CheckedDescriptionSeed (lanes : CheckedDescriptionLane → R) (word : BinaryWord)
    (start arity cap : Nat) (v : R → Nat) : Prop where
  arityValue : v (lanes .arity) = arity
  capValue : v (lanes .cap) = cap
  width : v (lanes .width) = circuitFieldWidth arity cap
  span : v (lanes .span) = 3 + 2 * circuitFieldWidth arity cap
  paddedLength : v (lanes .paddedLength) = mergeWitnessLength arity cap
  inputLength : v (lanes .inputLength) = word.length
  base : v (lanes .base) = start

private def offsetRole : DescriptionOffsetLane → CheckedDescriptionLane
  | .arity => .arity
  | .count => .count
  | .width => .width
  | .span => .span
  | .paddedLength => .paddedLength
  | lane => .offset lane

private theorem offsetRole_injective : Function.Injective offsetRole := by
  intro a b h
  cases a <;> cases b <;> simp_all [offsetRole]

private def positionRole (target : PaddedDescriptionLane) :
    ReverseWindowLane → CheckedDescriptionLane
  | .inputLength => .inputLength
  | .base => .base
  | .position => .validation target
  | lane => .reverse lane

private theorem positionRole_injective (target : PaddedDescriptionLane) :
    Function.Injective (positionRole target) := by
  intro a b h
  cases a <;> cases b <;> simp_all [positionRole]

private def installPosition (lanes : CheckedDescriptionLane → R)
    (source : DescriptionOffsetLane) (target : PaddedDescriptionLane) : Fragment R :=
  let reverse := lanes ∘ positionRole target
  (((add (lanes (.offset source)) (reverse .width) (reverse .scratch)).seq
    (incrementBy (reverse .width) 1)).seq (reverseWindowRegister 4 reverse)).seq
      (clearReverseLane (reverse .width))

/-- Cost of converting a logical last-bit offset to its reverse input address. -/
@[expose] def installDescriptionPositionCost (length base offset : Nat) : Nat :=
  (5 * offset + 3) + reverseWindowRegisterCost 4 length base (offset + 1) + (offset + 2)

theorem installDescriptionPositionCost_polynomiallyBounded {length base offset : Nat → Nat}
    (hLength : PolynomiallyBounded length) (hBase : PolynomiallyBounded base)
    (hOffset : PolynomiallyBounded offset) :
    PolynomiallyBounded (fun n ↦
      installDescriptionPositionCost (length n) (base n) (offset n)) := by
  let lit := PolynomiallyBounded.const
  exact (((((lit 5).mul hOffset).add (lit 3)).add
    (reverseWindowRegisterCost_polynomiallyBounded 4 hLength hBase (hOffset.add (lit 1)))).add
      (hOffset.add (lit 2)))

variable [DecidableEq R]

private theorem runsValues_installPosition (lanes : CheckedDescriptionLane → R)
    (hLanes : Function.Injective lanes) (word : BinaryWord) (source : DescriptionOffsetLane)
    (target : PaddedDescriptionLane) (v : R → Nat)
    (hWork : ∀ lane, v (lanes (.reverse lane)) = 0)
    (hTarget : v (lanes (.validation target)) = 0) :
    let inputLength := v (lanes .inputLength)
    let base := v (lanes .base)
    let offset := v (lanes (.offset source))
    ∃ ticks ≤ installDescriptionPositionCost inputLength base offset,
      (installPosition lanes source target).RunsValues word ticks v
        (setValue (lanes (.validation target)) (inputLength - 1 - (base + 4 * offset)) v) := by
  let reverse := lanes ∘ positionRole target
  let inputLength := v (lanes .inputLength)
  let base := v (lanes .base)
  let offset := v (lanes (.offset source))
  let position := inputLength - 1 - (base + 4 * offset)
  have hLane (a b : CheckedDescriptionLane) : lanes a = lanes b ↔ a = b :=
    ⟨fun h ↦ hLanes h, congrArg lanes⟩
  let loaded := setValue (reverse .width) offset v
  have hLoad : (add (lanes (.offset source)) (reverse .width) (reverse .scratch)).RunsValues
      word (5 * offset + 2) v loaded := by
    have hRun := runsValues_add (lanes (.offset source)) (reverse .width) (reverse .scratch)
      word v (by simp [reverse, positionRole, hLane]) (by simp [reverse, positionRole, hLane])
      (by simp [reverse, positionRole, hLane]) (hWork .scratch)
    have hWidth : v (reverse .width) = 0 := hWork .width
    simpa only [hWidth, Nat.zero_add, loaded, offset] using hRun
  let seeded := setValue (reverse .width) (offset + 1) v
  have hSeed : (incrementBy (reverse .width) 1).RunsValues word 1 loaded seeded := by
    simpa only [loaded, setValue_same, setValue_replace, seeded] using
      runsValues_incrementBy (reverse .width) 1 word loaded
  have hSeedZeros (lane : ReverseWindowLane) (hl : lane ≠ .inputLength) (hb : lane ≠ .base)
      (hw : lane ≠ .width) : seeded (reverse lane) = 0 := by
    cases lane <;> simp_all [seeded, setValue, reverse, positionRole]
  have hSeedLength : seeded (reverse .inputLength) = inputLength := by
    simp [seeded, setValue, reverse, positionRole, hLane, inputLength]
  have hSeedBase : seeded (reverse .base) = base := by
    simp [seeded, setValue, reverse, positionRole, hLane, base]
  have hSeedWidth : seeded (reverse .width) = offset + 1 := setValue_same ..
  obtain ⟨reverseTicks, hReverseTime, hReverse⟩ := runsValues_reverseWindowRegister 4 reverse
    (hLanes.comp (positionRole_injective target)) word seeded hSeedZeros
  rw [hSeedLength, hSeedBase, hSeedWidth] at hReverseTime hReverse
  have hAddress : reverseWindowStart inputLength base 4 (offset + 1) = position := by
    simp only [reverseWindowStart, Nat.add_sub_cancel, position]
  rw [hAddress] at hReverse
  let positioned := setValue (reverse .position) position seeded
  have hWidth : positioned (reverse .width) = offset + 1 := by
    simp [positioned, seeded, setValue, reverse, positionRole, hLane]
  have hFinal : setValue (reverse .width) 0 positioned =
      setValue (lanes (.validation target)) position v := by
    funext r
    by_cases hw : r = reverse .width
    · subst r
      simp [positioned, setValue, reverse, positionRole, hLane, hWork .width]
    · change r ≠ lanes (.reverse .width) at hw
      simp [positioned, seeded, setValue, reverse, positionRole, hw]
  have hClear : (clearReverseLane (reverse .width)).RunsValues word (offset + 2) positioned
      (setValue (lanes (.validation target)) position v) := by
    simpa only [hWidth, hFinal, Nat.add_assoc] using
      runsValues_clearReverseLane (reverse .width) word positioned
  have hCost : 5 * offset + 2 + 1 + reverseTicks + (offset + 2) ≤
      installDescriptionPositionCost inputLength base offset := by
    unfold installDescriptionPositionCost
    omega
  exact ⟨_, hCost, ((hLoad.seq hSeed).seq hReverse).seq hClear⟩

private def installValue (lanes : CheckedDescriptionLane → R) (source : CheckedDescriptionLane)
    (target : PaddedDescriptionLane) : Fragment R :=
  add (lanes source) (lanes (.validation target)) (lanes (.reverse .scratch))

private theorem runsValues_installValue (lanes : CheckedDescriptionLane → R)
    (hLanes : Function.Injective lanes) (word : BinaryWord) (source : CheckedDescriptionLane)
    (target : PaddedDescriptionLane) (v : R → Nat) (hSource : source ≠ .validation target)
    (hSourceScratch : source ≠ .reverse .scratch)
    (hTarget : v (lanes (.validation target)) = 0)
    (hScratch : v (lanes (.reverse .scratch)) = 0) :
    (installValue lanes source target).RunsValues word (5 * v (lanes source) + 2) v
      (setValue (lanes (.validation target)) (v (lanes source)) v) := by
  have h := runsValues_add (lanes source) (lanes (.validation target))
    (lanes (.reverse .scratch)) word v (fun e ↦ hSource (hLanes e))
    (fun e ↦ hSourceScratch (hLanes e)) (fun e ↦ by cases hLanes e) hScratch
  simpa only [installValue, hTarget, Nat.zero_add] using h

/-- Compute and install all cursors after the decoded gate count is checked. -/
def prepareCheckedDescription (lanes : CheckedDescriptionLane → R) : Fragment R :=
  let offset := descriptionOffsetRegister (lanes ∘ offsetRole)
  let widthOut := installValue lanes .width (.output 1)
  let widthGate := installValue lanes .width (.gate .width)
  let count := installValue lanes .count .gateCount
  let destination := installValue lanes (.offset .destination) (.gate (.gate .destination))
  let paddingWidth := installValue lanes (.offset .paddingWidth) (.padding 1)
  let outputPos := installPosition lanes .outputOffset (.output 0)
  let gatePos := installPosition lanes .gateOffset (.gate .position)
  let padPos := installPosition lanes .paddingOffset (.padding 0)
  ((((((((offset.seq widthOut).seq widthGate).seq count).seq destination).seq paddingWidth).seq
    outputPos).seq gatePos).seq padPos)

@[expose] def checkedDescriptionPreparationCost (length base arity count width span padded : Nat) :
    Nat :=
  let codeLength := 2 * width + count * span
  let padding := padded - codeLength
  descriptionOffsetRegisterCost arity count width span padded +
    (5 * width + 2) + (5 * width + 2) + (5 * count + 2) + (5 * (arity + count - 1) + 2) +
    (5 * padding + 2) + installDescriptionPositionCost length base (codeLength - 1) +
    installDescriptionPositionCost length base (width + (count - 1) * span + (span - 1)) +
    installDescriptionPositionCost length base (codeLength + (padding - 1))

theorem checkedDescriptionPreparationCost_polynomiallyBounded
    {length base arity count width span padded : Nat → Nat}
    (hLength : PolynomiallyBounded length) (hBase : PolynomiallyBounded base)
    (hArity : PolynomiallyBounded arity) (hCount : PolynomiallyBounded count)
    (hWidth : PolynomiallyBounded width) (hSpan : PolynomiallyBounded span)
    (hPadded : PolynomiallyBounded padded) :
    PolynomiallyBounded (fun n ↦ checkedDescriptionPreparationCost (length n) (base n)
      (arity n) (count n) (width n) (span n) (padded n)) := by
  let lit := PolynomiallyBounded.const
  have copy {f : Nat → Nat} (hf : PolynomiallyBounded f) :
      PolynomiallyBounded (fun n ↦ 5 * f n + 2) := ((lit 5).mul hf).add (lit 2)
  have pred {f : Nat → Nat} (hf : PolynomiallyBounded f) :
      PolynomiallyBounded (fun n ↦ f n - 1) := hf.mono (fun _ ↦ Nat.sub_le ..)
  have hCode := ((lit 2).mul hWidth).add (hCount.mul hSpan)
  have hPadding : PolynomiallyBounded (fun n ↦ padded n - (2 * width n + count n * span n)) :=
    hPadded.mono (fun _ ↦ Nat.sub_le ..)
  have hGate := (hWidth.add ((pred hCount).mul hSpan)).add (pred hSpan)
  have hPad := hCode.add (pred hPadding)
  have hOffset := descriptionOffsetRegisterCost_polynomiallyBounded
    hArity hCount hWidth hSpan hPadded
  have hCopies := ((((hOffset.add (copy hWidth)).add (copy hWidth)).add (copy hCount)).add
    (copy (pred (hArity.add hCount)))).add (copy hPadding)
  exact ((hCopies.add (installDescriptionPositionCost_polynomiallyBounded hLength hBase
    (pred hCode))).add (installDescriptionPositionCost_polynomiallyBounded hLength hBase hGate)).add
      (installDescriptionPositionCost_polynomiallyBounded hLength hBase hPad)

/-- The preparation reads no raw bits and preserves the prepared fields and decoded header. -/
theorem runsValues_prepareCheckedDescription (lanes : CheckedDescriptionLane → R)
    (hLanes : Function.Injective lanes) {word code : BinaryWord} {start arity cap : Nat}
    (hWindow : PaddedDescriptionWindow word code start arity cap) (before : R → Nat)
    (hSeed : CheckedDescriptionSeed lanes word start arity cap before)
    (hCount : before (lanes .count) = circuitDescriptionCount arity cap code)
    (hCountLe : circuitDescriptionCount arity cap code ≤ cap)
    (hZero : ∀ lane, lane ∉ checkedDescriptionInputLanes → lane ≠ .count →
      before (lanes lane) = 0) :
    let width := circuitFieldWidth arity cap
    let count := circuitDescriptionCount arity cap code
    ∃ ticks ≤ checkedDescriptionPreparationCost word.length start arity count width
        (3 + 2 * width) code.length,
      ∃ after : R → Nat,
        (prepareCheckedDescription lanes).RunsValues word ticks before after ∧
        PaddedDescriptionReady (lanes ∘ CheckedDescriptionLane.validation)
          word code start arity cap after ∧
        after (lanes (.offset .wires)) = arity + count ∧
        (∀ lane, (∀ i, lane ≠ .validation i) → (∀ i, lane ≠ .offset i) →
          after (lanes lane) = before (lanes lane)) ∧
        ∀ r, (∀ lane, r ≠ lanes lane) → after r = before r := by
  let w := circuitFieldWidth arity cap
  let c := circuitDescriptionCount arity cap code
  let span := 3 + 2 * w
  let H := 2 * w + c * span
  let pad := code.length - H
  let dst := arity + c - 1
  let output := H - 1
  let gate := w + (c - 1) * span + (span - 1)
  let padding := H + (pad - 1)
  have hLane (a b : CheckedDescriptionLane) : lanes a = lanes b ↔ a = b :=
    ⟨fun h ↦ hLanes h, congrArg lanes⟩
  have hLength : before (lanes .paddedLength) = code.length := hSeed.paddedLength.trans
    hWindow.length.symm
  let offs := lanes ∘ offsetRole
  have hOffsetZero (lane : DescriptionOffsetLane) (h : lane ∉ descriptionOffsetInputLanes) :
      before (offs lane) = 0 := by
    cases lane <;>
      simp_all [offs, offsetRole, descriptionOffsetInputLanes, checkedDescriptionInputLanes]
  obtain ⟨offsetValues, hOffsetRun, hOffset⟩ := runsValues_descriptionOffsetRegister offs
    (hLanes.comp offsetRole_injective) word before hOffsetZero
  rw [show before (offs .arity) = arity from hSeed.arityValue,
    show before (offs .count) = c from hCount,
    show before (offs .width) = w from hSeed.width,
    show before (offs .span) = span from hSeed.span,
    show before (offs .paddedLength) = code.length from hLength] at hOffsetRun
  have hCode : offsetValues (lanes (.offset .codeLength)) = H := by
    simpa only [offs, Function.comp_apply, offsetRole, hSeed.width, hCount, hSeed.span] using
      hOffset.codeLength
  have hPad : offsetValues (lanes (.offset .paddingWidth)) = pad := by
    simpa only [offs, Function.comp_apply, offsetRole, hLength, hCode] using hOffset.paddingWidth
  have hWires : offsetValues (lanes (.offset .wires)) = arity + c := by
    simpa only [offs, Function.comp_apply, offsetRole, hSeed.arityValue, hCount] using hOffset.wires
  have hDestination : offsetValues (lanes (.offset .destination)) = dst := by
    simpa only [offs, Function.comp_apply, offsetRole, hWires, dst] using hOffset.destination
  have hOutput : offsetValues (lanes (.offset .outputOffset)) = output := by
    simpa only [offs, Function.comp_apply, offsetRole, hCode, output] using hOffset.outputOffset
  have hGate : offsetValues (lanes (.offset .gateOffset)) = gate := by
    simpa only [offs, Function.comp_apply, offsetRole, hSeed.width, hCount, hSeed.span] using
      hOffset.gateOffset
  have hPadding : offsetValues (lanes (.offset .paddingOffset)) = padding := by
    simpa only [offs, Function.comp_apply, offsetRole, hCode, hPad, padding] using
      hOffset.paddingOffset
  have hFrame (lane : CheckedDescriptionLane)
      (h : ∀ off, lane ≠ .offset off) : offsetValues (lanes lane) = before (lanes lane) :=
    hOffset.frame _ (fun e ↦ h _ (hLanes e)) (fun e ↦ h _ (hLanes e))
      (fun e ↦ h _ (hLanes e)) (fun e ↦ h _ (hLanes e)) (fun e ↦ h _ (hLanes e))
      (fun e ↦ h _ (hLanes e)) (fun e ↦ h _ (hLanes e))
  have hV (lane : PaddedDescriptionLane) : offsetValues (lanes (.validation lane)) = 0 :=
    (hFrame _ (by intro _; simp)).trans
      (hZero _ (by simp [checkedDescriptionInputLanes]) (by simp))
  have hR (lane : ReverseWindowLane) : offsetValues (lanes (.reverse lane)) = 0 :=
    (hFrame _ (by intro _; simp)).trans
      (hZero _ (by simp [checkedDescriptionInputLanes]) (by simp))
  have hW : offsetValues (lanes .width) = w :=
    (hFrame _ (by intro _; simp)).trans hSeed.width
  have hC : offsetValues (lanes .count) = c :=
    (hFrame _ (by intro _; simp)).trans hCount
  have hN : offsetValues (lanes .inputLength) = word.length :=
    (hFrame _ (by intro _; simp)).trans hSeed.inputLength
  have hB : offsetValues (lanes .base) = start :=
    (hFrame _ (by intro _; simp)).trans hSeed.base
  let v1 := setValue (lanes (.validation (.output 1))) w offsetValues
  let v2 := setValue (lanes (.validation (.gate .width))) w v1
  let v3 := setValue (lanes (.validation .gateCount)) c v2
  let v4 := setValue (lanes (.validation (.gate (.gate .destination)))) dst v3
  let v5 := setValue (lanes (.validation (.padding 1))) pad v4
  have h1 := runsValues_installValue lanes hLanes word .width (.output 1) offsetValues
    (by simp) (by simp) (hV _) (hR _)
  rw [hW] at h1
  have h2 := runsValues_installValue lanes hLanes word .width (.gate .width) v1
    (by simp) (by simp) (by simp [v1, setValue, hLane, hV]) (by simp [v1, setValue, hLane, hR])
  rw [show v1 (lanes .width) = w by simp [v1, setValue, hLane, hW]] at h2
  have h3 := runsValues_installValue lanes hLanes word .count .gateCount v2 (by simp) (by simp)
    (by simp [v2, v1, setValue, hLane, hV]) (by simp [v2, v1, setValue, hLane, hR])
  rw [show v2 (lanes .count) = c by simp [v2, v1, setValue, hLane, hC]] at h3
  have h4 := runsValues_installValue lanes hLanes word (.offset .destination)
    (.gate (.gate .destination)) v3 (by simp) (by simp)
    (by simp [v3, v2, v1, setValue, hLane, hV]) (by simp [v3, v2, v1, setValue, hLane, hR])
  rw [show v3 (lanes (.offset .destination)) = dst by
    simp [v3, v2, v1, setValue, hLane, hDestination]] at h4
  have h5 := runsValues_installValue lanes hLanes word (.offset .paddingWidth) (.padding 1) v4
    (by simp) (by simp) (by simp [v4, v3, v2, v1, setValue, hLane, hV])
    (by simp [v4, v3, v2, v1, setValue, hLane, hR])
  rw [show v4 (lanes (.offset .paddingWidth)) = pad by
    simp [v4, v3, v2, v1, setValue, hLane, hPad]] at h5
  let reverse (offset : Nat) := word.length - 1 - (start + 4 * offset)
  let v6 := setValue (lanes (.validation (.output 0))) (reverse output) v5
  let v7 := setValue (lanes (.validation (.gate .position))) (reverse gate) v6
  let v8 := setValue (lanes (.validation (.padding 0))) (reverse padding) v7
  obtain ⟨outTicks, hOutTime, h6⟩ := runsValues_installPosition lanes hLanes word .outputOffset
    (.output 0) v5 (by intro lane; simp [v5, v4, v3, v2, v1, setValue, hLane, hR])
    (by simp [v5, v4, v3, v2, v1, setValue, hLane, hV])
  rw [show v5 (lanes .inputLength) = word.length by
      simp [v5, v4, v3, v2, v1, setValue, hLane, hN],
    show v5 (lanes .base) = start by simp [v5, v4, v3, v2, v1, setValue, hLane, hB],
    show v5 (lanes (.offset .outputOffset)) = output by
      simp [v5, v4, v3, v2, v1, setValue, hLane, hOutput]] at hOutTime h6
  obtain ⟨gateTicks, hGateTime, h7⟩ := runsValues_installPosition lanes hLanes word .gateOffset
    (.gate .position) v6 (by intro lane; simp [v6, v5, v4, v3, v2, v1, setValue, hLane, hR])
    (by simp [v6, v5, v4, v3, v2, v1, setValue, hLane, hV])
  rw [show v6 (lanes .inputLength) = word.length by
      simp [v6, v5, v4, v3, v2, v1, setValue, hLane, hN],
    show v6 (lanes .base) = start by simp [v6, v5, v4, v3, v2, v1, setValue, hLane, hB],
    show v6 (lanes (.offset .gateOffset)) = gate by
      simp [v6, v5, v4, v3, v2, v1, setValue, hLane, hGate]] at hGateTime h7
  obtain ⟨padTicks, hPadTime, h8⟩ := runsValues_installPosition lanes hLanes word .paddingOffset
    (.padding 0) v7 (by intro lane; simp [v7, v6, v5, v4, v3, v2, v1, setValue, hLane, hR])
    (by simp [v7, v6, v5, v4, v3, v2, v1, setValue, hLane, hV])
  rw [show v7 (lanes .inputLength) = word.length by
      simp [v7, v6, v5, v4, v3, v2, v1, setValue, hLane, hN],
    show v7 (lanes .base) = start by simp [v7, v6, v5, v4, v3, v2, v1, setValue, hLane, hB],
    show v7 (lanes (.offset .paddingOffset)) = padding by
      simp [v7, v6, v5, v4, v3, v2, v1, setValue, hLane, hPadding]] at hPadTime h8
  refine ⟨_, ?_, v8, ((((((((hOffsetRun.seq h1).seq h2).seq h3).seq h4).seq h5).seq
    h6).seq h7).seq h8), ?_, ?_, ?_, ?_⟩
  · unfold checkedDescriptionPreparationCost
    change _ ≤ descriptionOffsetRegisterCost arity c w span code.length +
      (5 * w + 2) + (5 * w + 2) + (5 * c + 2) + (5 * dst + 2) + (5 * pad + 2) +
      installDescriptionPositionCost word.length start output +
      installDescriptionPositionCost word.length start gate +
      installDescriptionPositionCost word.length start padding
    omega
  · have hWidthPos : 0 < w := by simp [w, circuitFieldWidth]
    have hOutputOffset : w + c * span + (w - 1) = output := by unfold output H; omega
    have hOutputPos : reverse output = reverseWindowStart word.length
        (start + 4 * (w + c * span)) 4 w := by
      simp only [reverse, reverseWindowStart, ← hOutputOffset, Nat.mul_add, Nat.add_assoc]
    have hGatePos : reverse gate = descriptionGateReversePosition word.length start w (c - 1) := by
      simp only [reverse, gate, descriptionGateReversePosition, reverseGateRecordPosition, span,
        Nat.mul_add, Nat.add_assoc]
    have hPadPos : reverse padding = reverseWindowStart word.length (start + 4 * H) 4 pad := by
      simp only [reverse, padding, reverseWindowStart, Nat.mul_add, Nat.add_assoc]
    have hCodeLength : circuitDescriptionCodeLength arity cap code = H := by
      simp only [circuitDescriptionCodeLength, circuitDescriptionLength, H, w, c, span]
    have hUnwritten (lane : PaddedDescriptionLane)
        (h : lane ≠ .padding 0 ∧ lane ≠ .gate .position ∧ lane ≠ .output 0 ∧
          lane ≠ .padding 1 ∧ lane ≠ .gate (.gate .destination) ∧ lane ≠ .gateCount ∧
          lane ≠ .gate .width ∧ lane ≠ .output 1) :
        v8 (lanes (.validation lane)) = 0 := by
      rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
      simp [v8, v7, v6, v5, v4, v3, v2, v1, setValue, hLane, hV, h1,h2,h3,h4,h5,h6,h7,h8]
    refine ⟨hCountLe, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [v8, v7, v6, setValue, hLane] using hOutputPos
    · simp [v8, v7, v6, v5, v4, v3, v2, v1, setValue, hLane, w]
    · intro i hi
      have h0 : i ≠ 0 := by
        intro h
        subst i
        exact (by decide : ¬ 2 ≤ (0 : Fin 5).val) hi
      have h1 : i ≠ 1 := by
        intro h
        subst i
        exact (by decide : ¬ 2 ≤ (1 : Fin 5).val) hi
      exact hUnwritten _ (by simp [h0, h1])
    · simp [v8, v7, v6, v5, v4, v3, setValue, hLane, c]
    · simp [v8, v7, v6, v5, v4, v3, v2, setValue, hLane, w]
    · simp [v8, v7, v6, v5, v4, setValue, hLane, dst, c]
    · simpa [v8, v7, setValue, hLane] using hGatePos
    · intro lane hl
      exact hUnwritten _ (by
        have hp : lane ≠ .position := by
          intro e
          subst lane
          simp [gateStructureScratchLanes] at hl
        have hd : lane ≠ .gate .destination := by
          intro e
          subst lane
          simp [gateStructureScratchLanes] at hl
        have hw : lane ≠ .width := by
          intro e
          subst lane
          simp [gateStructureScratchLanes] at hl
        simp [hp, hd, hw])
    · exact hUnwritten _ (by simp)
    · simpa [v8, setValue, hLane, hCodeLength, pad] using hPadPos
    · simp [v8, v7, v6, v5, setValue, hLane, hCodeLength, pad]
    · intro i hi
      have h0 : i ≠ 0 := by
        intro h
        subst i
        exact (by decide : ¬ 2 ≤ (0 : Fin 5).val) hi
      have h1 : i ≠ 1 := by
        intro h
        subst i
        exact (by decide : ¬ 2 ≤ (1 : Fin 5).val) hi
      exact hUnwritten _ (by simp [h0, h1])
  · simp [v8, v7, v6, v5, v4, v3, v2, v1, setValue, hLane, hWires, c]
  · intro lane hg ho
    simpa [v8, v7, v6, v5, v4, v3, v2, v1, setValue, hLane, hg] using hFrame lane ho
  · intro r hOutside
    simpa [v8, v7, v6, v5, v4, v3, v2, v1, setValue, hOutside] using
      hOffset.frame r (hOutside _) (hOutside _) (hOutside _) (hOutside _)
        (hOutside _) (hOutside _) (hOutside _)

private def countRole : DescriptionCountLane → CheckedDescriptionLane
  | .count => .count
  | .offset .inputLength => .inputLength
  | .offset .base => .base
  | .offset .width => .width
  | .offset lane => .reverse lane

private theorem countRole_injective : Function.Injective countRole := by
  intro a b h
  cases a with
  | count =>
    cases b with
    | count => rfl
    | offset b => cases b <;> simp [countRole] at h
  | offset a =>
    cases b with
    | count => cases a <;> simp [countRole] at h
    | offset b => cases a <;> cases b <;> simp_all [countRole]

private def compareRole (a b : CheckedDescriptionLane) : Fin 5 → CheckedDescriptionLane :=
  ([a, b, .guardLeft, .guardRight, .guardScratch] : List CheckedDescriptionLane).get

private theorem compareRole_injective (a b : CheckedDescriptionLane)
    (h : ([a, b, .guardLeft, .guardRight, .guardScratch] : List CheckedDescriptionLane).Nodup) :
    Function.Injective (compareRole a b) :=
  h.injective_get

private def checkedBranch (lanes : CheckedDescriptionLane → R) (a b : CheckedDescriptionLane)
    (below other : Fragment R) : Fragment R :=
  ifLess (lanes a) (lanes b) (lanes .guardLeft) (lanes .guardRight) (lanes .guardScratch)
    below other

private theorem runsValues_checkedBranch (lanes : CheckedDescriptionLane → R)
    (hLanes : Function.Injective lanes) (word : BinaryWord) (a b : CheckedDescriptionLane)
    (h : ([a, b, .guardLeft, .guardRight, .guardScratch] : List CheckedDescriptionLane).Nodup)
    (below other : Fragment R) (before : R → Nat)
    (hLeft : before (lanes .guardLeft) = 0) (hRight : before (lanes .guardRight) = 0)
    (hScratch : before (lanes .guardScratch) = 0) {ticks : Nat} {after : R → Nat}
    (hRun : (if before (lanes a) < before (lanes b) then below else other).RunsValues
      word ticks before after) :
    (checkedBranch lanes a b below other).RunsValues word
      (ifEqualTime (before (lanes a)) (before (lanes b)) + ticks) before after :=
  runsValues_ifLess (lanes ∘ compareRole a b) (hLanes.comp (compareRole_injective a b h))
    below other word before hLeft hRight hScratch hRun

/-- Count a failed check using at most three instructions, restoring the tested register. -/
private def countNonzero (test failures : R) : Fragment R where
  Label := Fin 3
  entry := some 0
  code
    | 0 => .dec test none (some 1)
    | 1 => .inc test (some 2)
    | _ => .inc failures none

private theorem runsValues_countNonzero (test failures : R)
    (word : BinaryWord) (before : R → Nat) :
    let failed := (decide (before test ≠ 0)).toNat
    (countNonzero test failures).RunsValues word (1 + 2 * failed) before
      (setValue failures (before failures + failed) before) := by
  dsimp only
  intro output
  by_cases h : before test = 0
  · simp [countNonzero, RegisterMachine.run, RegisterMachine.step, Instruction.execute,
      RegisterMachine.Fragment.close, RegisterMachine.Fragment.enter, h, setValue_current]
  · have hRestore : incrementValues test (decrementValues test before) = before := by
      have hNat : before test - 1 + 1 = before test := by omega
      funext r
      by_cases hr : r = test
      · subst r
        simp [incrementValues, decrementValues, hNat]
      · simp [incrementValues, decrementValues, hr]
    have hInc : incrementValues failures before =
        setValue failures (before failures + 1) before := by
      funext r
      by_cases hr : r = failures
      · subst r
        simp [incrementValues, setValue]
      · simp [incrementValues, setValue, hr]
    simp [countNonzero, RegisterMachine.run, RegisterMachine.step, Instruction.execute,
      RegisterMachine.Fragment.close, RegisterMachine.Fragment.enter, h, hRestore, hInc]

private def countDescriptionFailures (lanes : CheckedDescriptionLane → R) : Fragment R :=
  let output := checkedBranch lanes (.validation (.output 2)) (.offset .wires)
    skip (incrementBy (lanes .failures) 1)
  let gates := countNonzero (lanes (.validation (.gate (.gate .failures)))) (lanes .failures)
  let padding := countNonzero (lanes (.validation (.padding 2))) (lanes .failures)
  (output.seq gates).seq padding

private def checkedDescriptionBody (lanes : CheckedDescriptionLane → R) : Fragment R :=
  ((prepareCheckedDescription lanes).seq
    (paddedDescriptionRegister (lanes ∘ CheckedDescriptionLane.validation))).seq
      (countDescriptionFailures lanes)

/-- Read the claimed count and validate the description only if the count is within cap. -/
def checkedDescriptionRegister (lanes : CheckedDescriptionLane → R) : Fragment R :=
  (descriptionCountRegister (lanes ∘ countRole)).seq
    (checkedBranch lanes .cap .count (incrementBy (lanes .failures) 1)
      (checkedDescriptionBody lanes))

@[expose] def checkedDescriptionRegisterCost (length base arity cap count width padded : Nat) :
    Nat :=
  descriptionCountRegisterCost length base width + ifEqualTime cap count +
    checkedDescriptionPreparationCost length base arity count width (3 + 2 * width) padded +
    paddedDescriptionRegisterCost length width count
      (padded - (2 * width + count * (3 + 2 * width))) +
    ifEqualTime length (arity + count) + 7

theorem checkedDescriptionRegisterCost_polynomiallyBounded
    {length base arity cap count width padded : Nat → Nat}
    (hLength : PolynomiallyBounded length) (hBase : PolynomiallyBounded base)
    (hArity : PolynomiallyBounded arity) (hCap : PolynomiallyBounded cap)
    (hCount : PolynomiallyBounded count) (hWidth : PolynomiallyBounded width)
    (hPadded : PolynomiallyBounded padded) :
    PolynomiallyBounded (fun n ↦ checkedDescriptionRegisterCost (length n) (base n)
      (arity n) (cap n) (count n) (width n) (padded n)) := by
  let lit := PolynomiallyBounded.const
  have compare {a b : Nat → Nat} (ha : PolynomiallyBounded a) (hb : PolynomiallyBounded b) :
      PolynomiallyBounded (fun n ↦ ifEqualTime (a n) (b n)) :=
    ((lit 6).mul (ha.add hb)).add (lit 6)
  have hPad : PolynomiallyBounded (fun n ↦ padded n -
      (2 * width n + count n * (3 + 2 * width n))) :=
    hPadded.mono (fun _ ↦ Nat.sub_le ..)
  exact (((((descriptionCountRegisterCost_polynomiallyBounded hLength hBase hWidth).add
    (compare hCap hCount)).add (checkedDescriptionPreparationCost_polynomiallyBounded
      hLength hBase hArity hCount hWidth ((lit 3).add ((lit 2).mul hWidth)) hPadded)).add
    (paddedDescriptionRegisterCost_polynomiallyBounded hLength hWidth hCount hPad)).add
    (compare hLength (hArity.add hCount))).add (lit 7)

private theorem runsValues_countDescriptionFailures (lanes : CheckedDescriptionLane → R)
    (hLanes : Function.Injective lanes) (word : BinaryWord) (v : R → Nat)
    (hLeft : v (lanes .guardLeft) = 0) (hRight : v (lanes .guardRight) = 0)
    (hScratch : v (lanes .guardScratch) = 0) :
    let out := v (lanes (.validation (.output 2)))
    let wires := v (lanes (.offset .wires))
    let gateFailures := v (lanes (.validation (.gate (.gate .failures))))
    let padFailures := v (lanes (.validation (.padding 2)))
    let bad := (decide (¬ out < wires)).toNat + (decide (gateFailures ≠ 0)).toNat +
      (decide (padFailures ≠ 0)).toNat
    ∃ ticks ≤ ifEqualTime out wires + 7,
      (countDescriptionFailures lanes).RunsValues word ticks v
        (setValue (lanes .failures) (v (lanes .failures) + bad) v) := by
  let out := v (lanes (.validation (.output 2)))
  let wires := v (lanes (.offset .wires))
  let outBad := (decide (¬ out < wires)).toNat
  let gates := lanes (.validation (.gate (.gate .failures)))
  let padding := lanes (.validation (.padding 2))
  let gateBad := (decide (v gates ≠ 0)).toNat
  let padBad := (decide (v padding ≠ 0)).toNat
  let failures := lanes .failures
  let more := incrementBy failures 1
  let v1 := setValue failures (v failures + outBad) v
  let v2 := setValue failures (v failures + (outBad + gateBad)) v
  let v3 := setValue failures (v failures + (outBad + gateBad + padBad)) v
  have hLane (a b : CheckedDescriptionLane) : lanes a = lanes b ↔ a = b :=
    ⟨fun h ↦ hLanes h, congrArg lanes⟩
  have hBranch : (if out < wires then skip else more).RunsValues word outBad v v1 := by
    by_cases h : out < wires
    · have hBad : outBad = 0 := by simp [outBad, h]
      have hSame : v1 = v := by
        dsimp only [v1]
        rw [hBad, Nat.add_zero]
        exact setValue_current failures v
      simpa only [ite_eq_left h, hBad, hSame] using runsValues_skip word v
    · simpa [h, outBad, v1, more] using runsValues_incrementBy failures 1 word v
  have h1 := runsValues_checkedBranch lanes hLanes word (.validation (.output 2))
    (.offset .wires) (by simp) skip more v hLeft hRight hScratch hBranch
  have h2 := runsValues_countNonzero gates failures word v1
  dsimp only at h2
  have hGates : v1 gates = v gates := by simp [v1, gates, failures, setValue, hLane]
  rw [hGates] at h2
  have h2' : (countNonzero gates failures).RunsValues word (1 + 2 * gateBad) v1 v2 := by
    simpa only [v1, v2, setValue_same, setValue_replace, Nat.add_assoc, gateBad] using h2
  have h3 := runsValues_countNonzero padding failures word v2
  dsimp only at h3
  have hPadding : v2 padding = v padding := by simp [v2, padding, failures, setValue, hLane]
  rw [hPadding] at h3
  have h3' : (countNonzero padding failures).RunsValues word (1 + 2 * padBad) v2 v3 := by
    simpa only [v2, v3, setValue_same, setValue_replace, Nat.add_assoc, padBad] using h3
  have hSmall (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide
  have hOut := hSmall (decide (¬ out < wires))
  have hGate := hSmall (decide (v gates ≠ 0))
  have hPad := hSmall (decide (v padding ≠ 0))
  refine ⟨ifEqualTime out wires + outBad + (1 + 2 * gateBad) + (1 + 2 * padBad), ?_,
    (h1.seq h2').seq h3'⟩
  change ifEqualTime out wires + outBad + (1 + 2 * gateBad) + (1 + 2 * padBad) ≤
    ifEqualTime out wires + 7
  change outBad ≤ 1 at hOut
  change gateBad ≤ 1 at hGate
  change padBad ≤ 1 at hPad
  omega

/-- Exact validity of the raw padded codec, with a zero failure count precisely on valid codes.
The raw window and seven arithmetic input fields are the only data preconditions. -/
theorem runsValues_checkedDescriptionRegister (lanes : CheckedDescriptionLane → R)
    (hLanes : Function.Injective lanes) {word code : BinaryWord} {start arity cap : Nat}
    (hWindow : PaddedDescriptionWindow word code start arity cap) (before : R → Nat)
    (hSeed : CheckedDescriptionSeed lanes word start arity cap before)
    (hZero : ∀ lane, lane ∉ checkedDescriptionInputLanes → before (lanes lane) = 0) :
    let w := circuitFieldWidth arity cap
    let c := circuitDescriptionCount arity cap code
    ∃ ticks ≤ checkedDescriptionRegisterCost word.length start arity cap c w code.length,
      ∃ after, (checkedDescriptionRegister lanes).RunsValues word ticks before after ∧
        after (lanes .count) = c ∧
        (after (lanes .failures) = 0 ↔ PaddedCircuitDescriptionValid arity cap code) ∧
        (∀ lane ∈ checkedDescriptionInputLanes, after (lanes lane) = before (lanes lane)) ∧
        ∀ r, (∀ lane, r ≠ lanes lane) → after r = before r := by
  let w := circuitFieldWidth arity cap
  let c := circuitDescriptionCount arity cap code
  let counted := setValue (lanes .count) c before
  let counts := lanes ∘ countRole
  let valLanes := lanes ∘ CheckedDescriptionLane.validation
  have hLane (a b : CheckedDescriptionLane) : lanes a = lanes b ↔ a = b :=
    ⟨fun h ↦ hLanes h, congrArg lanes⟩
  have hCountZero (lane : DescriptionCountLane) (hn : lane ≠ .offset .inputLength)
      (hb : lane ≠ .offset .base) (hw : lane ≠ .offset .width) :
      before (counts lane) = 0 := by
    cases lane with
    | count => exact hZero _ (by simp [countRole, checkedDescriptionInputLanes])
    | offset lane =>
      cases lane <;> simp_all [counts, countRole, checkedDescriptionInputLanes]
  obtain ⟨readTicks, hReadTime, hRead⟩ := runsValues_descriptionCountRegister counts
    (hLanes.comp countRole_injective) hWindow before hSeed.inputLength hSeed.base hSeed.width
    hCountZero
  have hStable (lane : CheckedDescriptionLane) (h : lane ≠ .count) :
      counted (lanes lane) = before (lanes lane) := by simp [counted, setValue, hLane, h]
  have hZ (lane : CheckedDescriptionLane) (h : lane ∉ checkedDescriptionInputLanes)
      (hc : lane ≠ .count) : counted (lanes lane) = 0 := (hStable lane hc).trans (hZero lane h)
  have hCap : counted (lanes .cap) = cap := (hStable _ (by simp)).trans hSeed.capValue
  have hC : counted (lanes .count) = c := setValue_same ..
  have hSeeds : CheckedDescriptionSeed lanes word start arity cap counted := by
    constructor
    · exact (hStable _ (by simp)).trans hSeed.arityValue
    · exact hCap
    · exact (hStable _ (by simp)).trans hSeed.width
    · exact (hStable _ (by simp)).trans hSeed.span
    · exact (hStable _ (by simp)).trans hSeed.paddedLength
    · exact (hStable _ (by simp)).trans hSeed.inputLength
    · exact (hStable _ (by simp)).trans hSeed.base
  have hGuard {branch otherwise : Fragment R} {ticks : Nat} {after : R → Nat}
      (hRun : (if cap < c then branch else otherwise).RunsValues word ticks counted after) :
      (checkedBranch lanes .cap .count branch otherwise).RunsValues word
        (ifEqualTime cap c + ticks) counted after := by
    have hRun' : (if counted (lanes .cap) < counted (lanes .count) then branch
        else otherwise).RunsValues word ticks counted after := by
      simpa only [hCap, hC] using hRun
    simpa only [hCap, hC] using runsValues_checkedBranch lanes hLanes word .cap .count
      (by simp) branch otherwise counted (hZ _ (by simp [checkedDescriptionInputLanes]) (by simp))
      (hZ _ (by simp [checkedDescriptionInputLanes]) (by simp))
      (hZ _ (by simp [checkedDescriptionInputLanes]) (by simp)) hRun'
  have hInitStable (lane : CheckedDescriptionLane) (h : lane ∈ checkedDescriptionInputLanes) :
      lane ≠ .count ∧ lane ≠ .failures ∧ (∀ i, lane ≠ .validation i) ∧
        (∀ i, lane ≠ .offset i) := by
    cases lane <;> simp_all [checkedDescriptionInputLanes]
  by_cases hInvalid : cap < c
  · let rejected := setValue (lanes .failures) 1 counted
    have hFail : counted (lanes .failures) = 0 :=
      hZ _ (by simp [checkedDescriptionInputLanes]) (by simp)
    have hReject := runsValues_incrementBy (lanes .failures) 1 word counted
    rw [hFail, Nat.zero_add] at hReject
    have hRun := hRead.seq (hGuard (otherwise := checkedDescriptionBody lanes) (ticks := 1)
      (by simpa only [ite_eq_left hInvalid] using hReject))
    refine ⟨readTicks + (ifEqualTime cap c + 1), ?_, rejected, hRun, ?_, ?_, ?_, ?_⟩
    · change _ ≤ checkedDescriptionRegisterCost word.length start arity cap c w code.length
      unfold checkedDescriptionRegisterCost
      change readTicks ≤ descriptionCountRegisterCost word.length start w at hReadTime
      omega
    · simp [rejected, setValue, hLane, hC, c]
    · have hNotValid : ¬ PaddedCircuitDescriptionValid arity cap code :=
        fun h ↦ (Nat.not_le.mpr hInvalid) h.count_le
      simp [rejected, hNotValid]
    · intro lane hl
      obtain ⟨hc, hf, _, _⟩ := hInitStable lane hl
      simp [rejected, setValue, hLane, hf, hStable lane hc]
    · intro r hr
      simp [rejected, counted, setValue, hr]
  · have hCountLe : c ≤ cap := Nat.le_of_not_gt hInvalid
    obtain ⟨prepTicks, hPrepTime, ready, hPrep, hReady, hWires, hPrepFrame, hPrepOuter⟩ :=
      runsValues_prepareCheckedDescription lanes hLanes hWindow counted hSeeds hC hCountLe hZ
    obtain ⟨checkTicks, hCheckTime, checked, hCheck, hOut, hCorrect, hCheckFrame⟩ :=
      runsValues_paddedDescriptionRegister valLanes
        (hLanes.comp fun _ _ h ↦ CheckedDescriptionLane.validation.inj h) hWindow hReady
    have hCheckStable (r : R) (h : ∀ i, r ≠ valLanes i) :
        checked r = ready r :=
      hCheckFrame r (fun i ↦ h (.output i)) (fun i ↦ h (.gate i)) (h .gateCount)
        (fun i ↦ h (.padding i))
    have hNamed (lane : CheckedDescriptionLane) (hv : ∀ i, lane ≠ .validation i)
        (ho : ∀ i, lane ≠ .offset i) : checked (lanes lane) = counted (lanes lane) :=
      (hCheckStable _ (fun i e ↦ hv i (hLanes e))).trans (hPrepFrame lane hv ho)
    have hW : checked (lanes (.offset .wires)) = arity + c :=
      (hCheckStable _ (by intro i; simp [valLanes, hLane])).trans hWires
    have hGuardZero (lane : CheckedDescriptionLane)
        (hv : ∀ i, lane ≠ .validation i) (ho : ∀ i, lane ≠ .offset i)
        (hInput : lane ∉ checkedDescriptionInputLanes) (hc : lane ≠ .count) :
        checked (lanes lane) = 0 := (hNamed lane hv ho).trans (hZ lane hInput hc)
    obtain ⟨finishTicks, hFinishTime, hFinish⟩ := runsValues_countDescriptionFailures
      lanes hLanes word checked
      (hGuardZero _ (by intro _; simp) (by intro _; simp)
        (by simp [checkedDescriptionInputLanes]) (by simp))
      (hGuardZero _ (by intro _; simp) (by intro _; simp)
        (by simp [checkedDescriptionInputLanes]) (by simp))
      (hGuardZero _ (by intro _; simp) (by intro _; simp)
        (by simp [checkedDescriptionInputLanes]) (by simp))
    let out := checked (valLanes (.output 2))
    let gateBad := (decide (checked (valLanes (.gate (.gate .failures))) ≠ 0)).toNat
    let padBad := (decide (checked (valLanes (.padding 2)) ≠ 0)).toNat
    let bad := (decide (¬ out < arity + c)).toNat + gateBad + padBad
    let after := setValue (lanes .failures) bad checked
    have hV : checked (lanes .failures) = 0 :=
      hGuardZero _ (by intro _; simp) (by intro _; simp)
        (by simp [checkedDescriptionInputLanes]) (by simp)
    rw [hW, hV, Nat.zero_add] at hFinish
    rw [hW] at hFinishTime
    have hOutBound : out ≤ word.length := by
      rw [show out = circuitDescriptionOutput w c code from hOut]
      unfold circuitDescriptionOutput
      have hMul := Nat.mul_le_mul_right (3 + 2 * w) hCountLe
      have hLen : code.length = 2 * w + cap * (3 + 2 * w) := hWindow.length
      have hFits : w ≤ (code.drop (w + c * (3 + 2 * w))).length := by
        rw [List.length_drop, hLen]
        omega
      exact (fieldValue_le_circuitFieldWidth_cap arity cap _
        (List.length_take_of_le hFits)).trans hWindow.capacity
    have hTail := (hPrep.seq hCheck).seq hFinish
    have hRun := hRead.seq (hGuard (branch := incrementBy (lanes .failures) 1)
      (otherwise := checkedDescriptionBody lanes)
      (by simpa only [ite_eq_right hInvalid, checkedDescriptionBody, valLanes] using hTail))
    refine ⟨readTicks + (ifEqualTime cap c + (prepTicks + checkTicks + finishTicks)), ?_,
      after, hRun, ?_, ?_, ?_, ?_⟩
    · unfold checkedDescriptionRegisterCost
      have hCompare : ifEqualTime out (arity + c) ≤ ifEqualTime word.length (arity + c) := by
        unfold ifEqualTime
        omega
      change readTicks + (ifEqualTime cap c + (prepTicks + checkTicks + finishTicks)) ≤
        descriptionCountRegisterCost word.length start w + ifEqualTime cap c +
        checkedDescriptionPreparationCost word.length start arity c w (3 + 2 * w) code.length +
        paddedDescriptionRegisterCost word.length w c
          (code.length - (2 * w + c * (3 + 2 * w))) + ifEqualTime word.length (arity + c) + 7
      change readTicks ≤ descriptionCountRegisterCost word.length start w at hReadTime
      change prepTicks ≤ checkedDescriptionPreparationCost word.length start arity c w
        (3 + 2 * w) code.length at hPrepTime
      change checkTicks ≤ paddedDescriptionRegisterCost word.length w c
        (code.length - (2 * w + c * (3 + 2 * w))) at hCheckTime
      change finishTicks ≤ ifEqualTime out (arity + c) + 7 at hFinishTime
      omega
    · simp [after, setValue, hLane,
        hNamed .count (by intro _; simp) (by intro _; simp), hC, c]
    · simpa [after, setValue, bad, Nat.add_eq_zero_iff, and_assoc, gateBad, padBad, out, c]
        using hCorrect
    · intro lane hl
      obtain ⟨hc, hf, hv, ho⟩ := hInitStable lane hl
      simp [after, setValue, hLane, hf, hNamed lane hv ho, hStable lane hc]
    · intro r hr
      have hCheckOuter := hCheckStable r (fun i ↦ hr (.validation i))
      rw [show after r = checked r from setValue_other (hr .failures) .., hCheckOuter,
        hPrepOuter r hr]
      exact setValue_other (hr .count) ..

end PvsNP.MCSP
