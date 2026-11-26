module

public import PvsNP.MCSP.PackedStructureBlock
public import PvsNP.MCSP.PaddedFieldRegister

/-! # Counted validation of a prepared padded description -/

public section

namespace PvsNP.MCSP

open Circuits RegisterMachine RegisterMachine.Fragment

inductive PaddedDescriptionLane where
  | output (lane : Fin 5)
  | gate (lane : GateRecordLane)
  | gateCount
  | padding (lane : Fin 5)
  deriving DecidableEq

variable {R : Type}

/-- Read the output wire, validate all claimed gate records, then check the padding. -/
def paddedDescriptionRegister (lanes : PaddedDescriptionLane → R) : Fragment R :=
  (stridedField 4 (lanes ∘ PaddedDescriptionLane.output)).seq
    ((checkGateStructureBlock (lanes ∘ PaddedDescriptionLane.gate) (lanes .gateCount)).seq
      (stridedZeroWindow 4 (lanes ∘ PaddedDescriptionLane.padding)))

@[expose] def paddedDescriptionRegisterCost (length width count padding : Nat) : Nat :=
  stridedFieldCost 4 length width length +
    (gateBlockCost length width count + stridedZeroWindowCost 4 length padding)

theorem paddedDescriptionRegisterCost_polynomiallyBounded {length width count padding : Nat → Nat}
    (hLength : PolynomiallyBounded length) (hWidth : PolynomiallyBounded width)
    (hCount : PolynomiallyBounded count) (hPadding : PolynomiallyBounded padding) :
    PolynomiallyBounded (fun n ↦ paddedDescriptionRegisterCost
      (length n) (width n) (count n) (padding n)) :=
  (stridedFieldCost_polynomiallyBounded 4 hLength hWidth hLength).add
    ((gateBlockCost_polynomiallyBounded hLength hWidth hCount).add
      (stridedZeroWindowCost_polynomiallyBounded 4 hLength hPadding))

/-- Cursor positions and work registers after checking the decoded count is within the budget. -/
structure PaddedDescriptionReady (lanes : PaddedDescriptionLane → R)
    (word code : BinaryWord) (start arity cap : Nat) (values : R → Nat) : Prop where
  count_le : circuitDescriptionCount arity cap code ≤ cap
  outputPosition : values (lanes (.output 0)) = reverseWindowStart word.length
    (start + 4 * (circuitFieldWidth arity cap + circuitDescriptionCount arity cap code *
      (3 + 2 * circuitFieldWidth arity cap))) 4 (circuitFieldWidth arity cap)
  outputWidth : values (lanes (.output 1)) = circuitFieldWidth arity cap
  outputZero : ∀ i : Fin 5, 2 ≤ i.val → values (lanes (.output i)) = 0
  gateCount : values (lanes .gateCount) = circuitDescriptionCount arity cap code
  gateWidth : values (lanes (.gate .width)) = circuitFieldWidth arity cap
  gateDestination : values (lanes (.gate (.gate .destination))) =
    arity + circuitDescriptionCount arity cap code - 1
  gatePosition : values (lanes (.gate .position)) = descriptionGateReversePosition word.length
    start (circuitFieldWidth arity cap) (circuitDescriptionCount arity cap code - 1)
  gateScratch : ∀ lane ∈ gateStructureScratchLanes, values (lanes (.gate lane)) = 0
  gateFailures : values (lanes (.gate (.gate .failures))) = 0
  paddingPosition : values (lanes (.padding 0)) = reverseWindowStart word.length
    (start + 4 * circuitDescriptionCodeLength arity cap code) 4
    (code.length - circuitDescriptionCodeLength arity cap code)
  paddingWidth : values (lanes (.padding 1)) =
    code.length - circuitDescriptionCodeLength arity cap code
  paddingZero : ∀ i : Fin 5, 2 ≤ i.val → values (lanes (.padding i)) = 0

variable [DecidableEq R]

/-- The three executable checks characterize acceptance by the exact padded codec. -/
theorem runsValues_paddedDescriptionRegister (lanes : PaddedDescriptionLane → R)
    (hLanes : Function.Injective lanes) {word code : BinaryWord} {start arity cap : Nat}
    (hWindow : PaddedDescriptionWindow word code start arity cap) {before : R → Nat}
    (hReady : PaddedDescriptionReady lanes word code start arity cap before) :
    let width := circuitFieldWidth arity cap
    let count := circuitDescriptionCount arity cap code
    let padding := code.length - circuitDescriptionCodeLength arity cap code
    ∃ ticks ≤ paddedDescriptionRegisterCost word.length width count padding,
      ∃ after : R → Nat, (paddedDescriptionRegister lanes).RunsValues word ticks before after ∧
        after (lanes (.output 2)) = circuitDescriptionOutput width count code ∧
        ((after (lanes (.output 2)) < arity + count ∧
            after (lanes (.gate (.gate .failures))) = 0 ∧
            after (lanes (.padding 2)) = 0) ↔ PaddedCircuitDescriptionValid arity cap code) ∧
        ∀ r, (∀ i, r ≠ lanes (.output i)) → (∀ i, r ≠ lanes (.gate i)) →
          r ≠ lanes .gateCount → (∀ i, r ≠ lanes (.padding i)) → after r = before r := by
  let width := circuitFieldWidth arity cap
  let count := circuitDescriptionCount arity cap code
  let outputOffset := width + count * (3 + 2 * width)
  let outputLanes := lanes ∘ PaddedDescriptionLane.output
  let gateLanes := lanes ∘ PaddedDescriptionLane.gate
  let paddingLanes := lanes ∘ PaddedDescriptionLane.padding
  have laneEq (a b : PaddedDescriptionLane) : lanes a = lanes b ↔ a = b :=
    ⟨fun h ↦ hLanes h, congrArg lanes⟩
  have injOutput : Function.Injective outputLanes := hLanes.comp fun _ _ h ↦
    PaddedDescriptionLane.output.inj h
  have injGate : Function.Injective gateLanes := hLanes.comp fun _ _ h ↦
    PaddedDescriptionLane.gate.inj h
  have injPadding : Function.Injective paddingLanes := hLanes.comp fun _ _ h ↦
    PaddedDescriptionLane.padding.inj h
  have hLength : code.length = circuitDescriptionLength width cap := hWindow.length
  have hOutputFits : outputOffset + width ≤ code.length := by
    have hBound := Nat.mul_le_mul_right (3 + 2 * width) hReady.count_le
    rw [hLength, circuitDescriptionLength]
    change count * (3 + 2 * width) ≤ cap * (3 + 2 * width) at hBound
    dsimp only [outputOffset]
    omega
  obtain ⟨outTicks, hOutTime, withOutput, hOutRun, _, _, hOutValue, hOutFrame⟩ :=
    runsValues_paddedDescriptionField outputLanes injOutput hWindow outputOffset hOutputFits
      before hReady.outputPosition hReady.outputWidth
      (hReady.outputZero 2 (by decide)) (hReady.outputZero 3 (by decide))
      (hReady.outputZero 4 (by decide))
  have hGateStable (lane : GateRecordLane) :
      withOutput (gateLanes lane) = before (gateLanes lane) :=
    hOutFrame _ (by simp [gateLanes, outputLanes, laneEq])
      (by simp [gateLanes, outputLanes, laneEq]) (by simp [gateLanes, outputLanes, laneEq])
  have hCountStable : withOutput (lanes .gateCount) = before (lanes .gateCount) :=
    hOutFrame _ (by simp [outputLanes, laneEq]) (by simp [outputLanes, laneEq])
      (by simp [outputLanes, laneEq])
  have hGateReady := packedStructureBlockReady arity cap start word code gateLanes
    (lanes .gateCount) withOutput hLength hReady.count_le hWindow.capacity hWindow.read
    (hCountStable.trans hReady.gateCount) ((hGateStable .width).trans hReady.gateWidth)
    ((hGateStable _).trans hReady.gateDestination) ((hGateStable _).trans hReady.gatePosition)
    (fun lane h ↦ (hGateStable lane).trans (hReady.gateScratch lane h))
  have hGateCounter (lane : GateRecordLane) : gateLanes lane ≠ lanes .gateCount := by
    simp [gateLanes, laneEq]
  obtain ⟨gateTicks, hGateTime, withGates, hGateRun, _, _, _, hGates, hGateFrame⟩ :=
    runsValues_checkPackedStructureBlock arity cap code injGate hGateCounter
      ((hGateStable _).trans hReady.gateFailures) hGateReady
  rw [(hGateStable .width).trans hReady.gateWidth] at hGateTime
  have hPaddingStable (i : Fin 5) : withGates (paddingLanes i) = before (paddingLanes i) := by
    rw [hGateFrame _ (by simp [paddingLanes, laneEq]) (by simp [paddingLanes, gateLanes, laneEq])
      (by simp [paddingLanes, gateLanes, laneEq]) (by simp [paddingLanes, gateLanes, laneEq])]
    exact hOutFrame _ (by simp [paddingLanes, outputLanes, laneEq])
      (by simp [paddingLanes, outputLanes, laneEq]) (by simp [paddingLanes, outputLanes, laneEq])
  obtain ⟨padTicks, hPadTime, after, hPadRun, _, _, hPadding, hPadFrame⟩ :=
    runsValues_paddedDescriptionPadding paddingLanes injPadding hWindow withGates
      ((hPaddingStable 0).trans hReady.paddingPosition)
      ((hPaddingStable 1).trans hReady.paddingWidth)
      ((hPaddingStable 2).trans (hReady.paddingZero 2 (by decide)))
      ((hPaddingStable 3).trans (hReady.paddingZero 3 (by decide)))
      ((hPaddingStable 4).trans (hReady.paddingZero 4 (by decide)))
  rw [List.length_drop] at hPadTime
  have hOut : after (lanes (.output 2)) = circuitDescriptionOutput width count code := by
    rw [hPadFrame _ (by simp [paddingLanes, laneEq]) (by simp [paddingLanes, laneEq])
      (by simp [paddingLanes, laneEq]),
      hGateFrame _ (by simp [laneEq]) (by simp [gateLanes, laneEq]) (by simp [gateLanes, laneEq])
        (by simp [gateLanes, laneEq])]
    exact hOutValue
  have hGates' : after (lanes (.gate (.gate .failures))) = 0 ↔
      ∀ i, i < count → (circuitDescriptionGateAt width arity code i).isSome := by
    rw [hPadFrame _ (by simp [paddingLanes, laneEq]) (by simp [paddingLanes, laneEq])
      (by simp [paddingLanes, laneEq])]
    exact hGates
  refine ⟨outTicks + (gateTicks + padTicks), Nat.add_le_add hOutTime
    (Nat.add_le_add hGateTime hPadTime), after, hOutRun.seq (hGateRun.seq hPadRun), hOut, ?_, ?_⟩
  · change (_ ∧ _ ∧ after (paddingLanes 2) = 0) ↔ _
    rw [hOut, hGates', hPadding]
    exact ⟨fun ⟨hout, hgate, hpad⟩ ↦ ⟨hLength, hReady.count_le, hout, hgate, hpad⟩,
      fun h ↦ ⟨h.output_lt, h.gateAt, h.padding_zero⟩⟩
  · intro r hOutput hGate hCounter hPad
    exact (hPadFrame r (hPad 0) (hPad 1) (hPad 2)).trans
      ((hGateFrame r hCounter (hGate .position) (hGate (.gate .destination))
        (hGate (.gate .failures))).trans (hOutFrame r (hOutput 0) (hOutput 1) (hOutput 2)))

end PvsNP.MCSP
