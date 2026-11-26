module

public import PvsNP.MCSP.GateRegister
public import PvsNP.TuringMachine.Registers.StridedField

import all PvsNP.TuringMachine.Registers.BinaryCompare

/-! # Counted verification of one reverse-strided gate record -/

public section

namespace PvsNP.MCSP

open Circuits RegisterMachine RegisterMachine.Fragment

inductive GateRecordLane where
  | gate (lane : GateCheckLane)
  | position | width | remaining
  deriving DecidableEq

/-- A reverse cursor reads the last bit of the right operand first. -/
structure GateRecordLayout (word : BinaryWord) (position width : Nat)
    (tag left right : BinaryWord) : Prop where
  tag_length : tag.length = 3
  left_length : left.length = width
  right_length : right.length = width
  read : ∀ i, i < (tag ++ left ++ right).length →
    word.reverse[position + 4 * i]? = (tag ++ left ++ right).reverse[i]?

structure GateRecordReady {R : Type} (lanes : GateRecordLane → R) (word trace : BinaryWord)
    (values : R → Nat) : Prop where
  gate : GateCheckReady (lanes ∘ GateRecordLane.gate) word trace values
  remaining_zero : values (lanes .remaining) = 0
  left_zero : values (lanes (.gate .left)) = 0
  right_zero : values (lanes (.gate .right)) = 0
  opcode_zero : values (lanes (.gate .opcode)) = 0

/-- Interpret the three decoded fields and compare the gate with the supplied trace. -/
@[expose] def gateRecordPasses (trace : BinaryWord) (destination : Nat)
    (tag left right : BinaryWord) : Bool :=
  ((gateFromFields destination (fieldValue tag) (fieldValue left) (fieldValue right)).map
    fun gate ↦ gate.traceInstruction.checkAt destination trace).getD false

structure GateRecordResult {R : Type} (lanes : GateRecordLane → R) (trace : BinaryWord)
    (tag left right : BinaryWord) (before after : R → Nat) : Prop where
  position : after (lanes .position) = before (lanes .position) +
    4 * (3 + 2 * before (lanes .width))
  destination : after (lanes (.gate .destination)) = before (lanes (.gate .destination)) - 1
  failures : after (lanes (.gate .failures)) = before (lanes (.gate .failures)) +
    if gateRecordPasses trace (before (lanes (.gate .destination))) tag left right then 0 else 1
  frame : ∀ r, r ≠ lanes .position → r ≠ lanes (.gate .destination) →
    r ≠ lanes (.gate .failures) → after r = before r

private inductive RecordField where
  | right | left | opcode

private def RecordField.target : RecordField → GateCheckLane
  | .right => .right
  | .left => .left
  | .opcode => .opcode

private def fieldLanes (field : RecordField) : Fin 5 → GateRecordLane
  | 0 => .position
  | 1 => .remaining
  | 2 => .gate field.target
  | 3 => .gate .lookupWork
  | _ => .gate .scratch

private theorem fieldLanes_injective (field : RecordField) :
    Function.Injective (fieldLanes field) := by
  cases field <;> decide

variable {R : Type}

private def loadRecordWidth (lanes : GateRecordLane → R) : Fragment R :=
  add (lanes .width) (lanes .remaining) (lanes (.gate .scratch))

private def readRecordField (lanes : GateRecordLane → R) (field : RecordField) : Fragment R :=
  stridedField 4 (lanes ∘ fieldLanes field)

private def clearRecordOperands (lanes : GateRecordLane → R) : Fragment R :=
  ((clearLane (lanes (.gate .left))).seq (clearLane (lanes (.gate .right)))).seq
    (decrementLane (lanes (.gate .destination)))

/-- Read the right operand, left operand, and opcode in reverse order, then check the gate. -/
def checkGateRecordRegister (lanes : GateRecordLane → R) : Fragment R :=
  ((((loadRecordWidth lanes).seq (readRecordField lanes .right)).seq
    ((loadRecordWidth lanes).seq (readRecordField lanes .left))).seq
    ((incrementBy (lanes .remaining) 3).seq (readRecordField lanes .opcode))).seq
      ((checkGateRegister (lanes ∘ GateRecordLane.gate)).seq (clearRecordOperands lanes))

@[expose] def gateRecordCost (length width : Nat) : Nat :=
  2 * (5 * width + 2 + stridedFieldCost 4 length width length) +
    3 + stridedFieldCost 4 length 3 7 + gateCheckCost length + 2 * length + 3

theorem gateRecordCost_polynomiallyBounded {length width : Nat → Nat}
    (hLength : PolynomiallyBounded length) (hWidth : PolynomiallyBounded width) :
    PolynomiallyBounded (fun n ↦ gateRecordCost (length n) (width n)) := by
  have hCopy := ((PolynomiallyBounded.const 5).mul hWidth).add (PolynomiallyBounded.const 2)
  have hOperands := (PolynomiallyBounded.const 2).mul
    (hCopy.add (stridedFieldCost_polynomiallyBounded 4 hLength hWidth hLength))
  have hTag := stridedFieldCost_polynomiallyBounded 4 hLength
    (PolynomiallyBounded.const 3) (PolynomiallyBounded.const 7)
  have hGate := ((PolynomiallyBounded.const 100).mul hLength).add (PolynomiallyBounded.const 70)
  have hClear := (PolynomiallyBounded.const 2).mul hLength
  exact (((((hOperands.add (PolynomiallyBounded.const 3)).add hTag).add hGate).add hClear).add
    (PolynomiallyBounded.const 3))

private theorem GateRecordLayout.reverse_eq (tag left right : BinaryWord) :
    (tag ++ left ++ right).reverse = right.reverse ++ (left.reverse ++ tag.reverse) := by
  simp only [List.reverse_append, List.append_assoc]

private theorem GateRecordLayout.read_right {word tag left right : BinaryWord}
    {position width : Nat}
    (h : GateRecordLayout word position width tag left right) (i : Nat) (hi : i < right.length) :
    word.reverse[position + 4 * i]? = right.reverse[i]? := by
  have hRead := h.read i (by simp only [List.length_append]; omega)
  rw [GateRecordLayout.reverse_eq, List.getElem?_append_left] at hRead
  · exact hRead
  · simpa only [List.length_reverse] using hi

private theorem GateRecordLayout.read_left {word tag left right : BinaryWord} {position width : Nat}
    (h : GateRecordLayout word position width tag left right) (i : Nat) (hi : i < left.length) :
    word.reverse[position + 4 * right.length + 4 * i]? = left.reverse[i]? := by
  have hRead := h.read (right.length + i) (by simp only [List.length_append]; omega)
  rw [Nat.mul_add, ← Nat.add_assoc, GateRecordLayout.reverse_eq,
    List.getElem?_append_right (by simp only [List.length_reverse]; omega),
    List.length_reverse, Nat.add_sub_cancel_left,
    List.getElem?_append_left (by simpa only [List.length_reverse] using hi)] at hRead
  exact hRead

private theorem GateRecordLayout.read_tag {word tag left right : BinaryWord} {position width : Nat}
    (h : GateRecordLayout word position width tag left right) (i : Nat) (hi : i < tag.length) :
    word.reverse[position + 4 * right.length + 4 * left.length + 4 * i]? = tag.reverse[i]? := by
  have hRead := h.read (right.length + (left.length + i)) (by simp only [List.length_append]; omega)
  rw [Nat.mul_add, Nat.mul_add, ← Nat.add_assoc, ← Nat.add_assoc,
    GateRecordLayout.reverse_eq,
    List.getElem?_append_right (by simp only [List.length_reverse]; omega),
    List.length_reverse, Nat.add_sub_cancel_left,
    List.getElem?_append_right (by simp only [List.length_reverse]; omega),
    List.length_reverse, Nat.add_sub_cancel_left] at hRead
  exact hRead

variable [DecidableEq R]

private def decodedFieldValues (lanes : GateRecordLane → R) (field : RecordField)
    (bits : BinaryWord) (before : R → Nat) : R → Nat :=
  setValue (lanes .position) (before (lanes .position) + 4 * bits.length)
    (setValue (lanes (.gate field.target)) (fieldValue bits) before)

private theorem runsValues_recordField (lanes : GateRecordLane → R)
    (hLanes : Function.Injective lanes) (field : RecordField) (word bits : BinaryWord)
    (cap : Nat) (before : R → Nat) (setup : Fragment R) (setupTicks : Nat)
    (hSetup : setup.RunsValues word setupTicks before
      (setValue (lanes .remaining) bits.length before))
    (hRemaining : before (lanes .remaining) = 0)
    (hAcc : before (lanes (.gate field.target)) = 0)
    (hLookup : before (lanes (.gate .lookupWork)) = 0)
    (hScratch : before (lanes (.gate .scratch)) = 0)
    (hCap : fieldValue bits ≤ cap)
    (hRead : ∀ i, i < bits.length →
      word.reverse[before (lanes .position) + 4 * i]? = bits.reverse[i]?) :
    ∃ ticks ≤ setupTicks + stridedFieldCost 4 word.length bits.length cap,
      (setup.seq (readRecordField lanes field)).RunsValues word ticks before
        (decodedFieldValues lanes field bits before) := by
  have hNe {a b : GateRecordLane} (hne : a ≠ b) : lanes a ≠ lanes b := fun eq ↦ hne (hLanes eq)
  let loaded := setValue (lanes .remaining) bits.length before
  have hFrame {k : GateRecordLane} (hne : k ≠ .remaining) : loaded (lanes k) = before (lanes k) :=
    setValue_other (hNe hne) ..
  have hPosition := hFrame (show GateRecordLane.position ≠ .remaining by decide)
  obtain ⟨ticks, hTicks, after, hRun, hCount, hPos, hVal, hUnchanged⟩ :=
    runsValues_stridedField_of_reads 4 (lanes ∘ fieldLanes field)
      (hLanes.comp (fieldLanes_injective field)) word bits cap loaded
      (setValue_same ..)
      ((hFrame (show GateRecordLane.gate field.target ≠ .remaining by simp)).trans hAcc)
      ((hFrame (show GateRecordLane.gate .lookupWork ≠ .remaining by decide)).trans hLookup)
      ((hFrame (show GateRecordLane.gate .scratch ≠ .remaining by decide)).trans hScratch) hCap (by
        simpa only [Function.comp_apply, fieldLanes, hPosition] using hRead)
  simp only [Function.comp_apply, fieldLanes] at hCount hPos hVal hUnchanged
  have hState : after = decodedFieldValues lanes field bits before := by
    funext reg
    by_cases hPosLane : reg = lanes .position
    · subst reg
      simpa only [decodedFieldValues, setValue_same, hPosition] using hPos
    by_cases hAccLane : reg = lanes (.gate field.target)
    · subst reg
      simpa only [decodedFieldValues, setValue_other hPosLane, setValue_same] using hVal
    by_cases hCountLane : reg = lanes .remaining
    · subst reg
      simpa only [decodedFieldValues, setValue_other hPosLane, setValue_other hAccLane, hRemaining]
        using hCount
    · rw [hUnchanged reg hPosLane hCountLane hAccLane]
      simp only [decodedFieldValues, loaded, setValue_other hPosLane, setValue_other hAccLane,
        setValue_other hCountLane]
  exact ⟨setupTicks + ticks, Nat.add_le_add_left hTicks _, hState ▸ hSetup.seq hRun⟩

private theorem runsValues_loadRecordWidth (lanes : GateRecordLane → R)
    (hLanes : Function.Injective lanes) (word : BinaryWord) (before : R → Nat)
    (width : Nat) (hWidth : before (lanes .width) = width)
    (hRemaining : before (lanes .remaining) = 0) (hScratch : before (lanes (.gate .scratch)) = 0) :
    (loadRecordWidth lanes).RunsValues word (5 * width + 2) before
      (setValue (lanes .remaining) width before) := by
  have hNe {a b : GateRecordLane} (hne : a ≠ b) : lanes a ≠ lanes b := fun eq ↦ hne (hLanes eq)
  have hRun := runsValues_add (lanes .width) (lanes .remaining) (lanes (.gate .scratch))
    word before (hNe (by decide)) (hNe (by decide)) (hNe (by decide)) hScratch
  simpa only [loadRecordWidth, hWidth, hRemaining, Nat.zero_add] using hRun

/-- The register fragment reads and checks one record, then restores the scratch lanes. -/
theorem runsValues_checkGateRecordRegister {lanes : GateRecordLane → R}
    (hLanes : Function.Injective lanes) {word trace tag left right : BinaryWord}
    {before : R → Nat} (hReady : GateRecordReady lanes word trace before)
    (hLayout : GateRecordLayout word (before (lanes .position)) (before (lanes .width))
      tag left right)
    (hLeft : fieldValue left ≤ word.length) (hRight : fieldValue right ≤ word.length) :
    ∃ ticks ≤ gateRecordCost word.length (before (lanes .width)), ∃ after,
      (checkGateRecordRegister lanes).RunsValues word ticks before after ∧
        GateRecordResult lanes trace tag left right before after := by
  have hLane (a b : GateRecordLane) : lanes a = lanes b ↔ a = b :=
    ⟨fun h ↦ hLanes h, congrArg lanes⟩
  have hGateLanes : Function.Injective (lanes ∘ GateRecordLane.gate) :=
    hLanes.comp (fun _ _ h ↦ GateRecordLane.gate.inj h)
  let afterRight := decodedFieldValues lanes .right right before
  let afterLeft := decodedFieldValues lanes .left left afterRight
  let afterTag := decodedFieldValues lanes .opcode tag afterLeft
  have hLookup := hReady.gate.lookupWork_zero
  have hScratch := hReady.gate.scratch_zero
  change before (lanes (.gate .lookupWork)) = 0 at hLookup
  change before (lanes (.gate .scratch)) = 0 at hScratch
  obtain ⟨rightTicks, hRightTicks, hRunRight⟩ := runsValues_recordField lanes hLanes .right
    word right word.length before _ _
    (runsValues_loadRecordWidth lanes hLanes word before right.length hLayout.right_length.symm
      hReady.remaining_zero hScratch)
    hReady.remaining_zero hReady.right_zero hLookup hScratch hRight hLayout.read_right
  have hRightFrame {k : GateRecordLane} (hp : k ≠ .position) (hr : k ≠ .gate .right) :
      afterRight (lanes k) = before (lanes k) := by
    simp [afterRight, decodedFieldValues, RecordField.target, setValue, hLane, hp, hr]
  have hLeftRemaining := (hRightFrame (by decide) (by decide)).trans hReady.remaining_zero
  have hLeftAcc := (hRightFrame (by decide) (by decide)).trans hReady.left_zero
  have hLeftLookup := (hRightFrame (by decide) (by decide)).trans hLookup
  have hLeftScratch := (hRightFrame (by decide) (by decide)).trans hScratch
  have hLeftWidth :=
    (hRightFrame (k := .width) (by decide) (by decide)).trans hLayout.left_length.symm
  obtain ⟨leftTicks, hLeftTicks, hRunLeft⟩ := runsValues_recordField lanes hLanes .left
    word left word.length afterRight _ _
    (runsValues_loadRecordWidth lanes hLanes word afterRight left.length hLeftWidth
      hLeftRemaining hLeftScratch)
    hLeftRemaining hLeftAcc hLeftLookup hLeftScratch hLeft (by
      intro i hi
      simpa only [afterRight, decodedFieldValues, setValue_same] using hLayout.read_left i hi)
  have hOperandsFrame {k : GateRecordLane} (hp : k ≠ .position) (hr : k ≠ .gate .right)
      (hl : k ≠ .gate .left) : afterLeft (lanes k) = before (lanes k) := by
    simp [afterLeft, decodedFieldValues, RecordField.target, setValue, hLane, hp, hl,
      hRightFrame hp hr]
  have hTagRemaining := (hOperandsFrame (by decide) (by decide) (by decide)).trans
    hReady.remaining_zero
  have hTagAcc := (hOperandsFrame (by decide) (by decide) (by decide)).trans hReady.opcode_zero
  have hTagLookup := (hOperandsFrame (by decide) (by decide) (by decide)).trans hLookup
  have hTagScratch := (hOperandsFrame (by decide) (by decide) (by decide)).trans hScratch
  have hTagValue : fieldValue tag < 8 := by
    have hPow : (2 : Nat) ^ 3 = 8 := by decide
    simpa only [hLayout.tag_length, hPow] using fieldValue_lt_pow_length tag
  have hTagSetup : (incrementBy (lanes .remaining) 3).RunsValues word 3 afterLeft
      (setValue (lanes .remaining) tag.length afterLeft) := by
    simpa only [hTagRemaining, hLayout.tag_length, Nat.zero_add] using
      runsValues_incrementBy (lanes .remaining) 3 word afterLeft
  obtain ⟨tagTicks, hTagTicks, hRunTag⟩ := runsValues_recordField lanes hLanes .opcode
    word tag 7 afterLeft _ _ hTagSetup hTagRemaining hTagAcc hTagLookup hTagScratch
    (Nat.le_of_lt_succ hTagValue) (by
      intro i hi
      simpa only [afterLeft, afterRight, decodedFieldValues, setValue_same] using
        hLayout.read_tag i hi)
  have hTaggedFrame {k : GateCheckLane} (ho : k ≠ .opcode) (hr : k ≠ .right) (hl : k ≠ .left) :
      afterTag (lanes (.gate k)) = before (lanes (.gate k)) := by
    have hEarlier := hOperandsFrame (k := .gate k) (by simp) (by simpa) (by simpa)
    simp [afterTag, decodedFieldValues, RecordField.target, setValue, hLane, ho,
      hEarlier]
  have hDestination := hTaggedFrame (k := .destination) (by decide) (by decide) (by decide)
  have hFailure := hTaggedFrame (k := .failures) (by decide) (by decide) (by decide)
  have hTraceStart := hTaggedFrame (k := .traceStart) (by decide) (by decide) (by decide)
  have hDecodedLeft : afterTag (lanes (.gate .left)) = fieldValue left := by
    simp [afterTag, afterLeft, decodedFieldValues, RecordField.target, setValue, hLane]
  have hDecodedRight : afterTag (lanes (.gate .right)) = fieldValue right := by
    simp [afterTag, afterLeft, afterRight, decodedFieldValues, RecordField.target, setValue, hLane]
  have hDecodedTag : afterTag (lanes (.gate .opcode)) = fieldValue tag := by
    simp [afterTag, decodedFieldValues, RecordField.target, setValue, hLane]
  have hGateReady : GateCheckReady (lanes ∘ GateRecordLane.gate) word trace afterTag := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (hTaggedFrame (by decide) (by decide) (by decide)).trans hReady.gate.inputLength
    · exact hTraceStart ▸ hReady.gate.traceStart_le
    · exact hDestination ▸ hReady.gate.destination_le
    · exact hDecodedLeft ▸ hLeft
    · exact hDecodedRight ▸ hRight
    · exact hDestination ▸ hReady.gate.destination_lt
    · simpa only [Function.comp_apply, hTraceStart] using hReady.gate.readWire
    · exact (hTaggedFrame (by decide) (by decide) (by decide)).trans hReady.gate.address_zero
    · exact (hTaggedFrame (by decide) (by decide) (by decide)).trans hLookup
    · exact (hTaggedFrame (by decide) (by decide) (by decide)).trans hReady.gate.multiplier_zero
    · exact (hTaggedFrame (by decide) (by decide) (by decide)).trans hScratch
    · exact (hTaggedFrame (by decide) (by decide) (by decide)).trans hReady.gate.zero
  have hOpcode : afterTag (lanes (.gate .opcode)) < 8 := hDecodedTag ▸ hTagValue
  let key : Fin 8 := ⟨afterTag (lanes (.gate .opcode)), hOpcode⟩
  have hPasses : checkDecodedGate trace (afterTag (lanes (.gate .destination)))
      (afterTag (lanes (.gate .left))) (afterTag (lanes (.gate .right))) key =
      gateRecordPasses trace (before (lanes (.gate .destination))) tag left right := by
    rw [checkDecodedGate_eq_gateFromFields]
    let interpret (destination opcode lhs rhs : Nat) :=
      ((gateFromFields destination opcode lhs rhs).map fun gate ↦
        gate.traceInstruction.checkAt destination trace).getD false
    change interpret (afterTag (lanes (.gate .destination))) (afterTag (lanes (.gate .opcode)))
      (afterTag (lanes (.gate .left))) (afterTag (lanes (.gate .right))) =
        interpret (before (lanes (.gate .destination))) (fieldValue tag)
          (fieldValue left) (fieldValue right)
    rw [hDestination, hDecodedTag, hDecodedLeft, hDecodedRight]
  obtain ⟨gateTicks, hGateTicks, hRunGate⟩ :=
    runsValues_checkGateRegister hGateLanes hGateReady hOpcode
  let failures := before (lanes (.gate .failures)) +
    if gateRecordPasses trace (before (lanes (.gate .destination))) tag left right then 0 else 1
  let checked := setValue (lanes (.gate .failures)) failures
    (clearValues (lanes (.gate .opcode)) afterTag)
  have hCheck : (checkGateRegister (lanes ∘ GateRecordLane.gate)).RunsValues word gateTicks
      afterTag checked := by
    change (checkGateRegister (lanes ∘ GateRecordLane.gate)).RunsValues word gateTicks afterTag
      (setValue (lanes (.gate .failures)) (afterTag (lanes (.gate .failures)) +
        if checkDecodedGate trace (afterTag (lanes (.gate .destination)))
          (afterTag (lanes (.gate .left))) (afterTag (lanes (.gate .right))) key then 0 else 1)
        (clearValues (lanes (.gate .opcode)) afterTag)) at hRunGate
    rw [hFailure, hPasses] at hRunGate
    exact hRunGate
  let clearedLeft := clearValues (lanes (.gate .left)) checked
  let clearedRight := clearValues (lanes (.gate .right)) clearedLeft
  let after := decrementValues (lanes (.gate .destination)) clearedRight
  have hClear := ((runsValues_clearLane (lanes (.gate .left)) word checked).seq
    (runsValues_clearLane (lanes (.gate .right)) word clearedLeft)).seq
      (runsValues_decrementLane (lanes (.gate .destination)) word clearedRight)
  have hLeftValue : checked (lanes (.gate .left)) = fieldValue left := by
    simp [checked, setValue, clearValues, hLane, hDecodedLeft]
  have hRightValue : clearedLeft (lanes (.gate .right)) = fieldValue right := by
    simp [clearedLeft, checked, setValue, clearValues, hLane, hDecodedRight]
  have hCost : rightTicks + leftTicks + tagTicks +
      (gateTicks + (checked (lanes (.gate .left)) + 1 + (clearedLeft (lanes (.gate .right)) + 1) +
        1)) ≤ gateRecordCost word.length (before (lanes .width)) := by
    rw [hLayout.right_length] at hRightTicks
    rw [hLayout.left_length] at hLeftTicks
    rw [hLayout.tag_length] at hTagTicks
    unfold gateRecordCost
    omega
  have hRun := ((hRunRight.seq hRunLeft).seq hRunTag).seq (hCheck.seq hClear)
  refine ⟨_, hCost, after, ?_, ?_⟩
  · exact hRun
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simp [after, clearedRight, clearedLeft, checked, afterTag, afterLeft, afterRight,
        decrementValues, clearValues, setValue, hLane, decodedFieldValues,
        hLayout.left_length, hLayout.right_length, hLayout.tag_length]
      omega
    · simp [after, clearedRight, clearedLeft, checked, decrementValues, clearValues, setValue,
        hLane, hDestination]
    · simp [after, clearedRight, clearedLeft, checked, decrementValues, clearValues, setValue,
        hLane, failures]
    · intro reg hPosition hDest hFailures
      by_cases hl : reg = lanes (.gate .left)
      · subst reg
        simp [after, clearedRight, clearedLeft, decrementValues, clearValues, hLane,
          hReady.left_zero]
      by_cases hr : reg = lanes (.gate .right)
      · subst reg
        simp [after, clearedRight, decrementValues, clearValues, hLane, hReady.right_zero]
      by_cases ho : reg = lanes (.gate .opcode)
      · subst reg
        simp [after, clearedRight, clearedLeft, checked, decrementValues, clearValues, setValue,
          hLane, hReady.opcode_zero]
      · simp [after, clearedRight, clearedLeft, checked, afterTag, afterLeft, afterRight,
          decrementValues, clearValues, setValue, decodedFieldValues, RecordField.target,
          hPosition, hDest, hFailures, hl, hr, ho]

end PvsNP.MCSP
