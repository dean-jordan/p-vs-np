module

public import PvsNP.MCSP.GateBlockRegister

import all PvsNP.MCSP.GateBlockRegister
import all PvsNP.MCSP.GateRegister
import all PvsNP.MCSP.GateRecordRegister
import all PvsNP.TuringMachine.Registers.BinaryCompare
import Mathlib.Tactic.FinCases

/-! # Counted validation of gate records without a supplied wire trace -/

public section

namespace PvsNP.MCSP

open Circuits RegisterMachine RegisterMachine.Fragment

variable {R : Type}

/-- The structural checker only uses numeric fields and zeroed comparison scratch. -/
structure GateStructureReady (lanes : GateCheckLane → R) (word : BinaryWord)
    (v : R → Nat) : Prop where
  destination_le : v (lanes .destination) ≤ word.length
  left_le : v (lanes .left) ≤ word.length
  right_le : v (lanes .right) ≤ word.length
  address_zero : v (lanes .address) = 0
  lookup_zero : v (lanes .lookupWork) = 0
  scratch_zero : v (lanes .scratch) = 0
  zero : v (lanes .zero) = 0

private def requireEarlier (lanes : GateCheckLane → R) (op : Operand)
    (body : Fragment R) : Fragment R :=
  ifLess (lanes op.lane) (lanes .destination) (lanes .address) (lanes .lookupWork)
    (lanes .scratch) body (countFailure lanes false)

private def structureBranch (lanes : GateCheckLane → R) (opcode : Fin 8) : Fragment R :=
  match opcode.val with
  | 0 => requireZero lanes .left (requireZero lanes .right skip)
  | 1 => requireEarlier lanes .left (requireEarlier lanes .right skip)
  | 2 => requireZero lanes .right (requireEarlier lanes .left skip)
  | 4 => requireZero lanes .left (requireZero lanes .right skip)
  | 6 => requireEarlier lanes .left (requireEarlier lanes .right skip)
  | _ => countFailure lanes false

/-- Check a decoded opcode, unused fields, and bounds on wire references. -/
def checkGateStructureRegister (lanes : GateCheckLane → R) : Fragment R :=
  dispatchFin (lanes .opcode) (structureBranch lanes)

@[expose] def gateStructureCost (length : Nat) : Nat := 24 * length + 21

variable [DecidableEq R]

omit [DecidableEq R] in
private theorem structureOperandBound {lanes : GateCheckLane → R} {x : BinaryWord}
    {v : R → Nat} (h : GateStructureReady lanes x v) (operand : Operand) :
    v (lanes operand.lane) ≤ x.length := by
  cases operand
  · exact h.left_le
  · exact h.right_le

private theorem runStructureRequireEarlier {lanes : GateCheckLane → R}
    (hLanes : Function.Injective lanes) {x : BinaryWord} {v : R → Nat}
    (h : GateStructureReady lanes x v) (operand : Operand) (body : Fragment R)
    (passes : Bool) {cost : Nat} (hCost : 1 ≤ cost)
    (hBody : BoundedRun body x cost v (recordFailure lanes passes v)) :
    BoundedRun (requireEarlier lanes operand body) x (12 * x.length + 6 + cost) v
      (recordFailure lanes
        (decide (v (lanes operand.lane) < v (lanes .destination)) && passes) v) := by
  let source := v (lanes operand.lane)
  let destination := v (lanes .destination)
  let outcome := recordFailure lanes (decide (source < destination) && passes) v
  have hSelected : BoundedRun (if source < destination then body else countFailure lanes false)
      x cost v outcome := by
    by_cases hLess : source < destination
    · simpa only [ite_eq_left hLess, outcome, decide_eq_true hLess, Bool.true_and] using hBody
    · obtain ⟨ticks, hTicks, hRun⟩ := runCountFailure lanes false x v
      refine ⟨ticks, hTicks.trans hCost, ?_⟩
      simpa only [ite_eq_right hLess, outcome, decide_eq_false hLess, Bool.false_and] using hRun
  obtain ⟨ticks, hTicks, hRun⟩ := hSelected
  refine ⟨ifEqualTime source destination + ticks, ?_, ?_⟩
  · have hSource := structureOperandBound h operand
    have hDestination := h.destination_le
    unfold ifEqualTime source destination
    omega
  · exact runsValues_ifLess (lanes ∘ comparisonLanes operand false)
      (hLanes.comp (comparisonLanes_injective operand false)) _ _ x v
      h.address_zero h.lookup_zero h.scratch_zero hRun

private theorem runStructureRequireZero {lanes : GateCheckLane → R}
    (hLanes : Function.Injective lanes) {x : BinaryWord} {v : R → Nat}
    (h : GateStructureReady lanes x v) (operand : Operand) (body : Fragment R)
    (passes : Bool) {cost : Nat} (hCost : 1 ≤ cost)
    (hBody : BoundedRun body x cost v (recordFailure lanes passes v)) :
    BoundedRun (requireZero lanes operand body) x (12 * x.length + 6 + cost) v
      (recordFailure lanes (decide (v (lanes operand.lane) = 0) && passes) v) := by
  let source := v (lanes operand.lane)
  let outcome := recordFailure lanes (decide (source = 0) && passes) v
  have hSelected : BoundedRun (if v (lanes .zero) < source then countFailure lanes false
      else body) x cost v outcome := by
    by_cases hZero : source = 0
    · simpa only [h.zero, hZero, Nat.lt_irrefl, ite_false, outcome, decide_true, Bool.true_and]
        using hBody
    · obtain ⟨ticks, hTicks, hRun⟩ := runCountFailure lanes false x v
      have hPos : 0 < source := Nat.pos_of_ne_zero hZero
      refine ⟨ticks, hTicks.trans hCost, ?_⟩
      simpa only [h.zero, hPos, ite_true, outcome, decide_eq_false hZero, Bool.false_and] using hRun
  obtain ⟨ticks, hTicks, hRun⟩ := hSelected
  refine ⟨ifEqualTime (v (lanes .zero)) source + ticks, ?_, ?_⟩
  · have hSource := structureOperandBound h operand
    unfold ifEqualTime source
    rw [h.zero]
    omega
  · exact runsValues_ifLess (lanes ∘ comparisonLanes operand true)
      (hLanes.comp (comparisonLanes_injective operand true)) _ _ x v
      h.address_zero h.lookup_zero h.scratch_zero hRun

private theorem runStructureBranch {lanes : GateCheckLane → R} (hLanes : Function.Injective lanes)
    {x : BinaryWord} {v : R → Nat} (h : GateStructureReady lanes x v) (key : Fin 8) :
    BoundedRun (structureBranch lanes key) x (24 * x.length + 13) v
      (recordFailure lanes (gateFromFields (v (lanes .destination)) key.val
        (v (lanes .left)) (v (lanes .right))).isSome v) := by
  have hPass : BoundedRun skip x 1 v (recordFailure lanes true v) := by
    have hSame : recordFailure lanes true v = v := by
      funext k
      by_cases hk : k = lanes .failures <;> simp [recordFailure, setValue, hk]
    exact ⟨0, by decide, hSame.symm ▸ runsValues_skip x v⟩
  have hConstant := runStructureRequireZero hLanes h .left _ _ (by omega)
    (runStructureRequireZero hLanes h .right _ _ (by decide) hPass)
  have hNot := runStructureRequireZero hLanes h .right _ _ (by omega)
    (runStructureRequireEarlier hLanes h .left _ _ (by decide) hPass)
  have hBinary := runStructureRequireEarlier hLanes h .left _ _ (by omega)
    (runStructureRequireEarlier hLanes h .right _ _ (by decide) hPass)
  have hReject : BoundedRun (countFailure lanes false) x (24 * x.length + 13) v
      (recordFailure lanes false v) := by
    obtain ⟨ticks, hTicks, hRun⟩ := runCountFailure lanes false x v
    exact ⟨ticks, by omega, hRun⟩
  have hConstPass (op : Fin 8) (hOp : op.val = 0 ∨ op.val = 4) :
      (gateFromFields (v (lanes .destination)) op.val (v (lanes .left)) (v (lanes .right))).isSome =
        (decide (v (lanes .left) = 0) && decide (v (lanes .right) = 0)) := by
    rcases hOp with ho | ho <;>
      by_cases hl : v (lanes .left) = 0 <;> by_cases hr : v (lanes .right) = 0 <;>
      simp [ho, gateFromFields, hl, hr]
  have hBinaryPass (op : Fin 8) (hOp : op.val = 1 ∨ op.val = 6) :
      (gateFromFields (v (lanes .destination)) op.val (v (lanes .left)) (v (lanes .right))).isSome =
        (decide (v (lanes .left) < v (lanes .destination)) &&
          decide (v (lanes .right) < v (lanes .destination))) := by
    rcases hOp with ho | ho <;>
      by_cases hl : v (lanes .left) < v (lanes .destination) <;>
      by_cases hr : v (lanes .right) < v (lanes .destination) <;>
      simp [ho, gateFromFields, hl, hr]
  have hNotPass :
      (gateFromFields (v (lanes .destination)) 2 (v (lanes .left)) (v (lanes .right))).isSome =
        (decide (v (lanes .right) = 0) && decide (v (lanes .left) < v (lanes .destination))) := by
    by_cases hl : v (lanes .left) < v (lanes .destination) <;>
      by_cases hr : v (lanes .right) = 0 <;> simp [gateFromFields, hl, hr]
  have hBound : 12 * x.length + 6 + (12 * x.length + 6 + 1) = 24 * x.length + 13 := by omega
  simp (config := { instances := true }) only [Operand.lane, Bool.and_true, hBound]
    at hConstant hBinary hNot
  fin_cases key
  · rw [hConstPass _ (by decide)]
    exact hConstant
  · rw [hBinaryPass _ (by decide)]
    exact hBinary
  · rw [hNotPass]
    exact hNot
  · exact hReject
  · rw [hConstPass _ (by decide)]
    exact hConstant
  · exact hReject
  · rw [hBinaryPass _ (by decide)]
    exact hBinary
  · exact hReject

/-- A structural check consumes the opcode and increments failures exactly on invalid fields. -/
theorem runsValues_checkGateStructureRegister {lanes : GateCheckLane → R}
    (hLanes : Function.Injective lanes) {word : BinaryWord} {v : R → Nat}
    (h : GateStructureReady lanes word v) (hOpcode : v (lanes .opcode) < 8) :
    let passes := (gateFromFields (v (lanes .destination)) (v (lanes .opcode))
      (v (lanes .left)) (v (lanes .right))).isSome
    ∃ ticks ≤ gateStructureCost word.length,
      (checkGateStructureRegister lanes).RunsValues word ticks v
        (setValue (lanes .failures) (v (lanes .failures) + (if passes then 0 else 1))
          (clearValues (lanes .opcode) v)) := by
  let key : Fin 8 := ⟨v (lanes .opcode), hOpcode⟩
  let cleared := clearValues (lanes .opcode) v
  have hKeep (lane : GateCheckLane) (hn : lane ≠ .opcode) : cleared (lanes lane) = v (lanes lane) :=
    ite_eq_right (fun e ↦ hn (hLanes e))
  have hReady : GateStructureReady lanes word cleared := by
    exact ⟨hKeep .destination (by decide) ▸ h.destination_le,
      hKeep .left (by decide) ▸ h.left_le, hKeep .right (by decide) ▸ h.right_le,
      (hKeep .address (by decide)).trans h.address_zero,
      (hKeep .lookupWork (by decide)).trans h.lookup_zero,
      (hKeep .scratch (by decide)).trans h.scratch_zero,
      (hKeep .zero (by decide)).trans h.zero⟩
  obtain ⟨bodyTicks, hBodyTicks, hBody⟩ := runStructureBranch hLanes hReady key
  have hPasses : (gateFromFields (cleared (lanes .destination)) key.val
      (cleared (lanes .left)) (cleared (lanes .right))).isSome =
      (gateFromFields (v (lanes .destination)) (v (lanes .opcode))
        (v (lanes .left)) (v (lanes .right))).isSome := by
    let valid (dest left right : Nat) := (gateFromFields dest key.val left right).isSome
    change valid (cleared (lanes .destination)) (cleared (lanes .left)) (cleared (lanes .right)) =
      valid (v (lanes .destination)) (v (lanes .left)) (v (lanes .right))
    rw [hKeep .destination (by decide), hKeep .left (by decide), hKeep .right (by decide)]
  unfold recordFailure at hBody
  rw [hKeep .failures (by decide), hPasses] at hBody
  refine ⟨v (lanes .opcode) + 1 + bodyTicks, by unfold gateStructureCost; omega, ?_⟩
  intro output
  let cfg : Config R Unit := ⟨none, v, none, output⟩
  have hRun := run_dispatchFin (lanes .opcode) (structureBranch lanes) word cfg hOpcode
    (hBody output) rfl
  simpa only [cfg, checkGateStructureRegister, cleared, Config.map,
    dispatchBranchMap, Option.map_none, Option.map_some] using hRun

/-- The lanes needed to scan a raw record. Trace address and length are unused. -/
@[expose] def gateStructureScratchLanes : List GateRecordLane :=
  [.remaining, .gate .left, .gate .right, .gate .opcode, .gate .address,
    .gate .lookupWork, .gate .scratch, .gate .zero]

structure GateStructureRecordReady (lanes : GateRecordLane → R) (word : BinaryWord)
    (values : R → Nat) : Prop where
  destination_le : values (lanes (.gate .destination)) ≤ word.length
  zeroes : ∀ lane ∈ gateStructureScratchLanes, values (lanes lane) = 0

@[expose] def gateStructureRecordPasses (destination : Nat) (record : GateRecordBits) : Bool :=
  (gateFromFields destination record.fields.opcode record.fields.left record.fields.right).isSome

structure GateStructureRecordResult (lanes : GateRecordLane → R) (record : GateRecordBits)
    (before after : R → Nat) : Prop where
  position : after (lanes .position) = before (lanes .position) +
    4 * (3 + 2 * before (lanes .width))
  destination : after (lanes (.gate .destination)) = before (lanes (.gate .destination)) - 1
  failures : after (lanes (.gate .failures)) = before (lanes (.gate .failures)) +
    if gateStructureRecordPasses (before (lanes (.gate .destination))) record then 0 else 1
  frame : ∀ r, r ≠ lanes .position → r ≠ lanes (.gate .destination) →
    r ≠ lanes (.gate .failures) → after r = before r

/-- Read the serialized record, check its numbers, clear the operands, and advance. -/
def checkGateStructureRecord (lanes : GateRecordLane → R) : Fragment R :=
  ((((loadRecordWidth lanes).seq (readRecordField lanes .right)).seq
    ((loadRecordWidth lanes).seq (readRecordField lanes .left))).seq
    ((incrementBy (lanes .remaining) 3).seq (readRecordField lanes .opcode))).seq
      ((checkGateStructureRegister (lanes ∘ GateRecordLane.gate)).seq (clearRecordOperands lanes))

theorem runsValues_checkGateStructureRecord {lanes : GateRecordLane → R}
    (hLanes : Function.Injective lanes) {word : BinaryWord} {record : GateRecordBits}
    {before : R → Nat} (ready : GateStructureRecordReady lanes word before)
    (layout : GateRecordLayout word (before (lanes .position)) (before (lanes .width))
      record.tag record.left record.right)
    (hLeft : fieldValue record.left ≤ word.length)
    (hRight : fieldValue record.right ≤ word.length) :
    ∃ ticks ≤ gateRecordCost word.length (before (lanes .width)), ∃ after,
      (checkGateStructureRecord lanes).RunsValues word ticks before after ∧
        GateStructureRecordResult lanes record before after := by
  have hLane (a b : GateRecordLane) : lanes a = lanes b ↔ a = b :=
    ⟨fun h ↦ hLanes h, congrArg lanes⟩
  have hGateLanes : Function.Injective (lanes ∘ GateRecordLane.gate) :=
    hLanes.comp (fun _ _ h ↦ GateRecordLane.gate.inj h)
  have hZero := ready.zeroes
  have hRemaining := hZero .remaining (by decide)
  have hLookup := hZero (.gate .lookupWork) (by decide)
  have hScratch := hZero (.gate .scratch) (by decide)
  have hOldLeft := hZero (.gate .left) (by decide)
  have hOldRight := hZero (.gate .right) (by decide)
  have hOldOpcode := hZero (.gate .opcode) (by decide)
  let right := decodedFieldValues lanes .right record.right before
  let left := decodedFieldValues lanes .left record.left right
  let decoded := decodedFieldValues lanes .opcode record.tag left
  obtain ⟨rightTicks, hRightTicks, hRunRight⟩ := runsValues_recordField lanes hLanes .right
    word record.right word.length before _ _
    (runsValues_loadRecordWidth lanes hLanes word before record.right.length
      layout.right_length.symm hRemaining hScratch)
    hRemaining hOldRight hLookup hScratch hRight layout.read_right
  have hRightFrame {k : GateRecordLane} (hp : k ≠ .position) (hr : k ≠ .gate .right) :
      right (lanes k) = before (lanes k) := by
    simp [right, decodedFieldValues, RecordField.target, setValue, hLane, hp, hr]
  have hLeftRemaining := (hRightFrame (by decide) (by decide)).trans hRemaining
  have hLeftLookup := (hRightFrame (by decide) (by decide)).trans hLookup
  have hLeftScratch := (hRightFrame (by decide) (by decide)).trans hScratch
  have hLeftAcc := (hRightFrame (by decide) (by decide)).trans hOldLeft
  have hLeftWidth :=
    (hRightFrame (k := .width) (by decide) (by decide)).trans layout.left_length.symm
  obtain ⟨leftTicks, hLeftTicks, hRunLeft⟩ := runsValues_recordField lanes hLanes .left
    word record.left word.length right _ _
    (runsValues_loadRecordWidth lanes hLanes word right record.left.length hLeftWidth
      hLeftRemaining hLeftScratch)
    hLeftRemaining hLeftAcc hLeftLookup hLeftScratch hLeft (by
      intro i hi
      simpa only [right, decodedFieldValues, setValue_same] using layout.read_left i hi)
  have hLeftFrame {k : GateRecordLane} (hp : k ≠ .position) (hr : k ≠ .gate .right)
      (hl : k ≠ .gate .left) : left (lanes k) = before (lanes k) := by
    simp [left, decodedFieldValues, RecordField.target, setValue, hLane, hp, hl,
      hRightFrame hp hr]
  have hTagRemaining := (hLeftFrame (by decide) (by decide) (by decide)).trans hRemaining
  have hTagLookup := (hLeftFrame (by decide) (by decide) (by decide)).trans hLookup
  have hTagScratch := (hLeftFrame (by decide) (by decide) (by decide)).trans hScratch
  have hTagAcc := (hLeftFrame (by decide) (by decide) (by decide)).trans hOldOpcode
  have hTagValue : fieldValue record.tag < 8 := by
    have hPow : (2 : Nat) ^ 3 = 8 := by decide
    simpa only [layout.tag_length, hPow] using fieldValue_lt_pow_length record.tag
  have hSetup : (incrementBy (lanes .remaining) 3).RunsValues word 3 left
      (setValue (lanes .remaining) record.tag.length left) := by
    simpa only [hTagRemaining, layout.tag_length, Nat.zero_add] using
      runsValues_incrementBy (lanes .remaining) 3 word left
  obtain ⟨tagTicks, hTagTicks, hRunTag⟩ := runsValues_recordField lanes hLanes .opcode
    word record.tag 7 left _ _ hSetup hTagRemaining hTagAcc hTagLookup hTagScratch
    (Nat.le_of_lt_succ hTagValue) (by
      intro i hi
      simpa only [left, right, decodedFieldValues, setValue_same] using layout.read_tag i hi)
  have hDecodedFrame {k : GateCheckLane} (ho : k ≠ .opcode) (hr : k ≠ .right) (hl : k ≠ .left) :
      decoded (lanes (.gate k)) = before (lanes (.gate k)) := by
    have hEarlier := hLeftFrame (k := .gate k) (by simp) (by simpa) (by simpa)
    simp [decoded, decodedFieldValues, RecordField.target, setValue, hLane, ho, hEarlier]
  have hDestination := hDecodedFrame (k := .destination) (by decide) (by decide) (by decide)
  have hFailures := hDecodedFrame (k := .failures) (by decide) (by decide) (by decide)
  have hDecodedLeft : decoded (lanes (.gate .left)) = fieldValue record.left := by
    simp [decoded, left, decodedFieldValues, RecordField.target, setValue, hLane]
  have hDecodedRight : decoded (lanes (.gate .right)) = fieldValue record.right := by
    simp [decoded, left, right, decodedFieldValues, RecordField.target, setValue, hLane]
  have hDecodedTag : decoded (lanes (.gate .opcode)) = fieldValue record.tag := by
    simp [decoded, decodedFieldValues, RecordField.target, setValue, hLane]
  have hDecodedReady : GateStructureReady (lanes ∘ GateRecordLane.gate) word decoded := by
    refine ⟨hDestination ▸ ready.destination_le, hDecodedLeft ▸ hLeft, hDecodedRight ▸ hRight,
      ?_, ?_, ?_, ?_⟩
    · exact (hDecodedFrame (by decide) (by decide) (by decide)).trans
        (hZero (.gate .address) (by decide))
    · exact (hDecodedFrame (by decide) (by decide) (by decide)).trans hLookup
    · exact (hDecodedFrame (by decide) (by decide) (by decide)).trans hScratch
    · exact (hDecodedFrame (by decide) (by decide) (by decide)).trans
        (hZero (.gate .zero) (by decide))
  obtain ⟨checkTicks, hCheckTicks, hCheck⟩ :=
    runsValues_checkGateStructureRegister hGateLanes hDecodedReady (hDecodedTag ▸ hTagValue)
  have hPasses : (gateFromFields (decoded (lanes (.gate .destination)))
      (decoded (lanes (.gate .opcode))) (decoded (lanes (.gate .left)))
      (decoded (lanes (.gate .right)))).isSome =
      gateStructureRecordPasses (before (lanes (.gate .destination))) record := by
    let valid (dest op lhs rhs : Nat) := (gateFromFields dest op lhs rhs).isSome
    change valid (decoded (lanes (.gate .destination))) (decoded (lanes (.gate .opcode)))
        (decoded (lanes (.gate .left))) (decoded (lanes (.gate .right))) =
      valid (before (lanes (.gate .destination))) (fieldValue record.tag)
        (fieldValue record.left) (fieldValue record.right)
    rw [hDestination, hDecodedTag, hDecodedLeft, hDecodedRight]
  let failures := before (lanes (.gate .failures)) +
    if gateStructureRecordPasses (before (lanes (.gate .destination))) record then 0 else 1
  let checked := setValue (lanes (.gate .failures)) failures
    (clearValues (lanes (.gate .opcode)) decoded)
  have hRunCheck : (checkGateStructureRegister (lanes ∘ GateRecordLane.gate)).RunsValues word
      checkTicks decoded checked := by
    simpa only [Function.comp_apply, hFailures, hPasses, failures, checked] using hCheck
  let clearedLeft := clearValues (lanes (.gate .left)) checked
  let clearedRight := clearValues (lanes (.gate .right)) clearedLeft
  let after := decrementValues (lanes (.gate .destination)) clearedRight
  have hClear := ((runsValues_clearLane (lanes (.gate .left)) word checked).seq
    (runsValues_clearLane (lanes (.gate .right)) word clearedLeft)).seq
      (runsValues_decrementLane (lanes (.gate .destination)) word clearedRight)
  have hLeftValue : checked (lanes (.gate .left)) = fieldValue record.left := by
    simp [checked, setValue, clearValues, hLane, hDecodedLeft]
  have hRightValue : clearedLeft (lanes (.gate .right)) = fieldValue record.right := by
    simp [clearedLeft, checked, setValue, clearValues, hLane, hDecodedRight]
  have hCost : rightTicks + leftTicks + tagTicks +
      (checkTicks + (checked (lanes (.gate .left)) + 1 +
        (clearedLeft (lanes (.gate .right)) + 1) + 1)) ≤
        gateRecordCost word.length (before (lanes .width)) := by
    rw [layout.right_length] at hRightTicks
    rw [layout.left_length] at hLeftTicks
    rw [layout.tag_length] at hTagTicks
    unfold gateStructureCost at hCheckTicks
    unfold gateRecordCost gateCheckCost
    omega
  refine ⟨_, hCost, after, ((hRunRight.seq hRunLeft).seq hRunTag).seq (hRunCheck.seq hClear),
    ?_, ?_, ?_, ?_⟩
  · simp [after, clearedRight, clearedLeft, checked, decoded, left, right, decrementValues,
      clearValues, setValue, hLane, decodedFieldValues, layout.left_length, layout.right_length,
      layout.tag_length]
    omega
  · simp [after, clearedRight, clearedLeft, checked, decrementValues, clearValues, setValue, hLane,
      hDestination]
  · simp [after, clearedRight, clearedLeft, checked, decrementValues, clearValues, setValue, hLane,
      failures]
  · intro reg hPos hDest hFail
    by_cases hl : reg = lanes (.gate .left)
    · subst reg
      simp [after, clearedRight, clearedLeft, decrementValues, clearValues, hLane, hOldLeft]
    by_cases hr : reg = lanes (.gate .right)
    · subst reg
      simp [after, clearedRight, decrementValues, clearValues, hLane, hOldRight]
    by_cases ho : reg = lanes (.gate .opcode)
    · subst reg
      simp [after, clearedRight, clearedLeft, checked, decrementValues, clearValues, setValue,
        hLane, hOldOpcode]
    · simp [after, clearedRight, clearedLeft, checked, decoded, left, right, decrementValues,
        clearValues, setValue, decodedFieldValues, RecordField.target, hPos, hDest, hFail,
        hl, hr, ho]

private def indexedStructureFailure (arity : Nat) (records : List GateRecordBits)
    (i : Nat) : Nat :=
  (records[i]?.map fun record ↦ if gateStructureRecordPasses (arity + i) record then 0 else 1)
    |>.getD 0

/-- Count malformed gate records in a block with the given initial wire count. -/
def gateStructureFailureCount (arity : Nat) (records : List GateRecordBits) : Nat :=
  ((List.range records.length).map (indexedStructureFailure arity records)).sum

theorem gateStructureFailureCount_eq_zero_iff (arity : Nat) (records : List GateRecordBits) :
    gateStructureFailureCount arity records = 0 ↔
      ∀ (i : Nat) (hi : i < records.length),
        gateStructureRecordPasses (arity + i) records[i] = true := by
  rw [gateStructureFailureCount, List.sum_eq_zero_iff_forall_eq_nat]
  constructor
  · intro h i hi
    have hIndex := h _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    simpa only [indexedStructureFailure, List.getElem?_eq_getElem hi, Option.map_some,
      Option.getD_some, ite_eq_left_iff, Nat.one_ne_zero, imp_false, ne_eq, not_not] using hIndex
  · intro h value hValue
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hValue
    have hIn := List.mem_range.mp hi
    simp only [indexedStructureFailure, List.getElem?_eq_getElem hIn, Option.map_some,
      Option.getD_some, h i hIn, ite_true]

/-- The reverse block can have any serialized fields within their declared widths. -/
structure GateStructureBlockReady (lanes : GateRecordLane → R) (counter : R)
    (word : BinaryWord) (arity : Nat) (records : List GateRecordBits) (v : R → Nat) : Prop where
  count : v counter = records.length
  destination : v (lanes (.gate .destination)) = arity + records.length - 1
  wires_le : arity + records.length ≤ word.length
  zeroes : ∀ lane ∈ gateStructureScratchLanes, v (lanes lane) = 0
  layout : ∀ (i : Fin records.length),
    let width := v (lanes .width)
    let record := records[i]
    GateRecordLayout word (v (lanes .position) + 4 * (3 + 2 * width) *
      (records.length - (i.val + 1))) width record.tag record.left record.right
  operands : ∀ (i : Fin records.length),
    let record := records[i]
    fieldValue record.left ≤ word.length ∧ fieldValue record.right ≤ word.length

def checkGateStructureBlock (lanes : GateRecordLane → R) (counter : R) : Fragment R :=
  countdown counter (checkGateStructureRecord lanes)

/-- A complete scan validates every raw record with the polynomial gate-block clock. -/
theorem runsValues_checkGateStructureBlock {lanes : GateRecordLane → R}
    (hLanes : Function.Injective lanes) {counter : R} (hCounter : ∀ lane, lanes lane ≠ counter)
    {word : BinaryWord} {arity : Nat} {records : List GateRecordBits} {v : R → Nat}
    (ready : GateStructureBlockReady lanes counter word arity records v) :
    ∃ ticks ≤ gateBlockCost word.length (v (lanes .width)) records.length,
      ∃ after, (checkGateStructureBlock lanes counter).RunsValues word ticks v after ∧
        after counter = 0 ∧
        after (lanes .position) =
          v (lanes .position) + 4 * (3 + 2 * v (lanes .width)) * records.length ∧
        after (lanes (.gate .destination)) = arity - 1 ∧
        after (lanes (.gate .failures)) = v (lanes (.gate .failures)) +
          gateStructureFailureCount arity records ∧
        ∀ r, r ≠ counter → r ≠ lanes .position → r ≠ lanes (.gate .destination) →
          r ≠ lanes (.gate .failures) → after r = v r := by
  let body := checkGateStructureRecord lanes
  let loop := countdown counter body
  let stride := 4 * (3 + 2 * v (lanes .width))
  let update := fun total i ↦ total + indexedStructureFailure arity records i
  let Inv := fun (count total : Nat) (values : R → Nat) (cursor : Option Nat)
      (output : BinaryWord) ↦
    count ≤ records.length ∧ cursor = none ∧ output = ([] : BinaryWord) ∧
    values (lanes .position) = v (lanes .position) + stride * (records.length - count) ∧
    values (lanes (.gate .destination)) = arity + count - 1 ∧
    values (lanes (.gate .failures)) = total ∧
    ∀ r, r ≠ counter → r ≠ lanes .position → r ≠ lanes (.gate .destination) →
      r ≠ lanes (.gate .failures) → values r = v r
  have hBody (i acc : Nat) (cfg : loop.Cfg) (hCount : cfg.values counter = i + 1)
      (hInv : Inv (i + 1) acc cfg.values cfg.cursor cfg.output) :
      ∃ ticks ≤ gateRecordCost word.length (v (lanes .width)), ∃ next : body.Cfg,
        body.run word ticks (countdownBodyStart counter body cfg) = some next ∧
        next.pc = some none ∧ next.values counter = i ∧
        Inv i (update acc i) next.values next.cursor next.output := by
    obtain ⟨hCountLe, hCursor, hOutput, hPos, hDest, hFail, hFrame⟩ := hInv
    have hi : i < records.length := by omega
    let record := records[i]
    let tested := decrementValues counter cfg.values
    have unaffected (lane : GateRecordLane) : tested (lanes lane) = cfg.values (lanes lane) :=
      ite_eq_right (hCounter lane)
    have stable (lane : GateRecordLane) (hp : lane ≠ .position)
        (hd : lane ≠ .gate .destination) (hf : lane ≠ .gate .failures) :
        tested (lanes lane) = v (lanes lane) :=
      (unaffected lane).trans (hFrame _ (hCounter lane) (fun e ↦ hp (hLanes e))
        (fun e ↦ hd (hLanes e)) (fun e ↦ hf (hLanes e)))
    have hDest' : tested (lanes (.gate .destination)) = arity + i := by
      rw [unaffected, hDest]
      omega
    have hPos' := (unaffected .position).trans hPos
    have hWidth := stable .width (by decide) (by decide) (by decide)
    have hChecked : GateStructureRecordReady lanes word tested := by
      refine ⟨?_, ?_⟩
      · have hWires := ready.wires_le
        omega
      · intro lane hLane
        have hPosNe : lane ≠ .position := by
          rintro rfl
          simp [gateStructureScratchLanes] at hLane
        have hDestNe : lane ≠ .gate .destination := by
          rintro rfl
          simp [gateStructureScratchLanes] at hLane
        have hFailNe : lane ≠ .gate .failures := by
          rintro rfl
          simp [gateStructureScratchLanes] at hLane
        exact (stable lane hPosNe hDestNe hFailNe).trans (ready.zeroes lane hLane)
    have hLayout : GateRecordLayout word (tested (lanes .position)) (tested (lanes .width))
        record.tag record.left record.right := by
      rw [hPos', hWidth]
      exact ready.layout ⟨i, hi⟩
    have hFields := ready.operands ⟨i, hi⟩
    obtain ⟨ticks, hTicks, after, hRun, hResult⟩ :=
      runsValues_checkGateStructureRecord hLanes hChecked hLayout hFields.1 hFields.2
    let next : body.Cfg := ⟨some none, after, none, cfg.output⟩
    have hSame : next.values counter = i := by
      change after counter = i
      rw [hResult.frame _ (hCounter .position).symm (hCounter (.gate .destination)).symm
        (hCounter (.gate .failures)).symm]
      simp [tested, decrementValues, hCount]
    refine ⟨ticks, (by rwa [hWidth] at hTicks), next, ?_, rfl, hSame, ?_⟩
    · simpa only [body, next, tested, countdownBodyStart, enter, hCursor] using hRun cfg.output
    · refine ⟨by omega, rfl, hOutput, ?_, ?_, ?_, ?_⟩
      · change after (lanes .position) = _
        rw [hResult.position, hPos', hWidth]
        change v (lanes .position) + stride * (records.length - (i + 1)) + stride = _
        rw [Nat.add_assoc, ← Nat.mul_succ,
          show (records.length - (i + 1)).succ = records.length - i by omega]
      · change after (lanes (.gate .destination)) = _
        rw [hResult.destination, hDest']
      · change after (lanes (.gate .failures)) = _
        rw [hResult.failures, unaffected, hFail, hDest']
        simp only [update, indexedStructureFailure, List.getElem?_eq_getElem hi,
          Option.map_some, Option.getD_some, record]
      · intro r hc hp hd hf
        change after r = v r
        rw [hResult.frame _ hp hd hf]
        simpa only [tested, decrementValues, ite_eq_right hc] using hFrame r hc hp hd hf
  let start : loop.Cfg := ⟨some (some none), v, none, []⟩
  have hInitial : Inv records.length (v (lanes (.gate .failures)))
      start.values start.cursor start.output := by
    refine ⟨Nat.le_refl _, rfl, rfl, ?_, ready.destination, rfl, fun _ _ _ _ _ ↦ rfl⟩
    simp [start]
  obtain ⟨costs, _, hCost, next, hRun, hExit, hZero, hInv⟩ :=
    run_countdown_model (counter := counter) (body := body) (x := word)
      update Inv (gateRecordCost word.length (v (lanes .width))) hBody
      (cfg := start) rfl ready.count hInitial
  obtain ⟨_, hCursor, hOutput, hPos, hDest, hFail, hFrame⟩ := hInv
  refine ⟨records.length + costs.sum + 1, hCost, next.values, ?_, hZero, ?_, ?_, ?_, hFrame⟩
  · intro output
    have hSuffix := run_withOutputSuffix loop.close word output (records.length + costs.sum + 1)
      start
    change run loop.close word _ start = some next at hRun
    rw [hRun] at hSuffix
    change run loop.close word _ (withOutputSuffix start output) =
      some (withOutputSuffix next output) at hSuffix
    have hNext : withOutputSuffix next output = ⟨some none, next.values, none, output⟩ := by
      cases next
      simp_all [withOutputSuffix]
    rw [hNext] at hSuffix
    exact hSuffix
  · simpa only [Nat.sub_zero, stride] using hPos
  · simpa only [Nat.add_zero] using hDest
  · have hFold := foldl_add_indexed (indexedStructureFailure arity records)
      (List.range records.length).reverse (v (lanes (.gate .failures)))
    rw [List.map_reverse, List.sum_reverse_nat] at hFold
    exact hFail.trans hFold

end PvsNP.MCSP
