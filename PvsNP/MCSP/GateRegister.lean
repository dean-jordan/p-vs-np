module

public import PvsNP.Circuits.WireTrace
public import PvsNP.Circuits.DescriptionLayout
public import PvsNP.TuringMachine.Registers.AffineLookup
public import PvsNP.TuringMachine.Registers.Dispatch
public import PvsNP.TuringMachine.Registers.LessThan

import Mathlib.Tactic.FinCases

/-! # Checking a gate against the packed wire trace -/

public section

namespace PvsNP.MCSP

open Circuits RegisterMachine RegisterMachine.Fragment

/-- The gate fields and scratch registers used by one verification step. -/
inductive GateCheckLane where
  | inputLength | traceStart | destination | left | right | opcode | failures
  | address | lookupWork | multiplier | scratch | zero
  deriving DecidableEq

private inductive Operand where
  | left | right

private def Operand.lane : Operand → GateCheckLane
  | .left => .left
  | .right => .right

private def wireReadLanes (wire : GateCheckLane) : Fin 7 → GateCheckLane
  | 0 => .inputLength
  | 1 => .traceStart
  | 2 => wire
  | 3 => .address
  | 4 => .lookupWork
  | 5 => .multiplier
  | _ => .scratch

private theorem wireReadLanes_injective (wire : GateCheckLane)
    (hWire : wire = .destination ∨ wire = .left ∨ wire = .right) :
    Function.Injective (wireReadLanes wire) := by
  rcases hWire with rfl | rfl | rfl <;> decide

private def comparisonLanes (operand : Operand) (checkZero : Bool) : Fin 5 → GateCheckLane
  | 0 => if checkZero then .zero else operand.lane
  | 1 => if checkZero then operand.lane else .destination
  | 2 => .address
  | 3 => .lookupWork
  | _ => .scratch

private theorem comparisonLanes_injective (operand : Operand) (checkZero : Bool) :
    Function.Injective (comparisonLanes operand checkZero) := by
  cases operand <;> cases checkZero <;> decide

variable {R : Type}

/-- Trace bit `i` is the data bit of a two-bit block in the outer certificate. -/
structure GateCheckReady (lanes : GateCheckLane → R) (word trace : BinaryWord)
    (values : R → Nat) : Prop where
  inputLength : values (lanes .inputLength) = word.length
  traceStart_le : values (lanes .traceStart) ≤ word.length
  destination_le : values (lanes .destination) ≤ word.length
  left_le : values (lanes .left) ≤ word.length
  right_le : values (lanes .right) ≤ word.length
  destination_lt : values (lanes .destination) < trace.length
  readWire : ∀ i, i < trace.length → word[values (lanes .traceStart) + 2 * i]? = (trace)[i]?
  address_zero : values (lanes .address) = 0
  lookupWork_zero : values (lanes .lookupWork) = 0
  multiplier_zero : values (lanes .multiplier) = 0
  scratch_zero : values (lanes .scratch) = 0
  zero : values (lanes .zero) = 0

private def readWire (lanes : GateCheckLane → R) (wire : GateCheckLane)
    (body : Option Bool → Fragment R) : Fragment R :=
  affineLookup 2 (lanes ∘ wireReadLanes wire) body

private def readEarlierWire (lanes : GateCheckLane → R) (operand : Operand)
    (body : Option Bool → Fragment R) : Fragment R :=
  ifLess (lanes operand.lane) (lanes .destination) (lanes .address) (lanes .lookupWork)
    (lanes .scratch) (readWire lanes operand.lane body) (body none)

private def countFailure (lanes : GateCheckLane → R) (passes : Bool) : Fragment R :=
  incrementBy (lanes .failures) (if passes then 0 else 1)

private def requireZero (lanes : GateCheckLane → R) (operand : Operand) (body : Fragment R) :
    Fragment R :=
  ifLess (lanes .zero) (lanes operand.lane) (lanes .address) (lanes .lookupWork)
    (lanes .scratch) (countFailure lanes false) body

private def agreesWith (expected actual : Option Bool) : Bool :=
  expected.isSome && (actual == expected)

private def checkOutput (lanes : GateCheckLane → R) (expected : Option Bool) : Fragment R :=
  readWire lanes .destination (fun value ↦ countFailure lanes (agreesWith expected value))

private def checkConstant (lanes : GateCheckLane → R) (bit : Bool) : Fragment R :=
  requireZero lanes .left (requireZero lanes .right (checkOutput lanes (some bit)))

private def checkNot (lanes : GateCheckLane → R) : Fragment R :=
  requireZero lanes .right
    (readEarlierWire lanes .left fun value ↦ checkOutput lanes (value.map (!·)))

private def binaryOutput (op : BinaryOp) (a b : Option Bool) : Option Bool := do
  return op.eval (← a) (← b)

private def checkBinary (lanes : GateCheckLane → R) (op : BinaryOp) : Fragment R :=
  readEarlierWire lanes .left fun left ↦
    readEarlierWire lanes .right fun right ↦ checkOutput lanes (binaryOutput op left right)

private def gateBranch (lanes : GateCheckLane → R) : Fin 8 → Fragment R
  | 0 => checkConstant lanes false
  | 1 => checkBinary lanes .or
  | 2 => checkNot lanes
  | 4 => checkConstant lanes true
  | 6 => checkBinary lanes .and
  | _ => countFailure lanes false

/-- Check one decoded three-bit opcode and its two operand fields. The opcode
lane is consumed, and a failed check increments `failures` once. -/
def checkGateRegister (lanes : GateCheckLane → R) : Fragment R :=
  dispatchFin (lanes .opcode) (gateBranch lanes)

@[expose] def gateCheckCost (length : Nat) : Nat := 100 * length + 70

/-- The local check for a three-bit opcode, including its operand and trace requirements. -/
def checkDecodedGate (trace : BinaryWord) (destination left right : Nat) : Fin 8 → Bool
  | 0 => decide (left = 0 ∧ right = 0) && agreesWith (some false) (trace)[destination]?
  | 1 => agreesWith (binaryOutput .or (WireTraceInstruction.readEarlier trace destination left)
      (WireTraceInstruction.readEarlier trace destination right)) (trace)[destination]?
  | 2 => decide (right = 0) && agreesWith
      ((WireTraceInstruction.readEarlier trace destination left).map (!·)) (trace)[destination]?
  | 4 => decide (left = 0 ∧ right = 0) && agreesWith (some true) (trace)[destination]?
  | 6 => agreesWith (binaryOutput .and (WireTraceInstruction.readEarlier trace destination left)
      (WireTraceInstruction.readEarlier trace destination right)) (trace)[destination]?
  | _ => false

private theorem checkAt_eq_agreesWith (op : WireTraceInstruction) (trace : BinaryWord)
    (destination : Nat) : op.checkAt destination trace =
    agreesWith (op.expected destination trace) (trace)[destination]? := by
  unfold WireTraceInstruction.checkAt
  cases (trace)[destination]? <;> cases op.expected destination trace <;> rfl

/-- The finite register dispatch matches the codec's validation and the trace relation. -/
theorem checkDecodedGate_eq_gateFromFields (trace : BinaryWord) (destination left right : Nat)
    (opcode : Fin 8) : checkDecodedGate trace destination left right opcode =
      ((gateFromFields destination opcode.val left right).map fun gate ↦
        gate.traceInstruction.checkAt destination trace).getD false := by
  fin_cases opcode
  · by_cases h : left = 0 ∧ right = 0 <;>
      simp [checkDecodedGate, gateFromFields, h, Gate.traceInstruction, checkAt_eq_agreesWith,
        WireTraceInstruction.expected]
  · by_cases hLeft : left < destination <;> by_cases hRight : right < destination <;>
      simp [checkDecodedGate, gateFromFields, hLeft, hRight, Gate.traceInstruction,
        checkAt_eq_agreesWith, WireTraceInstruction.expected, WireTraceInstruction.readEarlier,
        binaryOutput, agreesWith]
  · by_cases hLeft : left < destination <;> by_cases hRight : right = 0 <;>
      simp [checkDecodedGate, gateFromFields, hLeft, hRight, Gate.traceInstruction,
        checkAt_eq_agreesWith, WireTraceInstruction.expected, WireTraceInstruction.readEarlier,
        agreesWith]
  · rfl
  · by_cases h : left = 0 ∧ right = 0 <;>
      simp [checkDecodedGate, gateFromFields, h, Gate.traceInstruction, checkAt_eq_agreesWith,
        WireTraceInstruction.expected]
  · rfl
  · by_cases hLeft : left < destination <;> by_cases hRight : right < destination <;>
      simp [checkDecodedGate, gateFromFields, hLeft, hRight, Gate.traceInstruction,
        checkAt_eq_agreesWith, WireTraceInstruction.expected, WireTraceInstruction.readEarlier,
        binaryOutput, agreesWith]
  · rfl

variable [DecidableEq R]

private def recordFailure (lanes : GateCheckLane → R) (passes : Bool) (values : R → Nat) :
    R → Nat :=
  setValue (lanes .failures) (values (lanes .failures) + (if passes then 0 else 1)) values

private abbrev BoundedRun (program : Fragment R) (x : BinaryWord) (bound : Nat)
    (initial final : R → Nat) : Prop :=
  ∃ ticks ≤ bound, program.RunsValues x ticks initial final

private theorem runCountFailure (lanes : GateCheckLane → R) (passes : Bool) (x : BinaryWord)
    (v : R → Nat) : BoundedRun (countFailure lanes passes) x 1 v (recordFailure lanes passes v) :=
  ⟨if passes then 0 else 1, by cases passes <;> decide,
    runsValues_incrementBy (lanes .failures) _ x v⟩

private theorem runReadWire {lanes : GateCheckLane → R} (hLanes : Function.Injective lanes)
    {x trace : BinaryWord} {v after : R → Nat} (h : GateCheckReady lanes x trace v)
    (wire : GateCheckLane) (hWire : wire = .destination ∨ wire = .left ∨ wire = .right)
    (hPos : v (lanes wire) < trace.length) (body : Option Bool → Fragment R) {cost : Nat}
    (hBody : BoundedRun (body (trace)[v (lanes wire)]?) x cost v after) :
    BoundedRun (readWire lanes wire body) x (25 * x.length + 16 + cost) v after := by
  have hBit := h.readWire _ hPos
  have hBound : v (lanes wire) ≤ x.length := by
    rcases hWire with rfl | rfl | rfl
    · exact h.destination_le
    · exact h.left_le
    · exact h.right_le
  obtain ⟨ticks, hTicks, hRun⟩ := hBody
  refine ⟨affineLookupCost 2 x.length (v (lanes .traceStart)) (v (lanes wire)) + ticks, ?_, ?_⟩
  · have hCost := affineLookupCost_le 2 x.length (v (lanes .traceStart)) (v (lanes wire))
    have hBase := h.traceStart_le
    omega
  · exact runsValues_affineLookup 2 (lanes ∘ wireReadLanes wire)
      (hLanes.comp (wireReadLanes_injective wire hWire)) body x v h.inputLength
      h.address_zero h.lookupWork_zero h.multiplier_zero h.scratch_zero (by
        change (body x[v (lanes .traceStart) + 2 * v (lanes wire)]?).RunsValues x ticks v after
        rwa [hBit])

private theorem runCheckOutput {lanes : GateCheckLane → R} (hLanes : Function.Injective lanes)
    {x trace : BinaryWord} {v : R → Nat} (h : GateCheckReady lanes x trace v)
    (expected : Option Bool) : BoundedRun (checkOutput lanes expected) x (25 * x.length + 17)
      v (recordFailure lanes (agreesWith expected (trace)[v (lanes .destination)]?) v) :=
  runReadWire hLanes h .destination (.inl rfl) h.destination_lt
    (fun value ↦ countFailure lanes (agreesWith expected value)) (runCountFailure lanes _ x v)

omit [DecidableEq R] in
private theorem operandBound {lanes : GateCheckLane → R} {x trace : BinaryWord} {v : R → Nat}
    (h : GateCheckReady lanes x trace v) (operand : Operand) :
    v (lanes operand.lane) ≤ x.length := by
  cases operand
  · exact h.left_le
  · exact h.right_le

private theorem runReadEarlier {lanes : GateCheckLane → R} (hLanes : Function.Injective lanes)
    {x trace : BinaryWord} {v after : R → Nat} (h : GateCheckReady lanes x trace v)
    (operand : Operand) (body : Option Bool → Fragment R) {cost : Nat}
    (hBody : BoundedRun (body (WireTraceInstruction.readEarlier trace
      (v (lanes .destination)) (v (lanes operand.lane)))) x cost v after) :
    BoundedRun (readEarlierWire lanes operand body) x (37 * x.length + 22 + cost) v after := by
  let source := v (lanes operand.lane)
  let dest := v (lanes .destination)
  have hSelected : BoundedRun (if source < dest then readWire lanes operand.lane body
      else body none) x (25 * x.length + 16 + cost) v after := by
    by_cases hLt : source < dest
    · rw [ite_eq_left hLt]
      have hWire : operand.lane = .destination ∨ operand.lane = .left ∨ operand.lane = .right := by
        cases operand <;> decide
      exact runReadWire hLanes h operand.lane hWire (hLt.trans h.destination_lt) body (by
        simpa only [WireTraceInstruction.readEarlier, source, dest, ite_eq_left hLt] using hBody)
    · rw [ite_eq_right hLt]
      have ⟨ticks, hTicks, hRun⟩ := hBody
      exact ⟨ticks, by omega, by
        simpa only [WireTraceInstruction.readEarlier, source, dest, ite_eq_right hLt] using hRun⟩
  obtain ⟨ticks, hTicks, hRun⟩ := hSelected
  refine ⟨ifEqualTime source dest + ticks, ?_, ?_⟩
  · have hSource := operandBound h operand
    have hDest := h.destination_le
    unfold ifEqualTime source dest
    omega
  · exact runsValues_ifLess (lanes ∘ comparisonLanes operand false)
      (hLanes.comp (comparisonLanes_injective operand false)) _ _ x v
      h.address_zero h.lookupWork_zero h.scratch_zero hRun

private theorem runRequireZero {lanes : GateCheckLane → R} (hLanes : Function.Injective lanes)
    {x trace : BinaryWord} {v : R → Nat} (h : GateCheckReady lanes x trace v)
    (operand : Operand) (body : Fragment R) (passes : Bool) {cost : Nat} (hCost : 1 ≤ cost)
    (hBody : v (lanes operand.lane) = 0 →
      BoundedRun body x cost v (recordFailure lanes passes v)) :
    BoundedRun (requireZero lanes operand body) x (6 * x.length + 6 + cost) v
      (recordFailure lanes (decide (v (lanes operand.lane) = 0) && passes) v) := by
  let source := v (lanes operand.lane)
  let outcome := recordFailure lanes (decide (source = 0) && passes) v
  have hSelected : BoundedRun (if v (lanes .zero) < source then countFailure lanes false
      else body) x cost v outcome := by
    by_cases hZero : source = 0
    · simpa only [h.zero, hZero, Nat.lt_irrefl, ite_false, decide_true, Bool.true_and,
        outcome] using hBody hZero
    · obtain ⟨ticks, hTicks, hRun⟩ := runCountFailure lanes false x v
      have hPos : 0 < source := Nat.pos_of_ne_zero hZero
      have hDec : decide (source = 0) = false := decide_eq_false hZero
      refine ⟨ticks, hTicks.trans hCost, ?_⟩
      simpa only [h.zero, hPos, ite_true, outcome, hDec, Bool.false_and] using hRun
  obtain ⟨ticks, hTicks, hRun⟩ := hSelected
  refine ⟨ifEqualTime (v (lanes .zero)) source + ticks, ?_, ?_⟩
  · have hSource := operandBound h operand
    unfold ifEqualTime source
    rw [h.zero]
    omega
  · exact runsValues_ifLess (lanes ∘ comparisonLanes operand true)
      (hLanes.comp (comparisonLanes_injective operand true)) _ _ x v
      h.address_zero h.lookupWork_zero h.scratch_zero hRun

private theorem runCheckConstant {lanes : GateCheckLane → R} (hLanes : Function.Injective lanes)
    {x trace : BinaryWord} {v : R → Nat} (h : GateCheckReady lanes x trace v) (bit : Bool) :
    BoundedRun (checkConstant lanes bit) x (37 * x.length + 29) v
      (recordFailure lanes (decide (v (lanes .left) = 0 ∧ v (lanes .right) = 0) &&
        agreesWith (some bit) (trace)[v (lanes .destination)]?) v) := by
  have hOutput := runCheckOutput hLanes h (some bit)
  have hRight := runRequireZero hLanes h .right _ _ (by omega) (fun _ ↦ hOutput)
  have hLeft := runRequireZero hLanes h .left _ _ (by omega) (fun _ ↦ hRight)
  obtain ⟨ticks, hTicks, hRun⟩ := hLeft
  refine ⟨ticks, by omega, ?_⟩
  rw [Bool.decide_and, Bool.and_assoc]
  exact hRun

private theorem runCheckNot {lanes : GateCheckLane → R} (hLanes : Function.Injective lanes)
    {x trace : BinaryWord} {v : R → Nat} (h : GateCheckReady lanes x trace v) :
    BoundedRun (checkNot lanes) x (68 * x.length + 45) v
      (recordFailure lanes (decide (v (lanes .right) = 0) && agreesWith
        ((WireTraceInstruction.readEarlier trace (v (lanes .destination))
          (v (lanes .left))).map (!·)) (trace)[v (lanes .destination)]?) v) := by
  have hRead := runReadEarlier hLanes h .left (fun value ↦ checkOutput lanes (value.map (!·)))
    (runCheckOutput hLanes h _)
  have hRight := runRequireZero hLanes h .right _ _ (by omega) (fun _ ↦ hRead)
  obtain ⟨ticks, hTicks, hRun⟩ := hRight
  exact ⟨ticks, by omega, hRun⟩

private theorem runCheckBinary {lanes : GateCheckLane → R} (hLanes : Function.Injective lanes)
    {x trace : BinaryWord} {v : R → Nat} (h : GateCheckReady lanes x trace v) (op : BinaryOp) :
    BoundedRun (checkBinary lanes op) x (99 * x.length + 61) v
      (recordFailure lanes (agreesWith (binaryOutput op
        (WireTraceInstruction.readEarlier trace (v (lanes .destination)) (v (lanes .left)))
        (WireTraceInstruction.readEarlier trace (v (lanes .destination)) (v (lanes .right))))
        (trace)[v (lanes .destination)]?) v) := by
  have hRight value := runReadEarlier hLanes h .right
    (fun other ↦ checkOutput lanes (binaryOutput op value other)) (runCheckOutput hLanes h _)
  have hLeft := runReadEarlier hLanes h .left
    (fun value ↦ readEarlierWire lanes .right fun other ↦
      checkOutput lanes (binaryOutput op value other)) (hRight _)
  have hTime : 37 * x.length + 22 + (37 * x.length + 22 + (25 * x.length + 17)) =
      99 * x.length + 61 := by omega
  simpa only [checkBinary, Operand.lane, hTime] using hLeft

private theorem runGateBranch {lanes : GateCheckLane → R} (hLanes : Function.Injective lanes)
    {x trace : BinaryWord} {v : R → Nat} (h : GateCheckReady lanes x trace v) (key : Fin 8) :
    BoundedRun (gateBranch lanes key) x (99 * x.length + 61) v
      (recordFailure lanes (checkDecodedGate trace (v (lanes .destination))
        (v (lanes .left)) (v (lanes .right)) key) v) := by
  have hConstant (bit : Bool) : BoundedRun (checkConstant lanes bit) x (99 * x.length + 61) v
      (recordFailure lanes (decide (v (lanes .left) = 0 ∧ v (lanes .right) = 0) &&
        agreesWith (some bit) (trace)[v (lanes .destination)]?) v) := by
    obtain ⟨ticks, hTicks, hRun⟩ := runCheckConstant hLanes h bit
    exact ⟨ticks, by omega, hRun⟩
  have hNot := runCheckNot hLanes h
  have hReject : BoundedRun (countFailure lanes false) x (99 * x.length + 61) v
      (recordFailure lanes false v) := by
    obtain ⟨ticks, hTicks, hRun⟩ := runCountFailure lanes false x v
    exact ⟨ticks, by omega, hRun⟩
  fin_cases key
  · exact hConstant false
  · exact runCheckBinary hLanes h .or
  · obtain ⟨ticks, hTicks, hRun⟩ := hNot
    exact ⟨ticks, by omega, hRun⟩
  · exact hReject
  · exact hConstant true
  · exact hReject
  · exact runCheckBinary hLanes h .and
  · exact hReject

private theorem gateReady_clearOpcode {lanes : GateCheckLane → R}
    (hLanes : Function.Injective lanes) {x trace : BinaryWord} {v : R → Nat}
    (h : GateCheckReady lanes x trace v) :
    GateCheckReady lanes x trace (clearValues (lanes .opcode) v) := by
  have point (lane : GateCheckLane) (hn : lane ≠ .opcode) :
      clearValues (lanes .opcode) v (lanes lane) = v (lanes lane) := by
    have hNe : lanes lane ≠ lanes .opcode := fun e ↦ hn (hLanes e)
    simp [clearValues, hNe]
  exact ⟨(point .inputLength (by decide)).trans h.inputLength,
    by simpa only [point .traceStart (by decide)] using h.traceStart_le,
    by simpa only [point .destination (by decide)] using h.destination_le,
    by simpa only [point .left (by decide)] using h.left_le,
    by simpa only [point .right (by decide)] using h.right_le,
    by simpa only [point .destination (by decide)] using h.destination_lt,
    by simpa only [point .traceStart (by decide)] using h.readWire,
    (point .address (by decide)).trans h.address_zero,
    (point .lookupWork (by decide)).trans h.lookupWork_zero,
    (point .multiplier (by decide)).trans h.multiplier_zero,
    (point .scratch (by decide)).trans h.scratch_zero,
    (point .zero (by decide)).trans h.zero⟩

/-- The uniform fragment terminates for every opcode and operand combination
in the prepared ranges. It reads only supplied trace values. -/
theorem runsValues_checkGateRegister {lanes : GateCheckLane → R}
    (hLanes : Function.Injective lanes) {x trace : BinaryWord} {v : R → Nat}
    (h : GateCheckReady lanes x trace v) (hOpcode : v (lanes .opcode) < 8) :
    let passes := checkDecodedGate trace (v (lanes .destination)) (v (lanes .left))
      (v (lanes .right)) ⟨v (lanes .opcode), hOpcode⟩
    ∃ ticks ≤ gateCheckCost x.length,
      (checkGateRegister lanes).RunsValues x ticks v
        (setValue (lanes .failures) (v (lanes .failures) + (if passes then 0 else 1))
          (clearValues (lanes .opcode) v)) := by
  let key : Fin 8 := ⟨v (lanes .opcode), hOpcode⟩
  have pt (reg : GateCheckLane) (hn : reg ≠ .opcode) :
      clearValues (lanes .opcode) v (lanes reg) = v (lanes reg) := by
    have hNe : lanes reg ≠ lanes .opcode := fun e ↦ hn (hLanes e)
    simp [clearValues, hNe]
  obtain ⟨bodyTicks, hBodyTicks, hBody⟩ := runGateBranch hLanes (gateReady_clearOpcode hLanes h) key
  refine ⟨v (lanes .opcode) + 1 + bodyTicks, by unfold gateCheckCost; omega, ?_⟩
  intro output
  let cfg : Config R Unit := ⟨none, v, none, output⟩
  have hRun := run_dispatchFin (lanes .opcode) (gateBranch lanes) x cfg hOpcode
    (hBody output) rfl
  simpa only [cfg, checkGateRegister, recordFailure, pt .destination (by decide),
    pt .left (by decide), pt .right (by decide), pt .failures (by decide), Config.map,
    dispatchBranchMap, Option.map_none, Option.map_some] using hRun

end PvsNP.MCSP
