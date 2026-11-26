module

public import PvsNP.MCSP.GateRecordRegister

/-! # Count failures in a circuit block independently of the scan direction -/

public section

namespace PvsNP.MCSP

open Circuits RegisterMachine RegisterMachine.Fragment

/-- Check the numeric fields of a gate and the supplied value of its output wire. -/
@[expose] def gateFieldsPass (trace : BinaryWord) (destination : Nat) (record : GateFields) :
    Bool :=
  ((gateFromFields destination record.opcode record.left record.right).map fun gate ↦
    gate.traceInstruction.checkAt destination trace).getD false

/-- Count failed gates in their serialized order. Each gate adds one wire. -/
@[expose] def gateFailureCount (trace : BinaryWord) : Nat → List GateFields → Nat
  | _, [] => 0
  | destination, record :: tail =>
    (if gateFieldsPass trace destination record then 0 else 1) +
      gateFailureCount trace (destination + 1) tail

/-- Reading the last record first adds the same error to the count. -/
theorem gateFailureCount_append (trace : BinaryWord) (destination : Nat)
    (initial rest : List GateFields) :
    gateFailureCount trace destination (initial ++ rest) =
      gateFailureCount trace destination initial +
        gateFailureCount trace (destination + initial.length) rest := by
  induction initial generalizing destination with
  | nil => simp [gateFailureCount]
  | cons first initial ih =>
    simp only [List.cons_append, gateFailureCount, List.length_cons, ih, Nat.add_assoc]
    rw [Nat.add_comm 1 initial.length]

theorem gateFieldsPass_gate (trace : BinaryWord) {n : Nat} (gate : Gate n) :
    gateFieldsPass trace n gate.traceInstruction.fields =
      gate.traceInstruction.checkAt n trace := by
  simp only [gateFieldsPass, gateFromFields_traceInstruction_fields, Option.map_some,
    Option.getD_some]

theorem gateFailureCount_network_eq_zero_iff {n m : Nat} (network : Network n m)
    (trace : BinaryWord) :
    (gateFailureCount trace n (network.traceInstructions.map WireTraceInstruction.fields) = 0 ∧
      trace.length = m) ↔ checkWireTraceFrom n network.traceInstructions trace = true := by
  induction network with
  | empty => simp [Network.traceInstructions, gateFailureCount, checkWireTraceFrom]
  | cons gate rest ih =>
    simp only [Network.traceInstructions, List.map_cons, gateFailureCount, gateFieldsPass_gate,
      checkWireTraceFrom, Bool.and_eq_true, ← ih]
    cases gate.traceInstruction.checkAt _ trace <;> simp

private def indexedFailure (trace : BinaryWord) (arity : Nat) (records : List GateFields)
    (index : Nat) : Nat :=
  (records[index]?.map fun record ↦ if gateFieldsPass trace (arity + index) record then 0 else 1)
    |>.getD 0

private theorem gateFailureCount_eq_sum (trace : BinaryWord) (arity : Nat)
    (records : List GateFields) : gateFailureCount trace arity records =
      ((List.range records.length).map (indexedFailure trace arity records)).sum := by
  induction records generalizing arity with
  | nil => rfl
  | cons record tail ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons]
    have hHead : indexedFailure trace arity (record :: tail) 0 =
        (if gateFieldsPass trace arity record then 0 else 1) := by simp [indexedFailure]
    have hTail : indexedFailure trace arity (record :: tail) ∘ Nat.succ =
        indexedFailure trace (arity + 1) tail := by
      funext i
      simp only [Function.comp_apply, indexedFailure, List.getElem?_cons_succ]
      rw [show arity + i.succ = arity + 1 + i by omega]
    rw [hHead, hTail, ← ih]
    rfl

private theorem foldl_add_indexed (f : Nat → Nat) (indices : List Nat) (initial : Nat) :
    indices.foldl (fun total i ↦ total + f i) initial = initial + (indices.map f).sum := by
  induction indices generalizing initial with
  | nil => simp
  | cons i tail ih => simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons, Nat.add_assoc]

/-- Summing the error bits during a backwards scan yields the forward count. -/
private theorem gateFailureCount_reverse_fold (trace : BinaryWord) (arity : Nat)
    (records : List GateFields)
    (initial : Nat) :
    (List.range records.length).reverse.foldl
      (fun count i ↦ count + indexedFailure trace arity records i) initial =
      initial + gateFailureCount trace arity records := by
  rw [foldl_add_indexed, List.map_reverse, List.sum_reverse_nat, gateFailureCount_eq_sum]

/-- The three fields as they occur in a gate record. -/
structure GateRecordBits where
  tag : BinaryWord
  left : BinaryWord
  right : BinaryWord

@[expose] def GateRecordBits.fields (record : GateRecordBits) : GateFields :=
  ⟨fieldValue record.tag, fieldValue record.left, fieldValue record.right⟩

@[expose] def GateRecordBits.encode (width : Nat) (fields : GateFields) : GateRecordBits :=
  ⟨fieldBits 3 fields.opcode, fieldBits width fields.left, fieldBits width fields.right⟩

private theorem GateRecordBits.fields_encode (width : Nat) (fields : GateFields) :
    (GateRecordBits.encode width fields).fields = decodeGateFields width (encodeGateFields
      width fields) := by
  have hRight : (fieldBits width fields.right).take width = fieldBits width fields.right :=
    List.take_of_length_le (Nat.le_of_eq (length_fieldBits width fields.right))
  simp only [GateRecordBits.encode, GateRecordBits.fields, decodeGateFields, encodeGateFields,
    List.append_assoc, List.take_left' (length_fieldBits 3 fields.opcode),
    List.drop_left' (length_fieldBits 3 fields.opcode),
    List.take_left' (length_fieldBits width fields.left),
    List.drop_left' (length_fieldBits width fields.left), hRight]

theorem decodedGateRecordBits_eq {n : Nat} (cap : Nat) (circuit : BooleanCircuit n)
    (hSize : circuit.size ≤ cap) :
    (circuit.network.traceInstructions.map (fun op ↦
      GateRecordBits.encode (circuitFieldWidth n cap) op.fields)).map GateRecordBits.fields =
        circuit.network.traceInstructions.map WireTraceInstruction.fields := by
  apply List.ext_getElem
  · simp only [List.length_map]
  · intro i hi _
    have hIndex : i < circuit.size := by
      simpa only [List.length_map, Network.length_traceInstructions,
        BooleanCircuit.size] using hi
    rw [List.getElem_map, List.getElem_map, List.getElem_map, GateRecordBits.fields_encode,
      ← take_drop_encodeCircuit_gateRecord cap circuit i hIndex,
      decodeGateFields_encodeCircuit_gateRecord cap circuit hSize i hIndex]

variable {R : Type}

/-- The block starts at the last record's final bit. Width and gate count are
in registers. The layout fixes the positions that the decoder will read. -/
structure GateBlockReady (lanes : GateRecordLane → R) (counter : R) (word trace : BinaryWord)
    (arity : Nat) (records : List GateRecordBits) (values : R → Nat) : Prop where
  count : values counter = records.length
  destination : values (lanes (.gate .destination)) = arity + records.length - 1
  traceLength : trace.length = arity + records.length
  traceLength_le : trace.length ≤ word.length
  gates : records ≠ [] → GateRecordReady lanes word trace values
  layout : ∀ (i : Fin records.length),
    let width := values (lanes .width)
    let record := records[i]
    GateRecordLayout word (values (lanes .position) +
      4 * (3 + 2 * width) * (records.length - (i.val + 1))) width
      record.tag record.left record.right
  operands : ∀ (i : Fin records.length),
    let record := records[i]
    fieldValue record.left ≤ word.length ∧ fieldValue record.right ≤ word.length

/-- Check every gate with the same loop body and count the failing records. -/
def checkGateBlockRegister (lanes : GateRecordLane → R) (counter : R) : Fragment R :=
  countdown counter (checkGateRecordRegister lanes)

@[expose] def gateBlockCost (length width count : Nat) : Nat :=
  count * (gateRecordCost length width + 1) + 1

theorem gateBlockCost_polynomiallyBounded {length width count : Nat → Nat}
    (hLength : PolynomiallyBounded length) (hWidth : PolynomiallyBounded width)
    (hCount : PolynomiallyBounded count) :
    PolynomiallyBounded (fun n ↦ gateBlockCost (length n) (width n) (count n)) :=
  (hCount.mul ((gateRecordCost_polynomiallyBounded hLength hWidth).add
    (PolynomiallyBounded.const 1))).add (PolynomiallyBounded.const 1)

private def withOutputSuffix {L : Type} (cfg : Config R L) (suffix : BinaryWord) : Config R L :=
  { cfg with output := cfg.output ++ suffix }

variable [DecidableEq R]

private theorem execute_withOutputSuffix {L : Type} (instruction : Instruction R L)
    (word suffix : BinaryWord) (cfg : Config R L) :
    instruction.execute word (withOutputSuffix cfg suffix) =
      (instruction.execute word cfg).map (withOutputSuffix · suffix) := by
  cases instruction <;> cases h : cfg.cursor <;>
    simp [Instruction.execute, Config.readAt, withOutputSuffix, h]
  all_goals split <;> rfl

private theorem run_withOutputSuffix {L : Type} (program : L → Instruction R L)
    (word suffix : BinaryWord) (ticks : Nat) (cfg : Config R L) :
    run program word ticks (withOutputSuffix cfg suffix) =
      (run program word ticks cfg).map (withOutputSuffix · suffix) := by
  induction ticks generalizing cfg with
  | zero => rfl
  | succ n ih =>
    rw [RegisterMachine.run_succ, RegisterMachine.run_succ]
    have hStep : RegisterMachine.step program word (withOutputSuffix cfg suffix) =
        (RegisterMachine.step program word cfg).map (withOutputSuffix · suffix) := by
      cases h : cfg.pc with
      | none => simp [RegisterMachine.step, withOutputSuffix, h]
      | some label =>
        have hNew : (withOutputSuffix cfg suffix).pc = some label := h
        rw [step_at hNew, step_at h]
        exact execute_withOutputSuffix (program label) word suffix cfg
    rw [hStep]
    cases RegisterMachine.step program word cfg <;>
      simp only [Option.map_none, Option.bind_none, Option.map_some, Option.bind_some, ih]

/-- A backward scan counts exactly the failing gates and clears the counter.
The layout hypotheses specify reads and widths. The gate checks handle the
opcode and operand values, including malformed values in the stated ranges. -/
theorem runsValues_checkGateBlockRegister {lanes : GateRecordLane → R}
    (hLanes : Function.Injective lanes) {counter : R} (hCounter : ∀ lane, lanes lane ≠ counter)
    {word trace : BinaryWord} {arity : Nat} {records : List GateRecordBits} {v : R → Nat}
    (ready : GateBlockReady lanes counter word trace arity records v) :
    ∃ ticks ≤ gateBlockCost word.length (v (lanes .width)) records.length,
      ∃ after, (checkGateBlockRegister lanes counter).RunsValues word ticks v after ∧
        after counter = 0 ∧
        after (lanes .position) =
          v (lanes .position) + 4 * (3 + 2 * v (lanes .width)) * records.length ∧
        after (lanes (.gate .destination)) = arity - 1 ∧
        after (lanes (.gate .failures)) = v (lanes (.gate .failures)) +
          gateFailureCount trace arity (records.map GateRecordBits.fields) ∧
        ∀ r, r ≠ counter → r ≠ lanes .position → r ≠ lanes (.gate .destination) →
          r ≠ lanes (.gate .failures) → after r = v r := by
  let body := checkGateRecordRegister lanes
  let loop := countdown counter body
  let fields := records.map GateRecordBits.fields
  let stride := 4 * (3 + 2 * v (lanes .width))
  let update := fun total i ↦ total + indexedFailure trace arity fields i
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
    have hWidth := stable .width (by simp) (by simp) (by simp)
    have hNonempty : records ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hStart := ready.gates hNonempty
    have hTrace := ready.traceLength
    have hLen := ready.traceLength_le
    have hChecked : GateRecordReady lanes word trace tested := by
      have gateStable (reg : GateCheckLane) (hd : reg ≠ .destination) (hf : reg ≠ .failures) :
          tested ((lanes ∘ GateRecordLane.gate) reg) = v ((lanes ∘ GateRecordLane.gate) reg) :=
        stable (.gate reg) (fun e ↦ GateRecordLane.noConfusion e)
          (fun e ↦ hd (GateRecordLane.gate.inj e)) (fun e ↦ hf (GateRecordLane.gate.inj e))
      have hg := hStart.gate
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
      · simpa only [gateStable .inputLength (by decide) (by decide)] using hg.inputLength
      · simpa only [gateStable .traceStart (by decide) (by decide)] using hg.traceStart_le
      · change tested (lanes (.gate .destination)) ≤ word.length
        omega
      · simpa only [gateStable .left (by decide) (by decide)] using hg.left_le
      · simpa only [gateStable .right (by decide) (by decide)] using hg.right_le
      · change tested (lanes (.gate .destination)) < trace.length
        omega
      · simpa only [gateStable .traceStart (by decide) (by decide)] using hg.readWire
      · simpa only [gateStable .address (by decide) (by decide)] using hg.address_zero
      · simpa only [gateStable .lookupWork (by decide) (by decide)] using hg.lookupWork_zero
      · simpa only [gateStable .multiplier (by decide) (by decide)] using hg.multiplier_zero
      · simpa only [gateStable .scratch (by decide) (by decide)] using hg.scratch_zero
      · simpa only [gateStable .zero (by decide) (by decide)] using hg.zero
      · rw [stable .remaining (by simp) (by simp) (by simp), hStart.remaining_zero]
      · rw [stable (.gate .left) (by simp) (by simp) (by simp), hStart.left_zero]
      · rw [stable (.gate .right) (by simp) (by simp) (by simp), hStart.right_zero]
      · rw [stable (.gate .opcode) (by simp) (by simp) (by simp), hStart.opcode_zero]
    have hLayout : GateRecordLayout word (tested (lanes .position)) (tested (lanes .width))
        record.tag record.left record.right := by
      rw [hPos', hWidth]
      exact ready.layout ⟨i, hi⟩
    have hFields := ready.operands ⟨i, hi⟩
    obtain ⟨ticks, hTicks, after, hRun, hResult⟩ :=
      runsValues_checkGateRecordRegister hLanes hChecked hLayout hFields.1 hFields.2
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
        simp only [update, indexedFailure, fields, List.getElem?_map, List.getElem?_eq_getElem hi,
          Option.map_some, Option.getD_some, gateFieldsPass, gateRecordPasses,
          GateRecordBits.fields, record]
        rfl
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
      cases next with
      | mk pc values cursor old =>
        change pc = some none at hExit
        change cursor = none at hCursor
        change old = [] at hOutput
        subst pc cursor old
        rfl
    rw [hNext] at hSuffix
    exact hSuffix
  · simpa only [Nat.sub_zero, stride] using hPos
  · simpa only [Nat.add_zero] using hDest
  · have hSum := gateFailureCount_reverse_fold trace arity fields (v (lanes (.gate .failures)))
    have hLength : fields.length = records.length := by simp only [fields, List.length_map]
    rw [hLength] at hSum
    exact hFail.trans hSum

/-- With the exact circuit layout, a zero failure register is equivalent to
the wire-trace checker for the circuit's gate block. -/
theorem runsValues_checkCircuitGateBlock {n : Nat} (cap : Nat) (circuit : BooleanCircuit n)
    (hSize : circuit.size ≤ cap) {lanes : GateRecordLane → R}
    (hLanes : Function.Injective lanes) {counter : R} (hCounter : ∀ lane, lanes lane ≠ counter)
    {word trace : BinaryWord} {v : R → Nat} (hInitial : v (lanes (.gate .failures)) = 0)
    (ready : GateBlockReady lanes counter word trace n
      (circuit.network.traceInstructions.map fun op ↦
        GateRecordBits.encode (circuitFieldWidth n cap) op.fields) v) :
    ∃ ticks ≤ gateBlockCost word.length (v (lanes .width)) circuit.size,
      ∃ after, (checkGateBlockRegister lanes counter).RunsValues word ticks v after ∧
        after counter = 0 ∧
        (after (lanes (.gate .failures)) = 0 ↔
          checkWireTraceFrom n circuit.network.traceInstructions trace = true) := by
  obtain ⟨ticks, hTicks, after, hRun, hCounterZero, _, _, hFailures, _⟩ :=
    runsValues_checkGateBlockRegister hLanes hCounter ready
  simp only [List.length_map, Network.length_traceInstructions] at hTicks
  have hLength : trace.length = circuit.wires := by
    have h := ready.traceLength
    rw [circuit.network.wires_eq_input_add_size]
    simpa only [List.length_map, Network.length_traceInstructions] using h
  refine ⟨ticks, hTicks, after, hRun, hCounterZero, ?_⟩
  rw [hFailures, decodedGateRecordBits_eq cap circuit hSize, hInitial, Nat.zero_add,
    ← gateFailureCount_network_eq_zero_iff]
  simp only [hLength, and_true]

end PvsNP.MCSP
