module

public import PvsNP.Circuits.WireTrace

import all PvsNP.Circuits.Description
import Mathlib.Data.List.Basic

/-! # Numeric gate fields and offsets in a circuit description -/

public section

namespace PvsNP.Circuits

/-- Interpret the numeric little-endian opcode and the two operand fields. -/
@[expose] def gateFromFields (destination opcode left right : Nat) : Option (Gate destination) :=
  match opcode with
  | 0 => if left = 0 ∧ right = 0 then some (.const false) else none
  | 4 => if left = 0 ∧ right = 0 then some (.const true) else none
  | 2 =>
    if h : left < destination then
      if right = 0 then some (.not ⟨left, h⟩) else none
    else none
  | 6 =>
    if hl : left < destination then
      if hr : right < destination then some (.binary .and ⟨left, hl⟩ ⟨right, hr⟩) else none
    else none
  | 1 =>
    if hl : left < destination then
      if hr : right < destination then some (.binary .or ⟨left, hl⟩ ⟨right, hr⟩) else none
    else none
  | _ => none

structure GateFields where
  opcode : Nat
  left : Nat
  right : Nat

/-- The opcode and operand integers written for an instruction by the codec. -/
@[expose] def WireTraceInstruction.fields : WireTraceInstruction → GateFields
  | .const false => ⟨0, 0, 0⟩
  | .const true => ⟨4, 0, 0⟩
  | .not src => ⟨2, src, 0⟩
  | .binary .and lhs rhs => ⟨6, lhs, rhs⟩
  | .binary .or lhs rhs => ⟨1, lhs, rhs⟩

theorem gateFromFields_traceInstruction_fields {n : Nat} (gate : Gate n) :
    let fields := gate.traceInstruction.fields
    gateFromFields n fields.opcode fields.left fields.right = some gate := by
  cases gate with
  | const b => cases b <;> rfl
  | not i => simp [gateFromFields, Gate.traceInstruction, WireTraceInstruction.fields, i.isLt]
  | binary op l r =>
    cases op <;>
      simp [gateFromFields, Gate.traceInstruction, WireTraceInstruction.fields, l.isLt, r.isLt]

private theorem gateFromFields_of_tag (n left right : Nat) {tag : List Bool}
    (hTag : tag.length = 3) :
    gateFromFields n (fieldValue tag) left right = readGateFields n tag left right := by
  obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp hTag
  cases a <;> cases b <;> cases c <;> rfl

private theorem readField_append (w : Nat) (field rest : List Bool) (hLength : field.length = w) :
    readField w (field ++ rest) = some (fieldValue field, rest) := by
  have hFits : w ≤ (field ++ rest).length := by
    rw [List.length_append, hLength]
    exact Nat.le_add_right ..
  rw [readField, ite_eq_left hFits, List.take_left' hLength, List.drop_left' hLength]

/-- The description parser checks the same numeric fields as `gateFromFields`. -/
theorem readGate_eq_gateFromFields (w n : Nat) (tag left right suffix : List Bool)
    (hTag : tag.length = 3) (hLeft : left.length = w) (hRight : right.length = w) :
    readGate w n (tag ++ left ++ right ++ suffix) =
      (gateFromFields n (fieldValue tag) (fieldValue left) (fieldValue right)).map
        (fun gate ↦ (gate, suffix)) := by
  simp only [readGate, List.append_assoc, List.take_left' hTag, List.drop_left' hTag,
    readField_append w left _ hLeft, readField_append w right suffix hRight,
    Option.bind_eq_bind, Option.bind_some, ← gateFromFields_of_tag n _ _ hTag]
  cases gateFromFields n (fieldValue tag) (fieldValue left) (fieldValue right) <;> rfl

/-- Serialize an opcode followed by the two fixed-width operand fields. -/
@[expose] def encodeGateFields (w : Nat) (fields : GateFields) : List Bool :=
  fieldBits 3 fields.opcode ++ fieldBits w fields.left ++ fieldBits w fields.right

@[simp] theorem length_encodeGateFields (w : Nat) (fields : GateFields) :
    (encodeGateFields w fields).length = 3 + 2 * w := by
  simp only [encodeGateFields, List.length_append, length_fieldBits]
  omega

/-- Read the three numbers at the start of a record. Field lengths are checked separately. -/
@[expose] def decodeGateFields (w : Nat) (bits : List Bool) : GateFields :=
  let operands := bits.drop 3
  ⟨fieldValue (bits.take 3), fieldValue (operands.take w), fieldValue ((operands.drop w).take w)⟩

theorem decodeGateFields_encodeGateFields (w : Nat) (fields : GateFields)
    (hOpcode : fields.opcode < 8) (hLeft : fields.left < 2 ^ w) (hRight : fields.right < 2 ^ w) :
    decodeGateFields w (encodeGateFields w fields) = fields := by
  have hTag := length_fieldBits 3 fields.opcode
  have hOperand := length_fieldBits w fields.left
  rw [decodeGateFields, encodeGateFields, List.append_assoc, List.take_left' hTag,
    List.drop_left' hTag, List.take_left' hOperand, List.drop_left' hOperand,
    List.take_of_length_le (Nat.le_of_eq (length_fieldBits w fields.right)),
    fieldValue_bits 3 _ hOpcode, fieldValue_bits w _ hLeft, fieldValue_bits w _ hRight]

private theorem encodeGate_eq_encodeGateFields {n : Nat} (w : Nat) (gate : Gate n) :
    encodeGate w gate = encodeGateFields w gate.traceInstruction.fields := by
  cases gate with
  | const b =>
    cases b <;> simp only [encodeGate, gateRecord, encodeGateFields, Gate.traceInstruction,
      WireTraceInstruction.fields] <;> rfl
  | not _ =>
    simp only [encodeGate, gateRecord, encodeGateFields, Gate.traceInstruction,
      WireTraceInstruction.fields]
    rfl
  | binary op _ _ =>
    cases op <;> simp only [encodeGate, gateRecord, encodeGateFields, Gate.traceInstruction,
      WireTraceInstruction.fields] <;> rfl

private theorem encodeNetwork_eq_gateRecords {n m : Nat} (w : Nat) (network : Network n m) :
    encodeNetwork w network = network.traceInstructions.flatMap
      (fun instruction ↦ encodeGateFields w instruction.fields) := by
  induction network with
  | empty => rfl
  | cons gate rest ih =>
    simp only [encodeNetwork, Network.traceInstructions, List.flatMap_cons,
      encodeGate_eq_encodeGateFields, ih]

/-- A canonical circuit description contains a header, fixed-size records, and its output. -/
theorem encodeCircuit_eq_gateRecords {n : Nat} (s : Nat) (c : BooleanCircuit n) :
    let w := circuitFieldWidth n s
    encodeCircuit s c = fieldBits w c.size ++
      c.network.traceInstructions.flatMap (fun instruction ↦ encodeGateFields w instruction.fields)
      ++
      fieldBits w c.output.val := by
  rw [encodeCircuit, encodeNetwork_eq_gateRecords]

/-- The final field follows immediately after the gate records. -/
theorem drop_encodeCircuit_gateRecords {n : Nat} (s : Nat) (c : BooleanCircuit n) :
    let w := circuitFieldWidth n s
    (encodeCircuit s c).drop (w + c.size * (3 + 2 * w)) = fieldBits w c.output.val := by
  dsimp only
  rw [encodeCircuit]
  apply List.drop_left'
  simp only [List.length_append, length_fieldBits, length_encodeNetwork, BooleanCircuit.size]

private theorem take_drop_flatMap_fixed {α β : Type} (f : α → List β) (width : Nat)
    (hWidth : ∀ record, (f record).length = width) (records : List α) (suffix : List β)
    (i : Nat) (hi : i < records.length) :
    ((records.flatMap f ++ suffix).drop (i * width)).take width = f records[i] := by
  induction records generalizing i with
  | nil => simp at hi
  | cons head rest ih =>
    cases i with
    | zero =>
      simp only [Nat.zero_mul, List.drop_zero, List.getElem_cons_zero, List.flatMap_cons,
        List.append_assoc, List.take_left' (hWidth head)]
    | succ i =>
      rw [List.flatMap_cons, List.append_assoc, Nat.succ_mul, Nat.add_comm (i * width) width,
        ← List.drop_drop, List.drop_left' (hWidth head)]
      exact ih i (Nat.lt_of_succ_lt_succ hi)

/-- Slice the `i`th record immediately after the gate-count header. -/
theorem take_drop_encodeCircuit_gateRecord {n : Nat} (s : Nat) (c : BooleanCircuit n)
    (i : Nat) (hi : i < c.size) :
    let w := circuitFieldWidth n s
    let instruction := c.network.traceInstructions[i]'(by simpa [BooleanCircuit.size] using hi)
    ((encodeCircuit s c).drop (w + i * (3 + 2 * w))).take (3 + 2 * w) =
      encodeGateFields w instruction.fields := by
  dsimp only
  rw [encodeCircuit_eq_gateRecords, List.append_assoc, ← List.drop_drop,
    List.drop_left' (length_fieldBits (circuitFieldWidth n s) c.size)]
  let encodeInstruction (instruction : WireTraceInstruction) :=
    encodeGateFields (circuitFieldWidth n s) instruction.fields
  exact take_drop_flatMap_fixed encodeInstruction _
    (fun instruction ↦ length_encodeGateFields _ instruction.fields)
    c.network.traceInstructions _ i (by simpa [BooleanCircuit.size] using hi)

private theorem gateFields_fit {n : Nat} (gate : Gate n) (w : Nat) (hWires : n ≤ 2 ^ w) :
    let fields := gate.traceInstruction.fields
    fields.opcode < 8 ∧ fields.left < 2 ^ w ∧ fields.right < 2 ^ w := by
  have hZero := Nat.two_pow_pos w
  cases gate with
  | const b =>
    cases b <;> exact ⟨by simp [Gate.traceInstruction, WireTraceInstruction.fields], hZero, hZero⟩
  | not i =>
    exact ⟨by simp [Gate.traceInstruction, WireTraceInstruction.fields],
      i.isLt.trans_le hWires, hZero⟩
  | binary op l r =>
    cases op <;> exact ⟨by simp [Gate.traceInstruction, WireTraceInstruction.fields],
      l.isLt.trans_le hWires, r.isLt.trans_le hWires⟩

private theorem traceInstruction_fields_fit {n m : Nat} (network : Network n m) (w : Nat)
    (hWires : m ≤ 2 ^ w) {instruction : WireTraceInstruction}
    (hInstruction : instruction ∈ network.traceInstructions) :
    instruction.fields.opcode < 8 ∧ instruction.fields.left < 2 ^ w ∧
      instruction.fields.right < 2 ^ w := by
  induction network with
  | empty => simp [Network.traceInstructions] at hInstruction
  | @cons n m gate rest ih =>
    simp only [Network.traceInstructions, List.mem_cons] at hInstruction
    rcases hInstruction with rfl | hRest
    · exact gateFields_fit gate w ((Network.cons gate rest).wires_le.trans hWires)
    · exact ih hWires hRest

theorem decodeGateFields_encodeCircuit_gateRecord {n : Nat} (s : Nat) (c : BooleanCircuit n)
    (hSize : c.size ≤ s) (i : Nat) (hi : i < c.size) :
    let w := circuitFieldWidth n s
    let instruction := c.network.traceInstructions[i]'(by simpa [BooleanCircuit.size] using hi)
    decodeGateFields w (((encodeCircuit s c).drop (w + i * (3 + 2 * w))).take (3 + 2 * w)) =
      instruction.fields := by
  dsimp only
  rw [take_drop_encodeCircuit_gateRecord s c i hi]
  have hWires : c.wires ≤ 2 ^ circuitFieldWidth n s := by
    rw [c.network.wires_eq_input_add_size]
    exact (Nat.add_le_add_left hSize n).trans (Nat.le_of_lt Nat.lt_log2_self)
  have hiTrace : i < c.network.traceInstructions.length := by simpa [BooleanCircuit.size] using hi
  obtain ⟨hOpcode, hLeft, hRight⟩ :=
    traceInstruction_fields_fit c.network _ hWires (List.getElem_mem hiTrace)
  exact decodeGateFields_encodeGateFields _ _ hOpcode hLeft hRight

/-- At record `i`, the next wire is `n + i` and all references are earlier. -/
theorem Network.gateFromFields_traceInstructionAt {n m : Nat} (network : Network n m)
    (i : Nat) (hi : i < network.traceInstructions.length) :
    let instruction := network.traceInstructions[i]
    let fields := instruction.fields
    (gateFromFields (n + i) fields.opcode fields.left fields.right).map Gate.traceInstruction =
      some instruction := by
  induction network generalizing i with
  | empty => simp [traceInstructions] at hi
  | @cons n m gate rest ih =>
    cases i with
    | zero =>
      simpa only [traceInstructions, List.getElem_cons_zero, Nat.add_zero, Option.map_some] using
        congrArg (Option.map Gate.traceInstruction) (gateFromFields_traceInstruction_fields gate)
    | succ i =>
      have hi' : i < rest.traceInstructions.length := Nat.lt_of_succ_lt_succ hi
      have hDestination : n + (i + 1) = n + 1 + i := by omega
      let instruction := rest.traceInstructions[i]
      let fields := instruction.fields
      let interpret (destination : Nat) :=
        (gateFromFields destination fields.opcode fields.left fields.right).map
          Gate.traceInstruction
      change interpret (n + (i + 1)) = some instruction
      rw [hDestination]
      exact ih i hi'

end PvsNP.Circuits
