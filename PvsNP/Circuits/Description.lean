module

public import PvsNP.Circuits.Enumerate

import Init.Data.List.TakeDrop
import Init.Data.Nat.Lemmas

/-! # Succinct binary descriptions of topologically ordered circuits -/

namespace PvsNP.Circuits

/-- Every gate count up to `s` and every wire below `n + s` fits this field. -/
@[expose] public def circuitFieldWidth (n s : Nat) : Nat := (n + s).log2 + 1

/-- Write the low bits of a natural number in a fixed-width little-endian field. -/
@[expose] public def fieldBits : Nat → Nat → List Bool
  | 0, _ => []
  | w + 1, a => decide (a % 2 = 1) :: fieldBits w (a / 2)

public theorem length_fieldBits (w a : Nat) : (fieldBits w a).length = w := by
  induction w generalizing a with
  | zero => rfl
  | succ w ih => simp only [fieldBits, List.length_cons, ih]

/-- Read a little-endian bit field as a natural number. -/
@[expose] public def fieldValue : List Bool → Nat
  | [] => 0
  | b :: rest => b.toNat + 2 * fieldValue rest

public theorem fieldValue_bits (w a : Nat) (hFit : a < 2 ^ w) :
    fieldValue (fieldBits w a) = a := by
  induction w generalizing a with
  | zero => simp only [fieldBits, fieldValue]; omega
  | succ w ih =>
    have hHalf : a / 2 < 2 ^ w :=
      (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr (by
        rw [← Nat.pow_succ]
        exact hFit)
    have hBit : (decide (a % 2 = 1)).toNat = a % 2 := by
      by_cases hOne : a % 2 = 1
      · simp only [hOne, decide_true, Bool.toNat_true]
      · have hZero : a % 2 = 0 := by
          have hRem := Nat.mod_lt a (by decide : 0 < 2)
          omega
        simp only [hZero, Nat.zero_ne_one, decide_false, Bool.toNat_false]
    simp only [fieldBits, fieldValue, hBit, ih _ hHalf]
    exact Nat.mod_add_div a 2

private def readField (w : Nat) (bits : List Bool) : Option (Nat × List Bool) :=
  if w ≤ bits.length then some (fieldValue (bits.take w), bits.drop w) else none

private theorem readField_bits (w a : Nat) (rest : List Bool) (hFit : a < 2 ^ w) :
    readField w (fieldBits w a ++ rest) = some (a, rest) := by
  have hLength : w ≤ (fieldBits w a ++ rest).length := by
    rw [List.length_append, length_fieldBits]
    exact Nat.le_add_right ..
  rw [readField, ite_eq_left hLength, List.take_left' (length_fieldBits w a),
    List.drop_left' (length_fieldBits w a), fieldValue_bits w a hFit]

private def gateRecord (w : Nat) (tag : List Bool) (left right : Nat) : List Bool :=
  tag ++ fieldBits w left ++ fieldBits w right

private def encodeGate {n : Nat} (w : Nat) : Gate n → List Bool
  | .const false => gateRecord w [false, false, false] 0 0
  | .const true => gateRecord w [false, false, true] 0 0
  | .not src => gateRecord w [false, true, false] src.val 0
  | .binary .and left right => gateRecord w [false, true, true] left.val right.val
  | .binary .or left right => gateRecord w [true, false, false] left.val right.val

private theorem length_encodeGate {n : Nat} (w : Nat) (gate : Gate n) :
    (encodeGate w gate).length = 3 + 2 * w := by
  cases gate with
  | const value =>
    cases value <;>
      simp only [encodeGate, gateRecord, List.length_append, List.length_cons, List.length_nil,
        length_fieldBits] <;> omega
  | not src =>
    simp only [encodeGate, gateRecord, List.length_append, List.length_cons, List.length_nil,
      length_fieldBits]
    omega
  | binary op left right =>
    cases op <;>
      simp only [encodeGate, gateRecord, List.length_append, List.length_cons, List.length_nil,
        length_fieldBits] <;> omega

private def readBinaryGate (n : Nat) (op : BinaryOp) (left right : Nat) : Option (Gate n) :=
  if hl : left < n then
    if hr : right < n then some (.binary op ⟨left, hl⟩ ⟨right, hr⟩) else none
  else
    none

private def readGateFields (n : Nat) (tag : List Bool) (left right : Nat) : Option (Gate n) :=
  match tag with
  | [false, false, false] => if left = 0 ∧ right = 0 then some (.const false) else none
  | [false, false, true] => if left = 0 ∧ right = 0 then some (.const true) else none
  | [false, true, false] =>
    if h : left < n then
      if right = 0 then some (.not ⟨left, h⟩) else none
    else
      none
  | [false, true, true] => readBinaryGate n .and left right
  | [true, false, false] => readBinaryGate n .or left right
  | _ => none

/-- Read one gate record, leaving the suffix after its two operand fields. -/
public def readGate (w n : Nat) (bits : List Bool) : Option (Gate n × List Bool) := do
  let tag := bits.take 3
  let (left, bits) ← readField w (bits.drop 3)
  let (right, bits) ← readField w bits
  let gate ← readGateFields n tag left right
  return (gate, bits)

private theorem readGate_encode {n : Nat} (w : Nat) (gate : Gate n) (rest : List Bool)
    (hWires : n ≤ 2 ^ w) :
    readGate w n (encodeGate w gate ++ rest) = some (gate, rest) := by
  have hZero : 0 < 2 ^ w := Nat.two_pow_pos w
  cases gate with
  | const value =>
    cases value <;> simp [readGate, encodeGate, gateRecord, List.append_assoc,
      readField_bits, readGateFields, hZero]
  | not src =>
    have hFit := Nat.lt_of_lt_of_le src.isLt hWires
    simp [readGate, encodeGate, gateRecord, List.append_assoc, readField_bits,
      readGateFields, hFit, hZero, src.isLt]
  | binary op left right =>
    have hl := Nat.lt_of_lt_of_le left.isLt hWires
    have hr := Nat.lt_of_lt_of_le right.isLt hWires
    cases op <;> simp [readGate, encodeGate, gateRecord, List.append_assoc, readField_bits,
      readGateFields, readBinaryGate, hl, hr, left.isLt, right.isLt]

private def encodeNetwork (w : Nat) : {n m : Nat} → Network n m → List Bool
  | _, _, .empty _ => []
  | _, _, .cons gate rest => encodeGate w gate ++ encodeNetwork w rest

private theorem length_encodeNetwork {n m : Nat} (w : Nat) (network : Network n m) :
    (encodeNetwork w network).length = network.size * (3 + 2 * w) := by
  induction network with
  | empty => simp only [encodeNetwork, List.length_nil, Network.size, Nat.zero_mul]
  | cons gate rest ih =>
    simp only [encodeNetwork, List.length_append, length_encodeGate, ih, Network.size,
      Nat.add_mul, Nat.one_mul]

private structure ParsedNetwork (n count : Nat) where
  wires : Nat
  network : Network n wires
  size_eq : network.size = count

private def readNetwork (w : Nat) : (n count : Nat) →
    List Bool → Option (ParsedNetwork n count × List Bool)
  | n, 0, bits => some (⟨n, .empty n, rfl⟩, bits)
  | n, count + 1, bits => do
    let (gate, bits) ← readGate w n bits
    let (parsed, bits) ← readNetwork w (n + 1) count bits
    return (⟨parsed.wires, .cons gate parsed.network, by
      simp only [Network.size, parsed.size_eq, Nat.add_comm 1]⟩, bits)

private theorem readNetwork_encode {n m : Nat} (w : Nat) (network : Network n m)
    (suffix : List Bool) (hWires : m ≤ 2 ^ w) {count : Nat} (hCount : network.size = count) :
    readNetwork w n count (encodeNetwork w network ++ suffix) =
      some (⟨m, network, hCount⟩, suffix) := by
  induction network generalizing count with
  | empty =>
    cases hCount
    rfl
  | @cons n m gate rest ih =>
    have hInput : n ≤ 2 ^ w := Nat.le_trans (Network.cons gate rest).wires_le hWires
    have hSucc : rest.size + 1 = count := by
      rw [← hCount, Network.size, Nat.add_comm]
    cases hSucc
    simp only [encodeNetwork, List.append_assoc, readNetwork, readGate_encode w gate _ hInput,
      Option.bind_eq_bind, Option.bind_some, ih hWires rfl, Option.pure_def]

/-- Write the gate count, the fixed-width gate records, and the output wire.
The parties agree on the input arity and gate budget. Fields are little-endian. -/
public def encodeCircuit {n : Nat} (s : Nat) (c : BooleanCircuit n) : List Bool :=
  let w := circuitFieldWidth n s
  fieldBits w c.size ++ encodeNetwork w c.network ++ fieldBits w c.output.val

/-- The first field of a circuit description records its gate count. -/
public theorem fieldValue_take_encodeCircuit {n : Nat} (s : Nat) (c : BooleanCircuit n)
    (hSize : c.size ≤ s) :
    fieldValue ((encodeCircuit s c).take (circuitFieldWidth n s)) = c.size := by
  have hCount : c.size < 2 ^ circuitFieldWidth n s := Nat.lt_of_le_of_lt
    (Nat.le_trans hSize (Nat.le_add_left s n)) Nat.lt_log2_self
  rw [encodeCircuit, List.append_assoc, List.take_left' (length_fieldBits _ _),
    fieldValue_bits _ _ hCount]

private def decodeCircuitChecked (n s : Nat) (bits : List Bool) :
    Option {c : BooleanCircuit n // c.size ≤ s} := do
  let w := circuitFieldWidth n s
  let (count, bits) ← readField w bits
  if hCount : count ≤ s then
    let (parsed, bits) ← readNetwork w n count bits
    let (output, bits) ← readField w bits
    if bits.isEmpty then
      if hOutput : output < parsed.wires then
        return ⟨⟨parsed.wires, parsed.network, ⟨output, hOutput⟩⟩, by
          change parsed.network.size ≤ s
          rw [parsed.size_eq]
          exact hCount⟩
      else
        none
    else
      none
  else
    none

/-- Read exactly one description within the gate budget. References must
point to existing wires, and no bits may remain after the output. -/
public def decodeCircuit (n s : Nat) (bits : List Bool) : Option (BooleanCircuit n) :=
  (decodeCircuitChecked n s bits).map Subtype.val

@[simp] public theorem length_encodeCircuit {n : Nat} (s : Nat) (c : BooleanCircuit n) :
    (encodeCircuit s c).length =
      2 * circuitFieldWidth n s + c.size * (3 + 2 * circuitFieldWidth n s) := by
  simp only [encodeCircuit, List.length_append, length_fieldBits, length_encodeNetwork,
    BooleanCircuit.size]
  omega

public theorem length_encodeCircuit_le {n : Nat} (s : Nat) (c : BooleanCircuit n)
    (hSize : c.size ≤ s) : (encodeCircuit s c).length ≤
      2 * circuitFieldWidth n s + s * (3 + 2 * circuitFieldWidth n s) := by
  rw [length_encodeCircuit]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hSize) _

public theorem decodeCircuit_encodeCircuit {n : Nat} (s : Nat) (c : BooleanCircuit n)
    (hSize : c.size ≤ s) : decodeCircuit n s (encodeCircuit s c) = some c := by
  let w := circuitFieldWidth n s
  have hWidth : n + s < 2 ^ w := Nat.lt_log2_self
  have hWires : c.wires ≤ 2 ^ w := by
    rw [c.network.wires_eq_input_add_size]
    exact Nat.le_trans (Nat.add_le_add_left hSize n) (Nat.le_of_lt hWidth)
  have hCount : c.size < 2 ^ w := Nat.lt_of_le_of_lt
    (Nat.le_trans hSize (Nat.le_add_left s n)) hWidth
  have hOutput : c.output.val < 2 ^ w := Nat.lt_of_lt_of_le c.output.isLt hWires
  have hLast :
      readField (circuitFieldWidth n s) (fieldBits (circuitFieldWidth n s) c.output.val) =
        some (c.output.val, []) := by
    simpa only [List.append_nil] using readField_bits (circuitFieldWidth n s) c.output.val [] hOutput
  have hNetwork : readNetwork (circuitFieldWidth n s) n c.size
      (encodeNetwork (circuitFieldWidth n s) c.network ++
        fieldBits (circuitFieldWidth n s) c.output.val) =
      some (⟨c.wires, c.network, rfl⟩, fieldBits (circuitFieldWidth n s) c.output.val) :=
    readNetwork_encode (circuitFieldWidth n s) c.network _ hWires rfl
  simp only [decodeCircuit, decodeCircuitChecked, encodeCircuit, List.append_assoc,
    readField_bits (circuitFieldWidth n s) _ _ hCount, Option.bind_eq_bind, Option.bind_some,
    dite_eq_left hSize, hNetwork, hLast, List.isEmpty_nil,
    ite_true, dite_eq_left c.output.isLt, Option.pure_def, Option.map_some]

public theorem size_le_of_decodeCircuit_eq_some {n s : Nat} {bits : List Bool} {c : BooleanCircuit n}
    (h : decodeCircuit n s bits = some c) : c.size ≤ s := by
  obtain ⟨decoded, _, rfl⟩ := Option.map_eq_some_iff.mp h
  exact decoded.property

end PvsNP.Circuits
