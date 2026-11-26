module

public import PvsNP.Circuits.DescriptionLayout

import all PvsNP.Circuits.Description
import all PvsNP.Circuits.DescriptionLayout

/-! # Check exact circuit descriptions by bounded record windows -/

public section

namespace PvsNP.Circuits

/-- The encoder inverts the value of every complete little-endian field. -/
theorem fieldBits_length_fieldValue (bits : List Bool) :
    fieldBits bits.length (fieldValue bits) = bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    have hBound := Bool.toNat_le b
    have hHalf : (b.toNat + 2 * fieldValue bits) / 2 = fieldValue bits := by omega
    have hLow : decide ((b.toNat + 2 * fieldValue bits) % 2 = 1) = b := by
      cases b
      · simp only [Bool.toNat_false, Nat.zero_add, Nat.mul_mod_right, Nat.zero_ne_one, decide_false]
      · simp only [Bool.toNat_true, decide_eq_true_eq]
        omega
    simp only [List.length_cons, fieldBits, fieldValue, hLow, hHalf, ih]

/-- Exact bit length at a specified field width and gate count. -/
@[expose] def circuitDescriptionLength (width count : Nat) : Nat :=
  2 * width + count * (3 + 2 * width)

/-- The claimed gate count in the initial fixed-width field. -/
@[expose] def circuitDescriptionCount (n cap : Nat) (word : List Bool) : Nat :=
  fieldValue (word.take (circuitFieldWidth n cap))

/-- The length through the output field, excluding any fixed-budget padding. -/
@[expose] def circuitDescriptionCodeLength (n cap : Nat) (word : List Bool) : Nat :=
  circuitDescriptionLength (circuitFieldWidth n cap) (circuitDescriptionCount n cap word)

/-- The output wire is stored immediately after the gate records. -/
@[expose] def circuitDescriptionOutput (width count : Nat) (word : List Bool) : Nat :=
  fieldValue ((word.drop (width + count * (3 + 2 * width))).take width)

private def gateWindow (width wires : Nat) (bits : List Bool) : Option (Gate wires) :=
  let fields := decodeGateFields width (bits.take (3 + 2 * width))
  gateFromFields wires fields.opcode fields.left fields.right

/-- Read record `i`, using the inputs and its predecessors as the only available wires. -/
def circuitDescriptionGateAt (width n : Nat) (word : List Bool) (i : Nat) :
    Option (Gate (n + i)) :=
  gateWindow width (n + i) (word.drop (width + i * (3 + 2 * width)))

/-- These are the exact checks on the header, records, and output of an unpadded word. -/
structure CircuitDescriptionValid (n cap : Nat) (word : List Bool) : Prop where
  count_le : circuitDescriptionCount n cap word ≤ cap
  length_eq : word.length =
    circuitDescriptionLength (circuitFieldWidth n cap) (circuitDescriptionCount n cap word)
  gateAt : ∀ i, i < circuitDescriptionCount n cap word →
    (circuitDescriptionGateAt (circuitFieldWidth n cap) n word i).isSome
  output_lt : circuitDescriptionOutput (circuitFieldWidth n cap)
    (circuitDescriptionCount n cap word) word < n + circuitDescriptionCount n cap word

private theorem take_gate_subfields (w : Nat) (bits : List Bool) :
    decodeGateFields w (bits.take (3 + 2 * w)) = decodeGateFields w bits := by
  simp only [decodeGateFields, List.take_take, List.drop_take, Nat.min_eq_left (show 3 ≤ 3 + 2*w
    by omega), show 3 + 2*w - 3 = 2*w by omega, show 2*w - w = w by omega,
    Nat.min_eq_left (show w ≤ 2*w by omega), Nat.min_self]

/-- A gate record is interpreted entirely from its bounded slice. -/
theorem circuitDescriptionGateAt_eq_fields (width n : Nat) (word : List Bool) (i : Nat) :
    let fields := decodeGateFields width
      (((word.drop (width + i * (3 + 2 * width))).take (3 + 2 * width)))
    circuitDescriptionGateAt width n word i =
      gateFromFields (n + i) fields.opcode fields.left fields.right := by
  rw [circuitDescriptionGateAt, gateWindow]

private theorem readField_eq_window (width : Nat) (bits : List Bool)
    (hLen : width ≤ bits.length) :
    readField width bits = some (fieldValue (bits.take width), bits.drop width) := by
  rw [readField, ite_eq_left hLen]

private theorem readGate_eq_window (width n : Nat) (bits : List Bool)
    (hLen : 3 + 2 * width ≤ bits.length) :
    readGate width n bits =
      (gateWindow width n bits).map (fun g ↦ (g, bits.drop (3 + 2 * width))) := by
  have hLeft : width ≤ (bits.drop 3).length := by
    simp only [List.length_drop]
    omega
  have hRight : width ≤ ((bits.drop 3).drop width).length := by
    simp only [List.length_drop]
    omega
  have hTag : (bits.take 3).length = 3 := List.length_take_of_le (by omega)
  have hDrop : (((bits.drop 3).drop width).drop width) = bits.drop (3 + 2 * width) := by
    simp only [List.drop_drop]
    congr 1
    omega
  have hInterpret (left right : Nat) :
      gateFromFields n (fieldValue (bits.take 3)) left right =
        readGateFields n (bits.take 3) left right := by
    let tag := bits.take 3
    change gateFromFields n (fieldValue tag) left right = readGateFields n tag left right
    obtain ⟨a, b, c, h⟩ := List.length_eq_three.mp hTag
    have h' : tag = [a, b, c] := h
    rw [h']
    cases a <;> cases b <;> cases c <;> rfl
  rw [readGate, readField_eq_window _ _ hLeft, gateWindow, take_gate_subfields]
  simp only [Option.bind_eq_bind, Option.bind_some, readField_eq_window _ _ hRight,
    hDrop, decodeGateFields, ← hInterpret]
  cases gateFromFields n (fieldValue (bits.take 3)) (fieldValue ((bits.drop 3).take width))
    (fieldValue (((bits.drop 3).drop width).take width)) <;> rfl

private theorem readGate_eq_none_of_short (width n : Nat) (bits : List Bool)
    (hShort : bits.length < 3 + 2 * width) (hw : 0 < width) : readGate width n bits = none := by
  by_cases hLeft : width ≤ (bits.drop 3).length
  · have hRight : ¬width ≤ ((bits.drop 3).drop width).length := by
      simp only [List.length_drop] at hLeft ⊢
      omega
    simp only [readGate, readField, ite_eq_left hLeft, Option.bind_eq_bind, Option.bind_some,
      ite_eq_right hRight, Option.bind_none]
  · simp only [readGate, readField, ite_eq_right hLeft, Option.bind_eq_bind, Option.bind_none]

private theorem fields_of_gateFromFields {n opcode a b : Nat} {gate : Gate n} (hOp : opcode < 8)
    (h : gateFromFields n opcode a b = some gate) :
    gate.traceInstruction.fields = ⟨opcode, a, b⟩ := by
  have hCases : opcode = 0 ∨ opcode = 1 ∨ opcode = 2 ∨ opcode = 3 ∨ opcode = 4 ∨
      opcode = 5 ∨ opcode = 6 ∨ opcode = 7 := by omega
  rcases hCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [gateFromFields] at h <;>
    (repeat' split at h)
  all_goals
    first
    | contradiction
    | have hSame := Option.some.inj h
      subst gate
      simp_all [Gate.traceInstruction, WireTraceInstruction.fields]

private theorem fieldValue_lt (bits : List Bool) : fieldValue bits < 2 ^ bits.length := by
  induction bits with
  | nil => decide
  | cons bit bits ih =>
    have := Bool.toNat_le bit
    simp only [fieldValue, List.length_cons, Nat.pow_succ]
    omega

private theorem readGate_sound {width n : Nat} {bits rest : List Bool} {gate : Gate n}
    (hw : 0 < width) (h : readGate width n bits = some (gate, rest)) :
    bits = encodeGate width gate ++ rest := by
  let recordWidth := 3 + 2 * width
  have hLen : recordWidth ≤ bits.length := by
    by_cases hFits : recordWidth ≤ bits.length
    · exact hFits
    · rw [readGate_eq_none_of_short width n bits (Nat.lt_of_not_ge hFits) hw] at h
      contradiction
  rw [readGate_eq_window width n bits hLen] at h
  obtain ⟨parsed, hParsed, hResult⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hResult
  let tag := bits.take 3
  let left := (bits.drop 3).take width
  let right := ((bits.drop 3).drop width).take width
  have hTag : tag.length = 3 := List.length_take_of_le (by dsimp [recordWidth] at hLen; omega)
  have hLeft : left.length = width := by
    apply List.length_take_of_le
    simp only [List.length_drop]
    dsimp [recordWidth] at hLen
    omega
  have hRight : right.length = width := by
    apply List.length_take_of_le
    simp only [List.length_drop]
    dsimp [recordWidth] at hLen
    omega
  have hOp : fieldValue tag < 8 := by
    simpa only [hTag, show 2 ^ (3 : Nat) = (8 : Nat) by decide] using fieldValue_lt tag
  rw [gateWindow, take_gate_subfields, decodeGateFields] at hParsed
  change gateFromFields n (fieldValue tag) (fieldValue left) (fieldValue right) = some parsed
    at hParsed
  have hFields := fields_of_gateFromFields hOp hParsed
  have hTagBits : fieldBits 3 (fieldValue tag) = tag := by
    simpa only [hTag] using fieldBits_length_fieldValue tag
  have hLeftBits : fieldBits width (fieldValue left) = left := by
    simpa only [hLeft] using fieldBits_length_fieldValue left
  have hRightBits : fieldBits width (fieldValue right) = right := by
    simpa only [hRight] using fieldBits_length_fieldValue right
  rw [encodeGate_eq_encodeGateFields, hFields, encodeGateFields]
  change bits = fieldBits 3 (fieldValue tag) ++ fieldBits width (fieldValue left) ++
    fieldBits width (fieldValue right) ++ bits.drop recordWidth
  rw [hTagBits, hLeftBits, hRightBits]
  have hSuffix : bits.drop recordWidth = (((bits.drop 3).drop width).drop width) := by
    simp only [List.drop_drop, recordWidth]
    congr 1
    omega
  rw [hSuffix]
  simp only [tag, left, right, List.append_assoc, List.take_append_drop]

private theorem readNetwork_sound (width n count : Nat) (bits rest : List Bool)
    (parsed : ParsedNetwork n count) (hw : 0 < width)
    (h : readNetwork width n count bits = some (parsed, rest)) :
    bits = encodeNetwork width parsed.network ++ rest := by
  induction count generalizing n bits with
  | zero =>
    simp only [readNetwork, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | succ count ih =>
    simp only [readNetwork, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
    obtain ⟨⟨gate, middle⟩, hGate, ⟨tail, suffix⟩, hTail, hResult⟩ := h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hResult)
    have hMiddle : middle = encodeNetwork width tail.network ++ suffix := ih _ _ _ hTail
    change bits = encodeNetwork width (.cons gate tail.network) ++ suffix
    rw [readGate_sound hw hGate, hMiddle, encodeNetwork, List.append_assoc]

private theorem readField_sound {width a : Nat} {bits rest : List Bool}
    (h : readField width bits = some (a, rest)) : bits = fieldBits width a ++ rest := by
  unfold readField at h
  split at h
  · rename_i hWidth
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hLength := List.length_take_of_le (l := bits) hWidth
    have hBits := fieldBits_length_fieldValue (bits.take width)
    rw [hLength] at hBits
    rw [hBits, List.take_append_drop]
  · contradiction

/-- A successful exact decoder produces the unique canonical encoding of its circuit. -/
theorem decodeCircuit_eq_some_iff_canonical {n cap : Nat} {word : List Bool}
    {c : BooleanCircuit n} : decodeCircuit n cap word = some c ↔
      c.size ≤ cap ∧ word = encodeCircuit cap c := by
  constructor
  · intro h
    have hw : 0 < circuitFieldWidth n cap := Nat.succ_pos _
    obtain ⟨checked, hChecked, rfl⟩ := Option.map_eq_some_iff.mp h
    have hSize := checked.property
    simp only [decodeCircuitChecked, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def] at hChecked
    obtain ⟨⟨count, body⟩, hCountField, hBody⟩ := hChecked
    by_cases hCount : count ≤ cap
    · simp only [dite_eq_left hCount, Option.bind_eq_some_iff] at hBody
      obtain ⟨⟨parsed, outputField⟩, hNetwork, ⟨output, tail⟩, hOutputField, hFinish⟩ := hBody
      cases tail with
      | nil =>
        by_cases hOutput : output < parsed.wires
        · simp only [List.isEmpty_nil, ite_true, dite_eq_left hOutput, Option.some.injEq] at hFinish
          subst checked
          refine ⟨hSize, ?_⟩
          change readField (circuitFieldWidth n cap) outputField = some (output, []) at hOutputField
          rw [readField_sound hCountField, readNetwork_sound _ _ _ _ _ _ hw hNetwork,
            readField_sound hOutputField, List.append_nil, encodeCircuit, List.append_assoc]
          change fieldBits (circuitFieldWidth n cap) count ++ _ =
            fieldBits (circuitFieldWidth n cap) parsed.network.size ++ _
          rw [parsed.size_eq]
        · simp [List.isEmpty_nil, hOutput] at hFinish
      | cons a tail => simp [List.isEmpty_cons] at hFinish
    · simp [hCount] at hBody
  · rintro ⟨hSize, rfl⟩
    exact decodeCircuit_encodeCircuit cap c hSize

private theorem readNetwork_of_windows (width n count : Nat) (bits : List Bool)
    (hLength : count * (3 + 2 * width) ≤ bits.length)
    (hGates : ∀ i, i < count →
      (gateWindow width (n + i) (bits.drop (i * (3 + 2 * width)))).isSome) :
    ∃ parsed : ParsedNetwork n count,
      readNetwork width n count bits = some (parsed, bits.drop (count * (3 + 2 * width))) := by
  induction count generalizing n bits with
  | zero => exact ⟨⟨n, .empty n, rfl⟩, by simp only [Nat.zero_mul, List.drop_zero, readNetwork]⟩
  | succ count ih =>
    let recordWidth := 3 + 2 * width
    have hFirst : (gateWindow width n bits).isSome := by simpa using hGates 0 (by omega)
    obtain ⟨gate, hGate⟩ := Option.isSome_iff_exists.mp hFirst
    have hLength' : count * recordWidth ≤ (bits.drop recordWidth).length := by
      change (count + 1) * recordWidth ≤ bits.length at hLength
      rw [Nat.succ_mul] at hLength
      simp only [List.length_drop]
      omega
    have hGates' (i : Nat) (hi : i < count) :
        (gateWindow width (n + 1 + i) ((bits.drop recordWidth).drop (i * recordWidth))).isSome := by
      rw [List.drop_drop, Nat.add_comm recordWidth, ← Nat.succ_mul, Nat.add_right_comm n]
      exact hGates (i + 1) (by omega)
    obtain ⟨parsed, hRest⟩ := ih (n + 1) (bits.drop recordWidth) hLength' hGates'
    have hRecord : recordWidth ≤ bits.length := by
      change (count + 1) * recordWidth ≤ bits.length at hLength
      rw [Nat.succ_mul] at hLength
      omega
    refine ⟨⟨parsed.wires, .cons gate parsed.network, ?_⟩, ?_⟩
    · simp only [Network.size, parsed.size_eq, Nat.add_comm 1]
    · rw [readNetwork, readGate_eq_window width n bits hRecord, hGate, Option.map_some]
      simp only [Option.bind_eq_bind, Option.bind_some]
      have hRest' : readNetwork width (n + 1) count (bits.drop (3 + 2 * width)) =
          some (parsed, (bits.drop recordWidth).drop (count * recordWidth)) := hRest
      rw [hRest', List.drop_drop, Nat.add_comm recordWidth, ← Nat.succ_mul]
      rfl

/-- Every word passing the bounded local checks has an exact decoding. -/
theorem CircuitDescriptionValid.exists_decode {n cap : Nat} {word : List Bool}
    (h : CircuitDescriptionValid n cap word) : ∃ c, decodeCircuit n cap word = some c := by
  let width := circuitFieldWidth n cap
  let count := circuitDescriptionCount n cap word
  let body := word.drop width
  have hLength : word.length = 2 * width + count * (3 + 2 * width) := h.length_eq
  have hHeader : width ≤ word.length := by omega
  have hBody : count * (3 + 2 * width) ≤ body.length := by
    simp only [body, List.length_drop]
    omega
  have hGates (i : Nat) (hi : i < count) :
      (gateWindow width (n + i) (body.drop (i * (3 + 2 * width)))).isSome := by
    simpa only [body, List.drop_drop, circuitDescriptionGateAt] using h.gateAt i hi
  obtain ⟨parsed, hParsed⟩ := readNetwork_of_windows width n count body hBody hGates
  let outputField := body.drop (count * (3 + 2 * width))
  let output := circuitDescriptionOutput width count word
  have hOutput : fieldValue (outputField.take width) = output := by
    simp only [outputField, body, List.drop_drop, output, circuitDescriptionOutput]
  have hOutputLength : outputField.length = width := by
    simp only [outputField, body, List.drop_drop, List.length_drop]
    omega
  have hOutputRead : readField width outputField = some (output, []) := by
    rw [readField_eq_window _ _ (Nat.le_of_eq hOutputLength.symm), hOutput,
      List.drop_eq_nil_of_le (Nat.le_of_eq hOutputLength)]
  have hWires : parsed.wires = n + count := by
    rw [parsed.network.wires_eq_input_add_size, parsed.size_eq]
  have hOutputBound : output < parsed.wires := hWires ▸ h.output_lt
  let c : BooleanCircuit n := ⟨parsed.wires, parsed.network, ⟨output, hOutputBound⟩⟩
  have hCount : count ≤ cap := h.count_le
  have hCountRead : readField width word = some (count, body) := readField_eq_window _ _ hHeader
  refine ⟨c, ?_⟩
  have hParsed' : readNetwork (circuitFieldWidth n cap) n count body =
      some (parsed, outputField) := hParsed
  dsimp only [width] at hCountRead hOutputRead
  rw [decodeCircuit, decodeCircuitChecked, hCountRead]
  simp only [Option.bind_eq_bind, Option.bind_some, dite_eq_left hCount, hParsed', hOutputRead,
    List.isEmpty_nil, ite_true, dite_eq_left hOutputBound, Option.pure_def, Option.map_some, c]

/-- The claimed count equals the number of gates reconstructed by an exact decode. -/
theorem circuitDescriptionCount_of_decode {n cap : Nat} {word : List Bool} {c : BooleanCircuit n}
    (h : decodeCircuit n cap word = some c) : circuitDescriptionCount n cap word = c.size := by
  obtain ⟨hSize, rfl⟩ := decodeCircuit_eq_some_iff_canonical.mp h
  exact fieldValue_take_encodeCircuit cap c hSize

/-- The output field determines the output wire of an exact decode. -/
theorem circuitDescriptionOutput_of_decode {n cap : Nat} {word : List Bool} {c : BooleanCircuit n}
    (h : decodeCircuit n cap word = some c) :
    circuitDescriptionOutput (circuitFieldWidth n cap) (circuitDescriptionCount n cap word) word =
      c.output.val := by
  rw [circuitDescriptionCount_of_decode h]
  obtain ⟨hSize, rfl⟩ := decodeCircuit_eq_some_iff_canonical.mp h
  have hWires : c.wires ≤ n + cap := by
    rw [c.network.wires_eq_input_add_size]
    exact Nat.add_le_add_left hSize n
  have hFit : c.output.val < 2 ^ circuitFieldWidth n cap :=
    (c.output.isLt.trans_le hWires).trans Nat.lt_log2_self
  rw [circuitDescriptionOutput, drop_encodeCircuit_gateRecords,
    List.take_of_length_le (by rw [length_fieldBits]), fieldValue_bits _ _ hFit]

/-- Bounded record decoding reconstructs the corresponding trace instruction. -/
theorem circuitDescriptionGateAt_of_decode {n cap : Nat} {word : List Bool} {c : BooleanCircuit n}
    (h : decodeCircuit n cap word = some c) (i : Nat) (hi : i < c.size) :
    (circuitDescriptionGateAt (circuitFieldWidth n cap) n word i).map Gate.traceInstruction =
      c.network.traceInstructions[i]? := by
  obtain ⟨hSize, rfl⟩ := decodeCircuit_eq_some_iff_canonical.mp h
  rw [circuitDescriptionGateAt_eq_fields,
    decodeGateFields_encodeCircuit_gateRecord cap c hSize i hi]
  have hiTrace : i < c.network.traceInstructions.length := by
    simpa [BooleanCircuit.size] using hi
  rw [List.getElem?_eq_getElem hiTrace]
  exact c.network.gateFromFields_traceInstructionAt i hiTrace

/-- The canonical encoding passes the local count, gate, and output checks. -/
theorem circuitDescriptionValid_encode {n cap : Nat} (c : BooleanCircuit n) (hSize : c.size ≤ cap) :
    CircuitDescriptionValid n cap (encodeCircuit cap c) := by
  have hDecoded := decodeCircuit_encodeCircuit cap c hSize
  have hCount := circuitDescriptionCount_of_decode hDecoded
  have hWires : c.wires = n + c.size := c.network.wires_eq_input_add_size
  refine ⟨hCount ▸ hSize, ?_, ?_, ?_⟩
  · rw [hCount, length_encodeCircuit, circuitDescriptionLength]
  · intro i hi
    rw [hCount] at hi
    have hTrace : i < c.network.traceInstructions.length := by simpa [BooleanCircuit.size] using hi
    have hGate := circuitDescriptionGateAt_of_decode hDecoded i hi
    rw [List.getElem?_eq_getElem hTrace] at hGate
    obtain ⟨_, hRead, _⟩ := Option.map_eq_some_iff.mp hGate
    exact Option.isSome_iff_exists.mpr ⟨_, hRead⟩
  · rw [circuitDescriptionOutput_of_decode hDecoded, hCount, ← hWires]
    exact c.output.isLt

/-- A raw unpadded word is valid exactly when it is the canonical encoding
of a circuit within the stated budget. -/
theorem circuitDescriptionValid_iff_canonical {n cap : Nat} {word : List Bool} :
    CircuitDescriptionValid n cap word ↔ ∃ c : BooleanCircuit n,
      c.size ≤ cap ∧ word = encodeCircuit cap c := by
  constructor
  · intro h
    obtain ⟨c, hDecode⟩ := h.exists_decode
    exact ⟨c, decodeCircuit_eq_some_iff_canonical.mp hDecode⟩
  · rintro ⟨c, hSize, rfl⟩
    exact circuitDescriptionValid_encode c hSize

/-- A fixed-budget word has the same local checks as an unpadded description,
with a zero suffix up to the total length determined by the budget. -/
structure PaddedCircuitDescriptionValid (n cap : Nat) (word : List Bool) : Prop where
  length_eq : word.length = circuitDescriptionLength (circuitFieldWidth n cap) cap
  count_le : circuitDescriptionCount n cap word ≤ cap
  output_lt : circuitDescriptionOutput (circuitFieldWidth n cap)
    (circuitDescriptionCount n cap word) word < n + circuitDescriptionCount n cap word
  gateAt : ∀ i, i < circuitDescriptionCount n cap word →
    (circuitDescriptionGateAt (circuitFieldWidth n cap) n word i).isSome
  padding_zero : (word.drop (circuitDescriptionCodeLength n cap word)).all (!·)

private theorem slice_take_of_le (bits : List Bool) {start width limit : Nat}
    (hFits : start + width ≤ limit) :
    ((bits.take limit).drop start).take width = (bits.drop start).take width := by
  rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)]

private theorem circuitDescriptionLength_mono (width : Nat) {count cap : Nat} (h : count ≤ cap) :
    circuitDescriptionLength width count ≤ circuitDescriptionLength width cap :=
  Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

/-- Trimming at the decoded output preserves the gate-count header. -/
theorem circuitDescriptionCount_trim (n cap : Nat) (word : List Bool) :
    circuitDescriptionCount n cap (word.take (circuitDescriptionCodeLength n cap word)) =
      circuitDescriptionCount n cap word := by
  let width := circuitFieldWidth n cap
  let count := circuitDescriptionCount n cap word
  change fieldValue ((word.take (circuitDescriptionLength width count)).take width) =
    fieldValue (word.take width)
  rw [List.take_take, Nat.min_eq_left]
  unfold circuitDescriptionLength
  omega

/-- Trimming at the decoded output also preserves the output field. -/
theorem circuitDescriptionOutput_trim (width count : Nat) (word : List Bool) :
    circuitDescriptionOutput width count (word.take (circuitDescriptionLength width count)) =
      circuitDescriptionOutput width count word := by
  unfold circuitDescriptionOutput
  rw [slice_take_of_le]
  unfold circuitDescriptionLength
  omega

/-- Each record preceding the decoded output is preserved by trimming. -/
theorem circuitDescriptionGateAt_trim (width n count : Nat) (word : List Bool) (i : Nat)
    (hi : i < count) :
    circuitDescriptionGateAt width n (word.take (circuitDescriptionLength width count)) i =
      circuitDescriptionGateAt width n word i := by
  simp only [circuitDescriptionGateAt, gateWindow]
  rw [slice_take_of_le]
  have hRecord : (i + 1) * (3 + 2 * width) ≤ count * (3 + 2 * width) :=
    Nat.mul_le_mul_right _ hi
  rw [Nat.succ_mul] at hRecord
  unfold circuitDescriptionLength
  omega

/-- The padded checks amount to the fixed length, a zero suffix, and the
ordinary checks on the prefix bounded by the header. -/
theorem paddedCircuitDescriptionValid_iff_trim {n cap : Nat} {word : List Bool} :
    PaddedCircuitDescriptionValid n cap word ↔
      word.length = circuitDescriptionLength (circuitFieldWidth n cap) cap ∧
      (word.drop (circuitDescriptionCodeLength n cap word)).all (!·) ∧
      CircuitDescriptionValid n cap (word.take (circuitDescriptionCodeLength n cap word)) := by
  let width := circuitFieldWidth n cap
  let count := circuitDescriptionCount n cap word
  let codeLength := circuitDescriptionCodeLength n cap word
  have hCount : circuitDescriptionCount n cap (word.take codeLength) = count :=
    circuitDescriptionCount_trim n cap word
  change PaddedCircuitDescriptionValid n cap word ↔
    word.length = circuitDescriptionLength width cap ∧ (word.drop codeLength).all (!·) ∧
    CircuitDescriptionValid n cap (word.take codeLength)
  constructor
  · intro h
    have hFit : codeLength ≤ word.length := h.length_eq ▸
      circuitDescriptionLength_mono width h.count_le
    refine ⟨h.length_eq, h.padding_zero, ⟨hCount ▸ h.count_le, ?_, ?_, ?_⟩⟩
    · rw [List.length_take_of_le hFit, hCount]
      rfl
    · intro i hi
      rw [hCount] at hi
      rw [show codeLength = circuitDescriptionLength width count from rfl,
        circuitDescriptionGateAt_trim _ _ _ _ _ hi]
      exact h.gateAt i hi
    · rw [hCount, show codeLength = circuitDescriptionLength width count from rfl,
        circuitDescriptionOutput_trim]
      exact h.output_lt
  · rintro ⟨hLength, hZero, h⟩
    have hCountLe : count ≤ cap := by simpa only [hCount] using h.count_le
    refine ⟨hLength, hCountLe, ?_, ?_, hZero⟩
    · have hOutput := h.output_lt
      rw [hCount] at hOutput
      change circuitDescriptionOutput width count
        (word.take (circuitDescriptionLength width count)) < n + count at hOutput
      rwa [circuitDescriptionOutput_trim] at hOutput
    · intro i hi
      have h' := h.gateAt i (hCount.symm ▸ hi)
      rw [show codeLength = circuitDescriptionLength width count from rfl,
        circuitDescriptionGateAt_trim _ _ _ _ _ hi] at h'
      exact h'

private theorem eq_replicate_false_of_all_not (bits : List Bool) (h : bits.all (!·)) :
    bits = List.replicate bits.length false := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    cases bit with
    | false =>
      simp only [List.all_cons, Bool.not_false, Bool.true_and] at h
      simp only [List.length_cons, List.replicate_succ, List.cons.injEq, true_and]
      exact ih h
    | true => simp only [List.all_cons, Bool.not_true, Bool.false_and, Bool.false_eq_true] at h

/-- Successful checks reconstruct exactly one padded canonical word. -/
theorem paddedCircuitDescriptionValid_iff_canonical {n cap : Nat} {word : List Bool} :
    PaddedCircuitDescriptionValid n cap word ↔ ∃ c : BooleanCircuit n, c.size ≤ cap ∧
      word = encodeCircuit cap c ++ List.replicate
        (circuitDescriptionLength (circuitFieldWidth n cap) cap - (encodeCircuit cap c).length)
        false := by
  let width := circuitFieldWidth n cap
  let count := circuitDescriptionCount n cap word
  let codeLength := circuitDescriptionCodeLength n cap word
  rw [paddedCircuitDescriptionValid_iff_trim]
  constructor
  · rintro ⟨hLength, hZero, hTrim⟩
    obtain ⟨c, hDecode⟩ := hTrim.exists_decode
    obtain ⟨hSize, hCode⟩ := decodeCircuit_eq_some_iff_canonical.mp hDecode
    have hCount : circuitDescriptionCount n cap (word.take codeLength) = count :=
      circuitDescriptionCount_trim n cap word
    have hSizeEq : count = c.size := hCount.symm.trans (circuitDescriptionCount_of_decode hDecode)
    have hCodeLength : codeLength = (encodeCircuit cap c).length := by
      rw [length_encodeCircuit]
      change circuitDescriptionLength width count = _
      rw [hSizeEq, circuitDescriptionLength]
    have hPadLength : (word.drop codeLength).length =
        circuitDescriptionLength width cap - (encodeCircuit cap c).length := by
      rw [List.length_drop, hLength, hCodeLength]
    have hSuffix : word.drop codeLength = List.replicate
        (circuitDescriptionLength width cap - (encodeCircuit cap c).length) false := by
      rw [← hPadLength]
      exact eq_replicate_false_of_all_not _ hZero
    change word.take codeLength = encodeCircuit cap c at hCode
    refine ⟨c, hSize, ?_⟩
    calc
      word = word.take codeLength ++ word.drop codeLength := (List.take_append_drop _ _).symm
      _ = _ := by rw [hCode, hSuffix]
  · rintro ⟨c, hSize, rfl⟩
    let code := encodeCircuit cap c
    let pad := List.replicate (circuitDescriptionLength width cap - code.length) false
    have hLength : code.length ≤ circuitDescriptionLength width cap :=
      length_encodeCircuit_le _ _ hSize
    have hHeader : width ≤ code.length := by
      rw [show code = encodeCircuit cap c from rfl, length_encodeCircuit]
      dsimp only [width]
      omega
    have hCount : circuitDescriptionCount n cap (code ++ pad) = c.size := by
      rw [circuitDescriptionCount, List.take_append_of_le_length hHeader]
      exact fieldValue_take_encodeCircuit cap c hSize
    let total := circuitDescriptionLength width (circuitDescriptionCount n cap (code ++ pad))
    have hCodeLength : total = code.length := by
      dsimp only [total]
      rw [hCount, show code = encodeCircuit cap c from rfl, length_encodeCircuit,
        circuitDescriptionLength]
    change (code ++ pad).length = circuitDescriptionLength width cap ∧
      ((code ++ pad).drop total).all (!·) ∧ CircuitDescriptionValid n cap ((code ++ pad).take total)
    rw [hCodeLength, List.take_left, List.drop_left]
    refine ⟨?_, ?_, circuitDescriptionValid_encode c hSize⟩
    · simp only [pad, List.length_append, List.length_replicate]
      omega
    · simp [pad, List.all_replicate]

end PvsNP.Circuits
