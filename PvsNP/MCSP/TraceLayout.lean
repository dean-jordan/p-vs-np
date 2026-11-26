module

public import PvsNP.Complexity.PackedOffsets
public import PvsNP.MCSP.GateRecordRegister
public import PvsNP.MCSP.TraceViolationLanguage

/-! # Physical bit positions in packed merge trace queries -/

public section

namespace PvsNP.MCSP

open Circuits

/-- The reverse cursor position of the last bit of a forward stride-four field. -/
@[expose] def reverseGateRecordPosition (wordLength start width : Nat) : Nat :=
  wordLength - 1 - (start + 4 * (3 + 2 * width - 1))

/-- Forward stride-four reads at a record start give exactly the reverse reads
used by the register fragment. -/
theorem gateRecordLayout_of_forwardReads {word tag left right : BinaryWord} {start width : Nat}
    (hTag : tag.length = 3) (hLeft : left.length = width) (hRight : right.length = width)
    (hReads : ∀ j, j < (tag ++ left ++ right).length →
      word[start + 4 * j]? = (tag ++ left ++ right)[j]?) :
    GateRecordLayout word (reverseGateRecordPosition word.length start width) width
      tag left right := by
  refine ⟨hTag, hLeft, hRight, ?_⟩
  let record := tag ++ left ++ right
  have hLength : record.length = 3 + 2 * width := by
    simp only [record, List.length_append, hTag, hLeft, hRight]
    omega
  simpa only [reverseWindowStart, reverseGateRecordPosition, hLength, record] using
    reverseWindowReads_of_forward hReads

/-- The raw description consists of the header and gate records before padding.
Any embedding of the witness bits at stride four gives the same gate layout. -/
theorem gateRecordLayout_of_witness_forwardReads {n : Nat} (cap : Nat)
    (c : BooleanCircuit n) (word : BinaryWord) (base i : Nat) (hi : i < c.size)
    (hReads : ∀ j, j < (encodeMergeWitness cap c).length →
      word[base + 4 * j]? = (encodeMergeWitness cap c)[j]?) :
    let w := circuitFieldWidth n cap
    let fields := (c.network.traceInstructions[i]'(by simpa [BooleanCircuit.size] using hi)).fields
    let start := base + 4 * (w + i * (3 + 2 * w))
    GateRecordLayout word (reverseGateRecordPosition word.length start w) w
      (fieldBits 3 fields.opcode) (fieldBits w fields.left) (fieldBits w fields.right) := by
  let w := circuitFieldWidth n cap
  let width := 3 + 2 * w
  let offset := w + i * width
  let raw := encodeCircuit cap c
  let witness := encodeMergeWitness cap c
  have hiTrace : i < c.network.traceInstructions.length := by simpa [BooleanCircuit.size] using hi
  let fields := c.network.traceInstructions[i].fields
  let record := encodeGateFields w fields
  have hRecordLength : record.length = width := length_encodeGateFields w fields
  have hSlice : (raw.drop offset).take width = record :=
    take_drop_encodeCircuit_gateRecord cap c i hi
  have hFits : offset + width ≤ raw.length := by
    have hMul := Nat.mul_le_mul_right width (Nat.succ_le_of_lt hi)
    rw [Nat.succ_mul] at hMul
    have hRawLength : raw.length = 2 * w + c.size * width := length_encodeCircuit cap c
    unfold offset
    omega
  have hRawLe : raw.length ≤ witness.length := by
    simp only [witness, encodeMergeWitness, List.length_append]
    exact Nat.le_add_right ..
  apply gateRecordLayout_of_forwardReads (length_fieldBits ..) (length_fieldBits ..)
    (length_fieldBits ..)
  intro j hj
  change j < record.length at hj
  have hjWidth : j < width := hRecordLength ▸ hj
  have hjRaw : offset + j < raw.length := by omega
  have hRead := hReads (offset + j) (hjRaw.trans_le hRawLe)
  change word[base + 4 * (offset + j)]? = witness[offset + j]? at hRead
  have hIndex : base + 4 * (offset + j) = base + 4 * offset + 4 * j := by omega
  rw [hIndex] at hRead
  have hRawRead := congrArg (fun bits : BinaryWord ↦ bits[j]?) hSlice
  simp only [List.getElem?_take_of_lt hjWidth, List.getElem?_drop] at hRawRead
  have hWitnessRead : witness[offset + j]? = raw[offset + j]? := by
    change (raw ++ List.replicate (mergeWitnessLength n cap - raw.length) false)[offset + j]? = _
    exact List.getElem?_append_left hjRaw
  exact hRead.trans (hWitnessRead.trans hRawRead)

/-- The candidate gate records are read directly from the nested packed input. -/
theorem candidate_gateRecordLayout (r : MergeRequest) (candidate : BooleanCircuit r.arity)
    (x : Fin r.arity → Bool) (oldTrace newTrace : BinaryWord) (oldValue newValue : Bool)
    (i : Nat) (hi : i < candidate.size) :
    let request := encodeMergeRequest r
    let witness := encodeMergeWitness r.cap candidate
    let cert := encodeMergeTraceCertificate x oldTrace newTrace oldValue newValue
    let word := packedPair (packedPair request witness) cert
    let w := circuitFieldWidth r.arity r.cap
    let instruction := candidate.network.traceInstructions[i]'(by
      simpa [BooleanCircuit.size] using hi)
    let fields := instruction.fields
    let position := word.length - 1 -
      (4 * (request.length + 1 + w + i * (3 + 2 * w) + (3 + 2 * w - 1)) + 3)
    GateRecordLayout word position w (fieldBits 3 fields.opcode)
      (fieldBits w fields.left) (fieldBits w fields.right) := by
  let request := encodeMergeRequest r
  let witness := encodeMergeWitness r.cap candidate
  let cert := encodeMergeTraceCertificate x oldTrace newTrace oldValue newValue
  let word := packedPair (packedPair request witness) cert
  let base := 4 * (request.length + 1) + 3
  let w := circuitFieldWidth r.arity r.cap
  have hReads (j : Nat) (hj : j < witness.length) : word[base + 4 * j]? = witness[j]? := by
    have hIndex : base + 4 * j = 4 * (request.length + 1 + j) + 3 := by
      unfold base
      omega
    rw [hIndex]
    exact getElem?_packedPair_nested_candidate request witness cert hj
  have hLayout := gateRecordLayout_of_witness_forwardReads r.cap candidate word base i hi hReads
  dsimp only at hLayout
  have hPosition : reverseGateRecordPosition word.length (base + 4 * (w + i * (3 + 2 * w))) w =
      word.length - 1 -
        (4 * (request.length + 1 + w + i * (3 + 2 * w) + (3 + 2 * w - 1)) + 3) := by
    unfold reverseGateRecordPosition base
    omega
  rwa [hPosition] at hLayout

/-- The offset of the old witness after the request's unary fields, counter and bit. -/
@[expose] def mergeOldWitnessOffset (n cap : Nat) : Nat := 2 * n + cap + 4

theorem getElem?_encodeMergeRequest_oldWitness (r : MergeRequest) {j : Nat}
    (hj : j < (encodeMergeWitness (max 1 r.cap) r.old).length) :
    (encodeMergeRequest r)[mergeOldWitnessOffset r.arity r.cap + j]? =
      (encodeMergeWitness (max 1 r.cap) r.old)[j]? := by
  let header := unaryField r.arity ++ unaryField r.cap ++ fieldBits (r.arity + 1) r.seen ++ [r.bit]
  have hEncoding : encodeMergeRequest r =
      header ++ (encodeMergeWitness (max 1 r.cap) r.old ++ r.pref) := by
    simp only [encodeMergeRequest, header, List.append_assoc, List.singleton_append]
  have hLength : header.length = mergeOldWitnessOffset r.arity r.cap := by
    simp only [header, unaryField, List.length_append, List.length_replicate,
      List.length_singleton, length_fieldBits, mergeOldWitnessOffset]
    omega
  rw [hEncoding, List.getElem?_append_right (by omega), hLength, Nat.add_sub_cancel_left,
    List.getElem?_append_left hj]

/-- The old gate records are read inside the request field, regardless of the candidate. -/
theorem old_gateRecordLayout (r : MergeRequest) (candidateCode : BinaryWord)
    (x : Fin r.arity → Bool) (oldTrace newTrace : BinaryWord) (oldValue newValue : Bool)
    (i : Nat) (hi : i < r.old.size) :
    let request := encodeMergeRequest r
    let cert := encodeMergeTraceCertificate x oldTrace newTrace oldValue newValue
    let word := packedPair (packedPair request candidateCode) cert
    let w := circuitFieldWidth r.arity (max 1 r.cap)
    let instruction := r.old.network.traceInstructions[i]'(by simpa [BooleanCircuit.size] using hi)
    let fields := instruction.fields
    let position := word.length - 1 -
      (4 * (mergeOldWitnessOffset r.arity r.cap + w + i * (3 + 2 * w) + (3 + 2 * w - 1)) + 3)
    GateRecordLayout word position w (fieldBits 3 fields.opcode)
      (fieldBits w fields.left) (fieldBits w fields.right) := by
  let request := encodeMergeRequest r
  let old := encodeMergeWitness (max 1 r.cap) r.old
  let offset := mergeOldWitnessOffset r.arity r.cap
  let cert := encodeMergeTraceCertificate x oldTrace newTrace oldValue newValue
  let word := packedPair (packedPair request candidateCode) cert
  let base := 4 * offset + 3
  let w := circuitFieldWidth r.arity (max 1 r.cap)
  have hReqLength : request.length = offset + old.length + r.pref.length := by
    rw [show request = encodeMergeRequest r by rfl, length_encodeMergeRequest]
    rw [show old = encodeMergeWitness (max 1 r.cap) r.old by rfl,
      length_encodeMergeWitness _ _ r.old_size_le]
    rfl
  have hReads (j : Nat) (hj : j < old.length) : word[base + 4 * j]? = old[j]? := by
    have hIndex : base + 4 * j = 4 * (offset + j) + 3 := by
      unfold base
      omega
    rw [hIndex]
    exact (getElem?_packedPair_nested_request request candidateCode cert (by omega)).trans
      (getElem?_encodeMergeRequest_oldWitness r hj)
  have hLayout :=
    gateRecordLayout_of_witness_forwardReads (max 1 r.cap) r.old word base i hi hReads
  dsimp only at hLayout
  have hPosition : reverseGateRecordPosition word.length (base + 4 * (w + i * (3 + 2 * w))) w =
      word.length - 1 - (4 * (offset + w + i * (3 + 2 * w) + (3 + 2 * w - 1)) + 3) := by
    unfold reverseGateRecordPosition base
    omega
  rwa [hPosition] at hLayout

/-- Forward bit address of the first old wire value in the outer packed word. -/
@[expose] def mergeOldTraceStart (query : BinaryWord) (n : Nat) : Nat :=
  2 * (query.length + 1) + 2 * (n + 1) + 1

/-- Forward bit address of the first new wire value in the outer packed word. -/
@[expose] def mergeNewTraceStart (query : BinaryWord) (n oldLength : Nat) : Nat :=
  mergeOldTraceStart query n + 2 * oldLength

theorem getElem?_packedMergeTrace_old {n : Nat} (query : BinaryWord) (x : Fin n → Bool)
    (oldTrace newTrace : BinaryWord) (oldValue newValue : Bool) {i : Nat}
    (hi : i < oldTrace.length) :
    (packedPair query (encodeMergeTraceCertificate x oldTrace newTrace oldValue newValue))[
      mergeOldTraceStart query n + 2 * i]? = oldTrace[i]? := by
  have hIndex : mergeOldTraceStart query n + 2 * i =
      2 * (query.length + 1) + 2 * (n + 1 + i) + 1 := by
    unfold mergeOldTraceStart
    omega
  rw [hIndex, getElem?_packedPair_right, encodeMergeTraceCertificate, List.append_assoc,
    List.append_assoc, List.getElem?_append_right (by simp only [length_mergeRowField]; omega),
    length_mergeRowField, Nat.add_sub_cancel_left, List.getElem?_append_left hi]

theorem getElem?_packedMergeTrace_new {n : Nat} (query : BinaryWord) (x : Fin n → Bool)
    (oldTrace newTrace : BinaryWord) (oldValue newValue : Bool) {i : Nat}
    (hi : i < newTrace.length) :
    (packedPair query (encodeMergeTraceCertificate x oldTrace newTrace oldValue newValue))[
      mergeNewTraceStart query n oldTrace.length + 2 * i]? = newTrace[i]? := by
  have hIndex : mergeNewTraceStart query n oldTrace.length + 2 * i =
      2 * (query.length + 1) + 2 * (n + 1 + (oldTrace.length + i)) + 1 := by
    unfold mergeNewTraceStart mergeOldTraceStart
    omega
  rw [hIndex, getElem?_packedPair_right, encodeMergeTraceCertificate, List.append_assoc,
    List.append_assoc, List.getElem?_append_right (by simp only [length_mergeRowField]; omega),
    length_mergeRowField, Nat.add_sub_cancel_left, List.getElem?_append_right (by omega),
    Nat.add_sub_cancel_left, List.getElem?_append_left hi]

end PvsNP.MCSP
