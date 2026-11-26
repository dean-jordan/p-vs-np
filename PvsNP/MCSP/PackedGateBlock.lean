module

public import PvsNP.MCSP.GateBlockRegister
public import PvsNP.MCSP.TraceLayout

/-! # Preparation of the candidate gate scan in the packed input -/

public section

namespace PvsNP.MCSP

open Circuits RegisterMachine.Fragment

/-- The last bit of record `i` in the candidate field, in forward input order. -/
@[expose] def candidateGateFinalBit (requestLength w i : Nat) : Nat :=
  4 * (requestLength + 1 + w + i * (3 + 2 * w) + (3 + 2 * w - 1)) + 3

private theorem candidateGateFinalBit_lt (r : MergeRequest) (c : BooleanCircuit r.arity)
    (cert : BinaryWord) (i : Nat) (hi : i < c.size) :
    let request := encodeMergeRequest r
    let code := encodeMergeWitness r.cap c
    let w := circuitFieldWidth r.arity r.cap
    candidateGateFinalBit request.length w i <
      (packedPair (packedPair request code) cert).length := by
  dsimp only
  let w := circuitFieldWidth r.arity r.cap
  let width := 3 + 2 * w
  have hPos : 0 < width := by unfold width; omega
  have hMul := Nat.mul_le_mul_right width (Nat.succ_le_of_lt hi)
  rw [Nat.succ_mul] at hMul
  have hLength : 2 * w + c.size * width ≤ (encodeMergeWitness r.cap c).length := by
    rw [← length_encodeCircuit r.cap c]
    simp only [encodeMergeWitness, List.length_append]
    exact Nat.le_add_right ..
  rw [length_packedPair, length_packedPair]
  change 4 * ((encodeMergeRequest r).length + 1 + w + i * width + (width - 1)) + 3 < _
  omega

private theorem candidateGateFinalBit_add_steps (requestLength w count i : Nat) (hi : i < count) :
    candidateGateFinalBit requestLength w (count - 1) =
      candidateGateFinalBit requestLength w i + 4 * (3 + 2 * w) * (count - (i + 1)) := by
  let width := 3 + 2 * w
  let steps := count - (i + 1)
  have hIndex : count - 1 = i + steps := by unfold steps; omega
  have hMul : (count - 1) * width = i * width + steps * width := by
    rw [hIndex, Nat.add_mul]
  have hStride : 4 * width * steps = 4 * (steps * width) := by ac_rfl
  change 4 * (requestLength + 1 + w + (count - 1) * width + (width - 1)) + 3 =
    4 * (requestLength + 1 + w + i * width + (width - 1)) + 3 + 4 * width * steps
  rw [hMul, hStride]
  omega

/-- The candidate scan visits records from the end, at one record stride per step. -/
theorem candidateGateReversePosition_eq (r : MergeRequest) (c : BooleanCircuit r.arity)
    (cert : BinaryWord) (i : Nat) (hi : i < c.size) :
    let request := encodeMergeRequest r
    let code := encodeMergeWitness r.cap c
    let w := circuitFieldWidth r.arity r.cap
    let length := (packedPair (packedPair request code) cert).length
    length - 1 - candidateGateFinalBit request.length w i =
      length - 1 - candidateGateFinalBit request.length w (c.size - 1) +
        4 * (3 + 2 * w) * (c.size - (i + 1)) := by
  dsimp only
  have hLast := candidateGateFinalBit_lt r c cert (c.size - 1) (by omega)
  have hShift := candidateGateFinalBit_add_steps (encodeMergeRequest r).length
    (circuitFieldWidth r.arity r.cap) c.size i hi
  dsimp only at hLast
  rw [hShift] at hLast ⊢
  omega

/-- The scratch lanes which must start at zero for a prepared candidate scan. -/
@[expose] def gateBlockScratchLanes : List GateRecordLane :=
  [.remaining, .gate .left, .gate .right, .gate .opcode, .gate .address, .gate .lookupWork,
    .gate .multiplier, .gate .scratch, .gate .zero]

/-- Explicit initial register values suffice to run the candidate block in place. -/
theorem packedCandidateGateBlockReady {R : Type} (r : MergeRequest) (c : BooleanCircuit r.arity)
    (x : Fin r.arity → Bool) (oldTrace newTrace : BinaryWord) (oldValue newValue : Bool)
    (lanes : GateRecordLane → R) (counter : R) (values : R → Nat)
    (hTrace : newTrace.length = r.arity + c.size)
    (hCount : values counter = c.size)
    (hDest : values (lanes (.gate .destination)) = r.arity + c.size - 1)
    (hZero : ∀ lane ∈ gateBlockScratchLanes, values (lanes lane) = 0) :
    let request := encodeMergeRequest r
    let query := packedPair request (encodeMergeWitness r.cap c)
    let cert := encodeMergeTraceCertificate x oldTrace newTrace oldValue newValue
    let word := packedPair query cert
    let w := circuitFieldWidth r.arity r.cap
    values (lanes .width) = w →
    values (lanes .position) =
      word.length - 1 - candidateGateFinalBit request.length w (c.size - 1) →
    values (lanes (.gate .inputLength)) = word.length →
    values (lanes (.gate .traceStart)) = mergeNewTraceStart query r.arity oldTrace.length →
    GateBlockReady lanes counter word newTrace r.arity
      (c.network.traceInstructions.map fun op ↦ GateRecordBits.encode w op.fields) values := by
  let request := encodeMergeRequest r
  let query := packedPair request (encodeMergeWitness r.cap c)
  let cert := encodeMergeTraceCertificate x oldTrace newTrace oldValue newValue
  let word := packedPair query cert
  let w := circuitFieldWidth r.arity r.cap
  let records := c.network.traceInstructions.map fun op ↦ GateRecordBits.encode w op.fields
  change values (lanes .width) = w →
    values (lanes .position) =
      word.length - 1 - candidateGateFinalBit request.length w (c.size - 1) →
    values (lanes (.gate .inputLength)) = word.length →
    values (lanes (.gate .traceStart)) = mergeNewTraceStart query r.arity oldTrace.length →
    GateBlockReady lanes counter word newTrace r.arity records values
  intro hWidth hPosition hInputLength hTraceStart
  have hRecordCount : records.length = c.size := by
    simp only [records, List.length_map, Network.length_traceInstructions, BooleanCircuit.size]
  have hRecordAt (i : Fin records.length) :
      records[i] = GateRecordBits.encode w (c.network.traceInstructions[i.val]'(by
        simpa only [records, List.length_map] using i.isLt)).fields := by
    change records[i.val]'i.isLt = _
    dsimp only [records]
    rw [List.getElem_map]
  have hCertLength : cert.length = r.arity + 1 + oldTrace.length + newTrace.length + 2 := by
    simp only [cert, encodeMergeTraceCertificate, List.length_append, length_mergeRowField,
      List.length_cons, List.length_nil]
  have hWordLength : word.length = 2 * (query.length + cert.length + 1) := length_packedPair ..
  have hTraceLe : newTrace.length ≤ word.length := by omega
  have hStartLe : mergeNewTraceStart query r.arity oldTrace.length ≤ word.length := by
    unfold mergeNewTraceStart mergeOldTraceStart
    omega
  have hOperandLe : 2 * (r.arity + r.cap + 1) ≤ word.length := by
    have hQuery := length_packedPair request (encodeMergeWitness r.cap c)
    have hRequest := arity_add_cap_le_length_encodeMergeRequest r
    change query.length = _ at hQuery
    change r.arity + r.cap ≤ request.length at hRequest
    omega
  refine ⟨hCount.trans hRecordCount.symm, ?_, ?_, hTraceLe, ?_, ?_, ?_⟩
  · rwa [hRecordCount]
  · rwa [hRecordCount]
  · intro hNonempty
    have hPositive : 0 < c.size := hRecordCount ▸ List.length_pos_iff.mpr hNonempty
    refine ⟨⟨hInputLength, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · exact hTraceStart ▸ hStartLe
    · change values (lanes (.gate .destination)) ≤ word.length
      omega
    · exact Nat.le_trans (Nat.le_of_eq (hZero (.gate .left) (by simp [gateBlockScratchLanes])))
        (Nat.zero_le _)
    · exact Nat.le_trans (Nat.le_of_eq (hZero (.gate .right) (by simp [gateBlockScratchLanes])))
        (Nat.zero_le _)
    · change values (lanes (.gate .destination)) < newTrace.length
      omega
    · intro i hi
      change word[values (lanes (.gate .traceStart)) + 2 * i]? = newTrace[i]?
      rw [hTraceStart]
      exact getElem?_packedMergeTrace_new query x oldTrace newTrace oldValue newValue hi
    · exact hZero (.gate .address) (by simp [gateBlockScratchLanes])
    · exact hZero (.gate .lookupWork) (by simp [gateBlockScratchLanes])
    · exact hZero (.gate .multiplier) (by simp [gateBlockScratchLanes])
    · exact hZero (.gate .scratch) (by simp [gateBlockScratchLanes])
    · exact hZero (.gate .zero) (by simp [gateBlockScratchLanes])
    · exact hZero .remaining (by simp [gateBlockScratchLanes])
    · exact hZero (.gate .left) (by simp [gateBlockScratchLanes])
    · exact hZero (.gate .right) (by simp [gateBlockScratchLanes])
    · exact hZero (.gate .opcode) (by simp [gateBlockScratchLanes])
  · intro i
    have hi : i.val < c.size := hRecordCount ▸ i.isLt
    have hSteps : records.length - (i.val + 1) = c.size - (i.val + 1) :=
      congrArg (· - (i.val + 1)) hRecordCount
    have hAddr : word.length - 1 - candidateGateFinalBit request.length w i.val =
        word.length - 1 - candidateGateFinalBit request.length w (c.size - 1) +
          4 * (3 + 2 * w) * (c.size - (i.val + 1)) :=
      candidateGateReversePosition_eq r c cert i hi
    dsimp only
    rw [hWidth, hPosition, hSteps, ← hAddr, hRecordAt i]
    exact candidate_gateRecordLayout r c x oldTrace newTrace oldValue newValue i hi
  · intro i
    dsimp only
    rw [hRecordAt i]
    exact ⟨(fieldValue_le_circuitFieldWidth_cap r.arity r.cap _ (length_fieldBits ..)).trans
      hOperandLe, (fieldValue_le_circuitFieldWidth_cap r.arity r.cap _ (length_fieldBits ..)).trans
      hOperandLe⟩

end PvsNP.MCSP
