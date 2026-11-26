module

public import PvsNP.Circuits.DescriptionValidation
public import PvsNP.MCSP.GateStructureRegister
public import PvsNP.MCSP.TraceLayout

/-! # Structural gate scans on raw padded description windows -/

public section

namespace PvsNP.MCSP

open Circuits RegisterMachine.Fragment

/-- Slice the three raw fields without validating their contents. -/
@[expose] def circuitDescriptionRecord (width : Nat) (code : BinaryWord) (i : Nat) :
    GateRecordBits :=
  let bits := (code.drop (width + i * (3 + 2 * width))).take (3 + 2 * width)
  let operands := bits.drop 3
  ⟨bits.take 3, operands.take width, (operands.drop width).take width⟩

/-- The record array uses the count declared in the raw header. -/
@[expose] def circuitDescriptionRecords (arity cap : Nat) (code : BinaryWord) :
    List GateRecordBits :=
  List.ofFn fun i : Fin (circuitDescriptionCount arity cap code) ↦
    circuitDescriptionRecord (circuitFieldWidth arity cap) code i.val

@[simp] theorem length_circuitDescriptionRecords (arity cap : Nat) (code : BinaryWord) :
    (circuitDescriptionRecords arity cap code).length = circuitDescriptionCount arity cap code :=
  List.length_ofFn

theorem gateStructureRecordPasses_circuitDescriptionRecord (arity width : Nat)
    (code : BinaryWord) (i : Nat) :
    gateStructureRecordPasses (arity + i) (circuitDescriptionRecord width code i) =
      (circuitDescriptionGateAt width arity code i).isSome := by
  rw [circuitDescriptionGateAt_eq_fields]
  rfl

theorem gateStructureFailureCount_circuitDescriptionRecords_eq_zero_iff (arity cap : Nat)
    (code : BinaryWord) :
    gateStructureFailureCount arity (circuitDescriptionRecords arity cap code) = 0 ↔
      ∀ i, i < circuitDescriptionCount arity cap code →
        (circuitDescriptionGateAt (circuitFieldWidth arity cap) arity code i).isSome := by
  rw [gateStructureFailureCount_eq_zero_iff]
  constructor
  · intro h i hi
    have hIndex : i < (circuitDescriptionRecords arity cap code).length := by
      rwa [length_circuitDescriptionRecords]
    simpa only [circuitDescriptionRecords, List.getElem_ofFn,
      gateStructureRecordPasses_circuitDescriptionRecord] using h i hIndex
  · intro h i hi
    have hIndex : i < circuitDescriptionCount arity cap code := by
      simpa only [length_circuitDescriptionRecords] using hi
    simpa only [circuitDescriptionRecords, List.getElem_ofFn,
      gateStructureRecordPasses_circuitDescriptionRecord] using h i hIndex

/-- Reverse address of a record's rightmost bit in a stride-four embedding. -/
@[expose] def descriptionGateReversePosition (wordLength base width i : Nat) : Nat :=
  reverseGateRecordPosition wordLength (base + 4 * (width + i * (3 + 2 * width))) width

private theorem descriptionGateRecord_fits {code : BinaryWord} {width cap i : Nat}
    (hLength : code.length = circuitDescriptionLength width cap) (hi : i < cap) :
    width + i * (3 + 2 * width) + (3 + 2 * width) ≤ code.length := by
  have hRecords := Nat.mul_le_mul_right (3 + 2 * width) (Nat.succ_le_of_lt hi)
  rw [Nat.succ_mul] at hRecords
  rw [hLength, circuitDescriptionLength]
  omega

/-- Every claimed record fits and can be read at the expected reverse position. -/
theorem packedDescriptionGateRecordLayout (word code : BinaryWord) (base width cap i : Nat)
    (hLength : code.length = circuitDescriptionLength width cap) (hi : i < cap)
    (hReads : ∀ j, j < code.length → word[base + 4 * j]? = code[j]?) :
    let record := circuitDescriptionRecord width code i
    GateRecordLayout word (descriptionGateReversePosition word.length base width i) width
      record.tag record.left record.right := by
  let offset := width + i * (3 + 2 * width)
  let recordWidth := 3 + 2 * width
  let bits := (code.drop offset).take recordWidth
  let record := circuitDescriptionRecord width code i
  have hFits : offset + recordWidth ≤ code.length := descriptionGateRecord_fits hLength hi
  have hBits : bits.length = recordWidth := by
    apply List.length_take_of_le
    rw [List.length_drop]
    omega
  have hTag : record.tag.length = 3 := by
    change (bits.take 3).length = 3
    apply List.length_take_of_le
    rw [hBits]
    unfold recordWidth
    omega
  have hLeft : record.left.length = width := by
    change ((bits.drop 3).take width).length = width
    apply List.length_take_of_le
    rw [List.length_drop, hBits]
    unfold recordWidth
    omega
  have hRemainder : ((bits.drop 3).drop width).length = width := by
    rw [List.length_drop, List.length_drop, hBits]
    unfold recordWidth
    omega
  have hRight : record.right.length = width := by
    change (((bits.drop 3).drop width).take width).length = width
    exact List.length_take_of_le hRemainder.ge
  have hFields : record.tag ++ record.left ++ record.right = bits := by
    change bits.take 3 ++ (bits.drop 3).take width ++ ((bits.drop 3).drop width).take width = bits
    rw [List.take_of_length_le hRemainder.le, List.append_assoc, List.take_append_drop,
      List.take_append_drop]
  change GateRecordLayout word (reverseGateRecordPosition word.length (base + 4 * offset) width)
    width record.tag record.left record.right
  apply gateRecordLayout_of_forwardReads hTag hLeft hRight
  intro j hj
  rw [hFields, hBits] at hj
  rw [hFields]
  change word[base + 4 * offset + 4 * j]? = ((code.drop offset).take recordWidth)[j]?
  rw [List.getElem?_take_of_lt hj, List.getElem?_drop, show base + 4 * offset + 4 * j =
    base + 4 * (offset + j) by omega]
  exact hReads (offset + j) (by omega)

private theorem descriptionGateReversePosition_step (word code : BinaryWord)
    (base width count cap i : Nat) (hLength : code.length = circuitDescriptionLength width cap)
    (hCount : count ≤ cap) (hi : i < count)
    (hReads : ∀ j, j < code.length → word[base + 4 * j]? = code[j]?) :
    descriptionGateReversePosition word.length base width i =
      descriptionGateReversePosition word.length base width (count - 1) +
        4 * (3 + 2 * width) * (count - (i + 1)) := by
  let stride := 3 + 2 * width
  let suffix := count - (i + 1)
  have hIndex : count - 1 = i + suffix := by unfold suffix; omega
  have hMul : (count - 1) * stride = i * stride + suffix * stride := by
    rw [hIndex, Nat.add_mul]
  have hStride : 4 * stride * suffix = 4 * (suffix * stride) := by ac_rfl
  have hFits : width + (count - 1) * stride + stride ≤ code.length :=
    descriptionGateRecord_fits hLength (by omega)
  let last := width + (count - 1) * stride + (stride - 1)
  have hLast : last < code.length := by
    have hPos : 0 < stride := by unfold stride; omega
    unfold last
    omega
  have hRead := hReads last hLast
  rw [List.getElem?_eq_getElem hLast] at hRead
  have hAddress := (List.getElem?_eq_some_iff.mp hRead).choose
  change word.length - 1 - (base + 4 * (width + i * stride) + 4 * (stride - 1)) =
    word.length - 1 - (base + 4 * (width + (count - 1) * stride) + 4 * (stride - 1)) +
      4 * stride * suffix
  unfold last at hAddress
  rw [hMul] at hAddress
  rw [hMul, hStride]
  omega

/-- Prepare a block scan from any raw padded description window. -/
theorem packedStructureBlockReady {R : Type} (arity cap base : Nat) (word code : BinaryWord)
    (lanes : GateRecordLane → R) (counter : R) (v : R → Nat)
    (hLength : code.length = circuitDescriptionLength (circuitFieldWidth arity cap) cap)
    (hCount : circuitDescriptionCount arity cap code ≤ cap)
    (hWord : 2 * (arity + cap + 1) ≤ word.length)
    (hReads : ∀ j, j < code.length → word[base + 4 * j]? = code[j]?) :
    let width := circuitFieldWidth arity cap
    let count := circuitDescriptionCount arity cap code
    v counter = count → v (lanes .width) = width →
    v (lanes (.gate .destination)) = arity + count - 1 →
    v (lanes .position) = descriptionGateReversePosition word.length base width (count - 1) →
    (∀ lane ∈ gateStructureScratchLanes, v (lanes lane) = 0) →
    GateStructureBlockReady lanes counter word arity
      (circuitDescriptionRecords arity cap code) v := by
  dsimp only
  intro hCounter hWidth hDest hPosition hZeroes
  let width := circuitFieldWidth arity cap
  let count := circuitDescriptionCount arity cap code
  let records := circuitDescriptionRecords arity cap code
  have hRecords : records.length = count := length_circuitDescriptionRecords arity cap code
  have hRecord (i : Fin records.length) :
      records[i] = circuitDescriptionRecord width code i.val := by
    change records[i.val]'i.isLt = _
    simp only [records, circuitDescriptionRecords, List.getElem_ofFn, width]
  have hLayout (i : Fin records.length) :
      let record := records[i]
      GateRecordLayout word (descriptionGateReversePosition word.length base width i.val) width
        record.tag record.left record.right := by
    dsimp only
    rw [hRecord i]
    have hi : i.val < count := hRecords ▸ i.isLt
    exact packedDescriptionGateRecordLayout word code base width cap i hLength
      (hi.trans_le hCount) hReads
  refine ⟨hCounter.trans hRecords.symm, hRecords ▸ hDest, ?_, hZeroes, ?_, ?_⟩
  · have hSize : count ≤ cap := hCount
    change arity + records.length ≤ word.length
    omega
  · intro i
    have hi : i.val < count := hRecords ▸ i.isLt
    have hSteps : records.length - (i.val + 1) = count - (i.val + 1) :=
      congrArg (· - (i.val + 1)) hRecords
    have hPos := descriptionGateReversePosition_step word code base width count cap i
      hLength hCount hi hReads
    dsimp only
    rw [hWidth, hPosition, hSteps, ← hPos]
    exact hLayout i
  · intro i
    have h := hLayout i
    exact ⟨(fieldValue_le_circuitFieldWidth_cap arity cap _ h.left_length).trans hWord,
      (fieldValue_le_circuitFieldWidth_cap arity cap _ h.right_length).trans hWord⟩

/-- Scan the prepared description and return zero failures exactly when every
claimed gate parses. The lanes and counter must be distinct, and the failure
register must start at zero. `packedStructureBlockReady` supplies the layout
hypotheses from the padded length, count bound, and raw reads. -/
theorem runsValues_checkPackedStructureBlock {R : Type} [DecidableEq R]
    (arity cap : Nat) (code : BinaryWord) {lanes : GateRecordLane → R}
    (hLanes : Function.Injective lanes) {counter : R} (hCounter : ∀ lane, lanes lane ≠ counter)
    {word : BinaryWord} {v : R → Nat} (hInitial : v (lanes (.gate .failures)) = 0)
    (ready : GateStructureBlockReady lanes counter word arity
      (circuitDescriptionRecords arity cap code) v) :
    let count := circuitDescriptionCount arity cap code
    ∃ ticks ≤ gateBlockCost word.length (v (lanes .width)) count,
      ∃ after, (checkGateStructureBlock lanes counter).RunsValues word ticks v after ∧
        after counter = 0 ∧
        after (lanes .position) = v (lanes .position) + 4 * (3 + 2 * v (lanes .width)) * count ∧
        after (lanes (.gate .destination)) = arity - 1 ∧
        (after (lanes (.gate .failures)) = 0 ↔
          ∀ i, i < count →
            (circuitDescriptionGateAt (circuitFieldWidth arity cap) arity code i).isSome) ∧
        ∀ reg, reg ≠ counter → reg ≠ lanes .position → reg ≠ lanes (.gate .destination) →
          reg ≠ lanes (.gate .failures) → after reg = v reg := by
  obtain ⟨ticks, hTicks, after, hRun, hZero, hPosition, hDest, hFailures, hFrame⟩ :=
    runsValues_checkGateStructureBlock hLanes hCounter ready
  rw [length_circuitDescriptionRecords] at hTicks hPosition
  refine ⟨ticks, hTicks, after, hRun, hZero, hPosition, hDest, ?_, hFrame⟩
  rw [hFailures, hInitial, Nat.zero_add,
    gateStructureFailureCount_circuitDescriptionRecords_eq_zero_iff]

end PvsNP.MCSP
