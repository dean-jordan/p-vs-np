module

public import PvsNP.MCSP.PackedRequestLayout
public import PvsNP.MCSP.DescriptionValidation
public import PvsNP.TuringMachine.Registers.StridedZeroWindow

/-! # Read the count, output wire, and padding of a packed description -/

public section

namespace PvsNP.MCSP

open Circuits RegisterMachine RegisterMachine.Fragment

/-- A raw description embedded at stride four, with length checks already made. -/
structure PaddedDescriptionWindow (word code : BinaryWord) (start arity cap : Nat) : Prop where
  length : code.length = mergeWitnessLength arity cap
  capacity : 2 * (arity + cap + 1) ≤ word.length
  read : ∀ i, i < code.length → word[start + 4 * i]? = code[i]?

private theorem packedRequestLength_ge {request : BinaryWord} {fields : MergeRequestFields}
    (hFields : readMergeRequestFields request = some fields) (candidate cert : BinaryWord) :
    2 * (fields.arity + max 1 fields.cap + 1) ≤
      (packedPair (packedPair request candidate) cert).length := by
  have hWord := (readMergeRequestFields_eq_some_iff.mp hFields).2
  have hBound : fields.arity + fields.cap + 2 ≤ request.length := by
    rw [hWord, MergeRequestFields.word]
    simp only [unaryField, List.length_append, List.length_replicate, List.length_cons,
      List.length_nil]
    omega
  have hCap : max 1 fields.cap ≤ fields.cap + 1 := Nat.max_le.mpr ⟨by omega, by omega⟩
  rw [length_packedPair, length_packedPair]
  omega

/-- The old description in a structurally split request has a full padded window. -/
theorem paddedDescriptionWindow_old {request : BinaryWord} {fields : MergeRequestFields}
    (hFields : readMergeRequestFields request = some fields) (candidate cert : BinaryWord) :
    PaddedDescriptionWindow (packedPair (packedPair request candidate) cert) fields.oldCode
      (4 * fields.oldStart + 3) fields.arity (max 1 fields.cap) := by
  refine ⟨(readMergeRequestFields_eq_some_iff.mp hFields).1.oldCode,
    packedRequestLength_ge hFields candidate cert, ?_⟩
  intro i hi
  rw [show 4 * fields.oldStart + 3 + 4 * i = 4 * (fields.oldStart + i) + 3 by omega]
  exact getElem?_packedRequestOld hFields candidate cert hi

/-- A candidate of the checked length has the analogous stride-four window. -/
theorem paddedDescriptionWindow_candidate {request : BinaryWord} {fields : MergeRequestFields}
    (hFields : readMergeRequestFields request = some fields) (candidate cert : BinaryWord)
    (hLength : candidate.length = mergeWitnessLength fields.arity fields.cap) :
    PaddedDescriptionWindow (packedPair (packedPair request candidate) cert) candidate
      (4 * (request.length + 1) + 3) fields.arity fields.cap := by
  have hCap := Nat.le_max_right 1 fields.cap
  have hCapacity := packedRequestLength_ge hFields candidate cert
  refine ⟨hLength, by omega, ?_⟩
  intro i hi
  rw [show 4 * (request.length + 1) + 3 + 4 * i =
    4 * (request.length + 1 + i) + 3 by omega]
  exact getElem?_packedPair_nested_candidate request candidate cert hi

private theorem PaddedDescriptionWindow.read_suffix {word code : BinaryWord}
    {start arity cap : Nat} (hWindow : PaddedDescriptionWindow word code start arity cap)
    (offset i : Nat) (hi : i < (code.drop offset).length) :
    word[start + 4 * offset + 4 * i]? = (code.drop offset)[i]? := by
  have hIn : offset + i < code.length := by rw [List.length_drop] at hi; omega
  rw [show start + 4 * offset + 4 * i = start + 4 * (offset + i) by omega,
    hWindow.read _ hIn, List.getElem?_drop]

variable {R : Type} [DecidableEq R]

/-- Read either the count field or the output field at its prepared offset.
Every bit pattern is allowed. The logarithmic width bounds its unary value. -/
theorem runsValues_paddedDescriptionField (lanes : Fin 5 → R) (hLanes : Function.Injective lanes)
    {word code : BinaryWord} {start arity cap : Nat}
    (hWindow : PaddedDescriptionWindow word code start arity cap) (offset : Nat)
    (hFits : offset + circuitFieldWidth arity cap ≤ code.length) (before : R → Nat)
    (hPos : before (lanes 0) = reverseWindowStart word.length (start + 4 * offset) 4
      (circuitFieldWidth arity cap))
    (hWidth : before (lanes 1) = circuitFieldWidth arity cap)
    (hValue : before (lanes 2) = 0) (hIndex : before (lanes 3) = 0)
    (hScratch : before (lanes 4) = 0) :
    ∃ ticks ≤ stridedFieldCost 4 word.length (circuitFieldWidth arity cap) word.length,
      ∃ after : R → Nat,
        (stridedField 4 lanes).RunsValues word ticks before after ∧
        after (lanes 1) = 0 ∧
        after (lanes 0) = before (lanes 0) + 4 * circuitFieldWidth arity cap ∧
        after (lanes 2) = fieldValue ((code.drop offset).take (circuitFieldWidth arity cap)) ∧
        ∀ r, r ≠ lanes 0 → r ≠ lanes 1 → r ≠ lanes 2 → after r = before r := by
  let width := circuitFieldWidth arity cap
  let bits := (code.drop offset).take width
  have hAvail : width ≤ (code.drop offset).length := by
    rw [List.length_drop]
    change offset + width ≤ code.length at hFits
    omega
  have hLen : bits.length = width := List.length_take_of_le hAvail
  have hForward (i : Nat) (hi : i < bits.length) :
      word[(start + 4 * offset) + 4 * i]? = bits[i]? := by
    have hi' : i < width := hLen ▸ hi
    exact (hWindow.read_suffix offset i (hi'.trans_le hAvail)).trans
      (List.getElem?_take_of_lt hi').symm
  have hRead (i : Nat) (hi : i < bits.length) :
      word.reverse[before (lanes 0) + 4 * i]? = bits.reverse[i]? := by
    rw [hPos, ← show bits.length = circuitFieldWidth arity cap from hLen]
    exact reverseWindowReads_of_forward hForward i hi
  have hCap := (fieldValue_le_circuitFieldWidth_cap arity cap bits hLen).trans hWindow.capacity
  simpa only [hLen, bits, width] using
    runsValues_stridedField_of_reads 4 lanes hLanes word bits word.length before
      (hWidth.trans hLen.symm) hValue hIndex hScratch hCap hRead

/-- Read the claimed gate count before testing its range. An out-of-range
count remains readable because only the fixed header is touched. -/
theorem runsValues_paddedDescriptionCount (lanes : Fin 5 → R) (hLanes : Function.Injective lanes)
    {word code : BinaryWord} {start arity cap : Nat}
    (hWindow : PaddedDescriptionWindow word code start arity cap) (before : R → Nat)
    (hPos : before (lanes 0) = reverseWindowStart word.length start 4
      (circuitFieldWidth arity cap))
    (hWidth : before (lanes 1) = circuitFieldWidth arity cap)
    (hValue : before (lanes 2) = 0) (hIndex : before (lanes 3) = 0)
    (hScratch : before (lanes 4) = 0) :
    ∃ ticks ≤ stridedFieldCost 4 word.length (circuitFieldWidth arity cap) word.length,
      ∃ after : R → Nat,
        (stridedField 4 lanes).RunsValues word ticks before after ∧
        after (lanes 1) = 0 ∧
        after (lanes 0) = before (lanes 0) + 4 * circuitFieldWidth arity cap ∧
        after (lanes 2) = circuitDescriptionCount arity cap code ∧
        ∀ r, r ≠ lanes 0 → r ≠ lanes 1 → r ≠ lanes 2 → after r = before r := by
  have hFits : 0 + circuitFieldWidth arity cap ≤ code.length := by
    rw [hWindow.length, mergeWitnessLength]
    omega
  simpa only [List.drop_zero, circuitDescriptionCount] using
    runsValues_paddedDescriptionField lanes hLanes hWindow 0 hFits before
      (by simpa only [Nat.mul_zero, Nat.add_zero] using hPos) hWidth hValue hIndex hScratch

/-- Count every nonzero bit after the code's output, with zero exactly when
the raw description has the canonical padding. -/
theorem runsValues_paddedDescriptionPadding (lanes : Fin 5 → R) (hLanes : Function.Injective lanes)
    {word code : BinaryWord} {start arity cap : Nat}
    (hWindow : PaddedDescriptionWindow word code start arity cap) (before : R → Nat)
    (hPos : before (lanes 0) = reverseWindowStart word.length
      (start + 4 * circuitDescriptionCodeLength arity cap code) 4
      (code.length - circuitDescriptionCodeLength arity cap code))
    (hWidth : before (lanes 1) = code.length - circuitDescriptionCodeLength arity cap code)
    (hCount : before (lanes 2) = 0) (hIndex : before (lanes 3) = 0)
    (hScratch : before (lanes 4) = 0) :
    let padding := code.drop (circuitDescriptionCodeLength arity cap code)
    ∃ ticks ≤ stridedZeroWindowCost 4 word.length padding.length, ∃ after : R → Nat,
      (stridedZeroWindow 4 lanes).RunsValues word ticks before after ∧
      after (lanes 1) = 0 ∧ after (lanes 0) = before (lanes 0) + 4 * padding.length ∧
      (after (lanes 2) = 0 ↔ padding.all (!·) = true) ∧
      ∀ r, r ≠ lanes 0 → r ≠ lanes 1 → r ≠ lanes 2 → after r = before r := by
  let offset := circuitDescriptionCodeLength arity cap code
  let padding := code.drop offset
  have hRead (i : Nat) (hi : i < padding.reverse.length) :
      word.reverse[before (lanes 0) + 4 * i]? = padding.reverse[i]? := by
    rw [List.length_reverse] at hi
    have hPos' : before (lanes 0) = reverseWindowStart word.length
        (start + 4 * offset) 4 padding.length := by
      simpa only [padding, List.length_drop] using hPos
    rw [hPos']
    exact reverseWindowReads_of_forward (hWindow.read_suffix offset) i hi
  obtain ⟨ticks, hTicks, after, hRun, hEnd, hEndPos, hTotal, hFrame⟩ :=
    runsValues_stridedZeroWindow_of_reads 4 lanes hLanes word padding.reverse before
      (by simpa only [List.length_reverse, padding, List.length_drop] using hWidth)
      hIndex hScratch hRead
  rw [List.length_reverse] at hTicks hEndPos
  rw [hCount, Nat.zero_add, List.count_reverse] at hTotal
  refine ⟨ticks, hTicks, after, hRun, hEnd, hEndPos, ?_, hFrame⟩
  rw [hTotal, List.count_eq_zero, List.all_eq_true]
  constructor
  · intro h b hb
    cases b
    · rfl
    · exact (h hb).elim
  · intro h hb
    have hc := h true hb
    contradiction

end PvsNP.MCSP
