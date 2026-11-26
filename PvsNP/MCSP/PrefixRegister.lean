module

public import PvsNP.MCSP.PackedRequestLayout
public import PvsNP.TuringMachine.Registers.StridedCompare

/-! # Counted comparison of a packed request prefix with its candidate -/

public section

namespace PvsNP.MCSP

open Circuits RegisterMachine RegisterMachine.Fragment

private theorem getElem?_reverse_of_forward {word bits : BinaryWord} {start stride : Nat}
    (hReads : ∀ i, i < bits.length → word[start + stride * i]? = bits[i]?) :
    ∀ i, i < bits.length → word.reverse[word.length - 1 - start - stride * i]? = bits[i]? := by
  intro i hi
  have hForward := hReads i hi
  rw [List.getElem?_eq_getElem hi] at hForward
  have hIn := (List.getElem?_eq_some_iff.mp hForward).choose
  have hIndex : word.length - 1 - start - stride * i + (start + stride * i) + 1 =
      word.length := by omega
  rw [List.getElem?_reverse' hIndex]
  exact hReads i hi

variable {R : Type} [DecidableEq R]

/-- Compare exactly the two prefix windows. The candidate length is checked
before this fragment, so the requested prefix fits in both fields. -/
theorem runsValues_packedRequestPrefix (lanes : Fin 6 → R) (hLanes : Function.Injective lanes)
    {request : BinaryWord} {fields : MergeRequestFields}
    (hFields : readMergeRequestFields request = some fields) (candidate cert : BinaryWord)
    (hCandidate : fields.pref.length ≤ candidate.length) (before : R → Nat)
    (hLeft : before (lanes 0) = (packedPair (packedPair request candidate) cert).length - 1 -
      (4 * fields.prefStart + 3))
    (hRight : before (lanes 1) = (packedPair (packedPair request candidate) cert).length - 1 -
      (4 * (request.length + 1) + 3))
    (hWidth : before (lanes 2) = fields.pref.length)
    (hIndex : before (lanes 3) = 0) (hWork : before (lanes 4) = 0)
    (hOrder : before (lanes 5) = 0) :
    let word := packedPair (packedPair request candidate) cert
    ∃ ticks ≤ stridedCompareTime 4 4 word.length fields.pref.length, ∃ after : R → Nat,
      (stridedCompare 4 4 lanes).RunsValues word ticks before after ∧
      after (lanes 2) = 0 ∧
      (after (lanes 5) = 0 ↔ candidate.take fields.pref.length = fields.pref) ∧
      after (lanes 0) = before (lanes 0) - 4 * fields.pref.length ∧
      after (lanes 1) = before (lanes 1) - 4 * fields.pref.length ∧
      ∀ r, r ≠ lanes 0 → r ≠ lanes 1 → r ≠ lanes 2 → r ≠ lanes 5 → after r = before r := by
  let word := packedPair (packedPair request candidate) cert
  let pref := fields.pref
  let provided := candidate.take pref.length
  have hLength : provided.length = pref.length := List.length_take_of_le hCandidate
  have hLeftReads (i : Nat) (hi : i < pref.length) :
      word[4 * fields.prefStart + 3 + 4 * i]? = pref[i]? := by
    rw [show 4 * fields.prefStart + 3 + 4 * i = 4 * (fields.prefStart + i) + 3 by omega]
    exact getElem?_packedRequestPref hFields candidate cert hi
  have hRightReads (i : Nat) (hi : i < provided.length) :
      word[4 * (request.length + 1) + 3 + 4 * i]? = provided[i]? := by
    have hi' : i < pref.length := by simpa only [hLength] using hi
    rw [show 4 * (request.length + 1) + 3 + 4 * i =
      4 * (request.length + 1 + i) + 3 by omega,
      getElem?_packedPair_nested_candidate _ _ _ (hi'.trans_le hCandidate)]
    exact (List.getElem?_take_of_lt hi').symm
  obtain ⟨ticks, hTicks, after, hRun, hZero, hResult, hEndL, hEndR, hFrame⟩ :=
    runsValues_stridedCompare_of_reads 4 4 lanes hLanes word pref provided before
      (by decide) (by decide) hLength.symm hWidth hIndex hWork hOrder
      (by rw [hLeft]; exact getElem?_reverse_of_forward hLeftReads)
      (by rw [hRight]; exact getElem?_reverse_of_forward hRightReads)
  refine ⟨ticks, hTicks, after, hRun, hZero, ?_, hEndL, hEndR, hFrame⟩
  change after (lanes 5) = 0 ↔ provided = pref
  rw [hResult, ← fieldValue_eq_iff_of_length hLength]
  by_cases hLT : fieldValue pref < fieldValue provided
  · simp only [ite_eq_left hLT, Nat.one_ne_zero, false_iff]
    omega
  by_cases hGT : fieldValue provided < fieldValue pref
  · rw [ite_eq_right hLT, ite_eq_left hGT]
    omega
  · simp only [ite_eq_right hLT, ite_eq_right hGT, true_iff]
    omega

end PvsNP.MCSP
