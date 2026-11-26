module

public import PvsNP.MCSP.PackedRequestLayout
public import PvsNP.TuringMachine.Registers.StridedZeroWindow

import Init.Data.List.Count

/-! # Check a row counter without decoding it into unary -/

public section

namespace PvsNP.MCSP

open RegisterMachine RegisterMachine.Fragment

/-- The reverse position, lower width, output counters and lookup workspace. -/
inductive SeenFieldLane where
  | position | width | high | lowerOnes | lookupIndex | scratch
  deriving DecidableEq

private def seenLowLanes : Fin 5 → SeenFieldLane
  | 0 => .position
  | 1 => .width
  | 2 => .lowerOnes
  | 3 => .lookupIndex
  | _ => .scratch

private theorem seenLowLanes_injective : Function.Injective seenLowLanes := by decide

variable {R : Type}

private def readSeenHigh (lanes : SeenFieldLane → R) : Fragment R :=
  readRegisterBitAdvance 4 (lanes .position) (lanes .lookupIndex) (lanes .scratch) fun bit ↦
    incrementBy (lanes .high) (bit.getD false).toNat

/-- Read the high bit, then count the true lower bits at stride four. -/
def seenFieldRegister (lanes : SeenFieldLane → R) : Fragment R :=
  (readSeenHigh lanes).seq (stridedZeroWindow 4 (lanes ∘ seenLowLanes))

@[expose] def seenFieldRegisterCost (inputLength arity : Nat) : Nat :=
  7 * inputLength + 10 + stridedZeroWindowCost 4 inputLength arity

theorem seenFieldRegisterCost_polynomiallyBounded {inputLength arity : Nat → Nat}
    (hInput : PolynomiallyBounded inputLength) (hArity : PolynomiallyBounded arity) :
    PolynomiallyBounded (fun n ↦ seenFieldRegisterCost (inputLength n) (arity n)) :=
  ((((PolynomiallyBounded.const 7).mul hInput).add (PolynomiallyBounded.const 10)).add
    (stridedZeroWindowCost_polynomiallyBounded 4 hInput hArity))

/-- The output counters decide the range test and preserve neighboring registers. -/
structure SeenFieldRegisterResult (lanes : SeenFieldLane → R) (low : BinaryWord) (high : Bool)
    (before after : R → Nat) : Prop where
  highBit : after (lanes .high) = high.toNat
  lowerOnes : after (lanes .lowerOnes) = low.count true
  position : after (lanes .position) = before (lanes .position) + 4 * (low.length + 1)
  widthZero : after (lanes .width) = 0
  inRange : (after (lanes .high) = 0 ∨ after (lanes .lowerOnes) = 0) ↔
    mergeSeenFieldInRange (low ++ [high]) = true
  frame : ∀ r, r ≠ lanes .position → r ≠ lanes .width → r ≠ lanes .high →
    r ≠ lanes .lowerOnes → after r = before r

private theorem countTrue_eq_zero_iff_all_not (bits : BinaryWord) :
    bits.count true = 0 ↔ bits.all (!·) = true := by
  induction bits with
  | nil => simp
  | cons bit bits ih => cases bit <;> simp [ih]

variable [DecidableEq R]

/-- Scan a prepared little-endian counter whose reverse reads begin at its high bit. -/
theorem runsValues_seenFieldRegister (lanes : SeenFieldLane → R)
    (hLanes : Function.Injective lanes) (x low : BinaryWord) (high : Bool) (before : R → Nat)
    (hWidth : before (lanes .width) = low.length) (hHighZero : before (lanes .high) = 0)
    (hCountZero : before (lanes .lowerOnes) = 0) (hIndex : before (lanes .lookupIndex) = 0)
    (hScratch : before (lanes .scratch) = 0)
    (hRead : ∀ i, i < (low ++ [high]).length →
      x.reverse[before (lanes .position) + 4 * i]? = (low ++ [high]).reverse[i]?) :
    ∃ ticks ≤ seenFieldRegisterCost x.length low.length, ∃ after : R → Nat,
      (seenFieldRegister lanes).RunsValues x ticks before after ∧
      SeenFieldRegisterResult lanes low high before after := by
  have hNe {a b : SeenFieldLane} (h : a ≠ b) : lanes a ≠ lanes b := fun e ↦ h (hLanes e)
  have hThis : x.reverse[before (lanes .position)]? = some high := by
    simpa only [Nat.mul_zero, Nat.add_zero, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.getElem?_cons_zero] using hRead 0 (by simp)
  let marked := setValue (lanes .high) high.toNat before
  let sampled := setValue (lanes .position) (before (lanes .position) + 4) marked
  let highTicks := 5 * before (lanes .position) + 2 +
    (inputAtCost (before (lanes .position)) x.length + high.toNat) + 4
  have hMarkedPosition : marked (lanes .position) = before (lanes .position) :=
    setValue_other (hNe (by decide)) ..
  have hHighRun : (readSeenHigh lanes).RunsValues x highTicks before sampled := by
    have hMark : (incrementBy (lanes .high) high.toNat).RunsValues x high.toNat before marked := by
      simpa only [hHighZero, Nat.zero_add, marked] using
        runsValues_incrementBy (lanes .high) high.toNat x before
    have hRun := runsValues_readRegisterBitAdvance 4 (lanes .position) (lanes .lookupIndex)
      (lanes .scratch) (fun bit ↦ incrementBy (lanes .high) (bit.getD false).toNat) x before
      (hNe (by decide)) (hNe (by decide)) (hNe (by decide)) hIndex hScratch
      (by simpa only [hThis, Option.getD_some] using hMark)
    simpa only [readSeenHigh, sampled, highTicks, hMarkedPosition] using hRun
  have hHighBound : highTicks ≤ 7 * x.length + 10 := by
    have hIn := (List.getElem?_eq_some_iff.mp hThis).choose
    simp only [List.length_reverse] at hIn
    have hc := inputAtCost_le (before (lanes .position)) x.length
    have hb := Bool.toNat_le high
    dsimp only [highTicks]
    omega
  have hSampledPosition : sampled (lanes .position) = before (lanes .position) + 4 :=
    setValue_same ..
  have hSampledHigh : sampled (lanes .high) = high.toNat :=
    (setValue_other (hNe (by decide)) ..).trans (setValue_same ..)
  have hSampledFrame {r : R} (hp : r ≠ lanes .position) (hh : r ≠ lanes .high) :
      sampled r = before r := (setValue_other hp ..).trans (setValue_other hh ..)
  have hSampledWidth : sampled (lanes .width) = low.length :=
    (hSampledFrame (r := lanes .width) (hNe (by decide)) (hNe (by decide))).trans hWidth
  have hSampledIndex : sampled (lanes .lookupIndex) = 0 :=
    (hSampledFrame (r := lanes .lookupIndex) (hNe (by decide)) (hNe (by decide))).trans hIndex
  have hSampledScratch : sampled (lanes .scratch) = 0 :=
    (hSampledFrame (r := lanes .scratch) (hNe (by decide)) (hNe (by decide))).trans hScratch
  let lowerLanes := lanes ∘ seenLowLanes
  have hReadLow (i : Nat) (hi : i < low.reverse.length) :
      x.reverse[sampled (lowerLanes 0) + 4 * i]? = low.reverse[i]? := by
    have hOffset : i + 1 < (low ++ [high]).length := by
      simp only [List.length_reverse] at hi
      simp only [List.length_append, List.length_singleton]
      omega
    change x.reverse[sampled (lanes .position) + 4 * i]? = _
    rw [hSampledPosition, show before (lanes .position) + 4 + 4 * i =
      before (lanes .position) + 4 * (i + 1) by omega]
    simpa only [List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.getElem?_cons_succ] using hRead (i + 1) hOffset
  obtain ⟨lowTicks, hLowCost, after, hLowRun, hZero, hPos, hOnes, hLowFrame⟩ :=
    runsValues_stridedZeroWindow_of_reads 4 lowerLanes (hLanes.comp seenLowLanes_injective)
      x low.reverse sampled
      (by rw [List.length_reverse]; exact hSampledWidth) hSampledIndex hSampledScratch hReadLow
  have hAfterHigh : after (lanes .high) = high.toNat :=
    (hLowFrame (lanes .high) (hNe (by decide)) (hNe (by decide)) (hNe (by decide))).trans
      hSampledHigh
  have hAfterCount : after (lanes .lowerOnes) = low.count true := by
    change after (lanes .lowerOnes) = sampled (lanes .lowerOnes) + low.reverse.count true at hOnes
    rw [hOnes, hSampledFrame (r := lanes .lowerOnes) (hNe (by decide)) (hNe (by decide)),
      hCountZero, Nat.zero_add, List.count_reverse]
  refine ⟨highTicks + lowTicks, ?_, after, hHighRun.seq hLowRun, ?_⟩
  · simp only [List.length_reverse] at hLowCost
    exact Nat.add_le_add hHighBound hLowCost
  · refine ⟨hAfterHigh, hAfterCount, ?_, hZero, ?_, ?_⟩
    · change after (lanes .position) = sampled (lanes .position) + 4 * low.reverse.length at hPos
      rw [hPos, hSampledPosition, List.length_reverse]
      omega
    · rw [hAfterHigh, hAfterCount, countTrue_eq_zero_iff_all_not, mergeSeenFieldInRange_append]
      cases high <;> simp
    · intro r hp hw hh hl
      exact (hLowFrame r hp hw hl).trans (hSampledFrame hp hh)

/-- Instantiate the scan at the counter's physical offset in a nested packed request. -/
theorem runsValues_seenFieldRegister_packed (lanes : SeenFieldLane → R)
    (hLanes : Function.Injective lanes) {request : BinaryWord} {fields : MergeRequestFields}
    (hFields : readMergeRequestFields request = some fields) (candidate cert : BinaryWord)
    (before : R → Nat)
    (hPos : before (lanes .position) = reverseWindowStart
      (packedPair (packedPair request candidate) cert).length (4 * fields.counterStart + 3)
      4 fields.counter.length)
    (hWidth : before (lanes .width) = fields.arity) (hHighZero : before (lanes .high) = 0)
    (hCountZero : before (lanes .lowerOnes) = 0) (hIndex : before (lanes .lookupIndex) = 0)
    (hScratch : before (lanes .scratch) = 0) :
    let word := packedPair (packedPair request candidate) cert
    ∃ ticks ≤ seenFieldRegisterCost word.length fields.arity, ∃ after : R → Nat,
      (seenFieldRegister lanes).RunsValues word ticks before after ∧
      SeenFieldRegisterResult lanes fields.counter.dropLast (fields.counter.getLastD false)
        before after ∧
      ((after (lanes .high) = 0 ∨ after (lanes .lowerOnes) = 0) ↔
        mergeSeenFieldInRange fields.counter = true) := by
  let word := packedPair (packedPair request candidate) cert
  have hCounter := (readMergeRequestFields_eq_some_iff.mp hFields).1.counter
  have hNonempty : fields.counter ≠ [] := by rintro he; simp [he] at hCounter
  have hSplit : fields.counter.dropLast ++ [fields.counter.getLastD false] = fields.counter := by
    simpa only [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hNonempty,
      Option.getD_some] using List.dropLast_concat_getLast hNonempty
  have hLower : fields.counter.dropLast.length = fields.arity := by
    rw [List.length_dropLast, hCounter]
    omega
  have hRead (i : Nat) (hi : i < fields.counter.length) :
      word[(4 * fields.counterStart + 3) + 4 * i]? = fields.counter[i]? := by
    rw [show (4 * fields.counterStart + 3) + 4 * i = 4 * (fields.counterStart + i) + 3 by omega]
    exact getElem?_packedRequestCounter hFields candidate cert hi
  have hReverse (i : Nat) (hi : i < fields.counter.length) :
      word.reverse[before (lanes .position) + 4 * i]? = fields.counter.reverse[i]? := by
    rw [hPos]
    exact reverseWindowReads_of_forward hRead i hi
  obtain ⟨ticks, hTicks, after, hRun, hResult⟩ := runsValues_seenFieldRegister lanes hLanes word
    fields.counter.dropLast (fields.counter.getLastD false) before (hWidth.trans hLower.symm)
    hHighZero hCountZero hIndex hScratch (by simpa only [hSplit] using hReverse)
  rw [hLower] at hTicks
  refine ⟨ticks, hTicks, after, hRun, hResult, ?_⟩
  simpa only [hSplit] using hResult.inRange

end PvsNP.MCSP
