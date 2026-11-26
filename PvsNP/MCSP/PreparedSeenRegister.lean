module

public import PvsNP.MCSP.SeenFieldRegister
public import PvsNP.TuringMachine.Registers.ReverseWindow

/-! # Check the packed counter using the measured forward address -/

public section

namespace PvsNP.MCSP

open RegisterMachine RegisterMachine.Fragment

/-- Workspace for the physical offset, the retained arity, and the two counters. -/
inductive PreparedSeenLane where
  | offset (lane : ReverseWindowLane)
  | arity | high | lowerOnes
  deriving DecidableEq

variable {R : Type}

private def preparedSeenScanLane : SeenFieldLane → PreparedSeenLane
  | .position => .offset .position
  | .width => .offset .width
  | .high => .high
  | .lowerOnes => .lowerOnes
  | .lookupIndex => .offset .multiplier
  | .scratch => .offset .scratch

private theorem preparedSeenScanLane_injective : Function.Injective preparedSeenScanLane := by
  intro a b h
  cases a <;> cases b <;> simp_all [preparedSeenScanLane]

private def clearSeenPosition (lane : R) : Fragment R where
  Label := Unit
  entry := some ()
  code _ := .dec lane none (some ())

/-- Copy the width, find the high bit, scan the field, and clear the temporary cursor. -/
def preparedSeenRegister (lanes : PreparedSeenLane → R) : Fragment R :=
  let offset := lanes ∘ PreparedSeenLane.offset
  let width := offset .width
  let copy := add (lanes .arity) width (offset .scratch)
  let scan := seenFieldRegister (lanes ∘ preparedSeenScanLane)
  (((((copy.seq (incrementBy width 1)).seq (reverseWindowRegister 4 offset)).seq
    (decrementLane width)).seq scan).seq (clearSeenPosition (offset .position)))

@[expose] def preparedSeenRegisterCost (length base arity : Nat) : Nat :=
  reverseWindowRegisterCost 4 length base (arity + 1) + (5 * arity + 4) +
    seenFieldRegisterCost length arity + (length + 4 * (arity + 1) + 1)

theorem preparedSeenRegisterCost_polynomiallyBounded {length base arity : Nat → Nat}
    (hLength : PolynomiallyBounded length) (hBase : PolynomiallyBounded base)
    (hArity : PolynomiallyBounded arity) :
    PolynomiallyBounded (fun n ↦ preparedSeenRegisterCost (length n) (base n) (arity n)) := by
  have hWidth := hArity.add (PolynomiallyBounded.const 1)
  exact (((reverseWindowRegisterCost_polynomiallyBounded 4 hLength hBase hWidth).add
    (((PolynomiallyBounded.const 5).mul hArity).add (PolynomiallyBounded.const 4))).add
    (seenFieldRegisterCost_polynomiallyBounded hLength hArity)).add
    ((hLength.add ((PolynomiallyBounded.const 4).mul hWidth)).add (PolynomiallyBounded.const 1))

variable [DecidableEq R]

private theorem runsValues_clearSeenPosition (lane : R) (word : BinaryWord) (v : R → Nat) :
    (clearSeenPosition lane).RunsValues word (v lane + 1) v (setValue lane 0 v) := by
  intro output
  exact run_clear word (program := (clearSeenPosition lane).close) rfl
    (cfg := (clearSeenPosition lane).enter (⟨none, v, none, output⟩ : Config R Unit)) rfl

/-- Test the raw packed counter from the measured forward start and retained arity.
The high bit and the number of true lower bits are the only modified registers. -/
theorem runsValues_preparedSeenRegister (lanes : PreparedSeenLane → R)
    (hLanes : Function.Injective lanes) {request : BinaryWord} {fields : MergeRequestFields}
    (hFields : readMergeRequestFields request = some fields) (candidate cert : BinaryWord)
    (before : R → Nat)
    (hLength : before (lanes (.offset .inputLength)) =
      (packedPair (packedPair request candidate) cert).length)
    (hBase : before (lanes (.offset .base)) = 4 * fields.counterStart + 3)
    (hArity : before (lanes .arity) = fields.arity)
    (hZero : ∀ lane, lane ≠ .offset .inputLength → lane ≠ .offset .base →
      lane ≠ .arity → before (lanes lane) = 0) :
    let word := packedPair (packedPair request candidate) cert
    ∃ ticks ≤ preparedSeenRegisterCost word.length (4 * fields.counterStart + 3) fields.arity,
      ∃ after : R → Nat, (preparedSeenRegister lanes).RunsValues word ticks before after ∧
        after (lanes .high) = (fields.counter.getLastD false).toNat ∧
        after (lanes .lowerOnes) = fields.counter.dropLast.count true ∧
        ((after (lanes .high) = 0 ∨ after (lanes .lowerOnes) = 0) ↔
          mergeSeenFieldInRange fields.counter = true) ∧
        ∀ r, r ≠ lanes .high → r ≠ lanes .lowerOnes → after r = before r := by
  let word := packedPair (packedPair request candidate) cert
  let base := 4 * fields.counterStart + 3
  let arity := fields.arity
  let offset := lanes ∘ PreparedSeenLane.offset
  let scan := lanes ∘ preparedSeenScanLane
  let width := offset .width
  let position := offset .position
  let reverse := reverseWindowStart word.length base 4 (arity + 1)
  let copied := setValue width arity before
  let widened := setValue width (arity + 1) before
  let positioned := setValue position reverse widened
  let seeded := setValue width arity positioned
  have hLane (a b : PreparedSeenLane) : lanes a = lanes b ↔ a = b :=
    ⟨fun h ↦ hLanes h, congrArg lanes⟩
  have hWidthZero := hZero (.offset .width) (by simp) (by simp) (by simp)
  have hPositionZero := hZero (.offset .position) (by simp) (by simp) (by simp)
  have hScratchZero := hZero (.offset .scratch) (by simp) (by simp) (by simp)
  have hHighZero := hZero .high (by simp) (by simp) (by simp)
  have hLowZero := hZero .lowerOnes (by simp) (by simp) (by simp)
  have hIndexZero := hZero (.offset .multiplier) (by simp) (by simp) (by simp)
  have hCopy : (add (lanes .arity) width (offset .scratch)).RunsValues word (5 * arity + 2)
      before copied := by
    have hEmpty : before width = 0 := hWidthZero
    simpa only [hEmpty, hArity, Nat.zero_add, arity, copied] using
      runsValues_add (lanes .arity) width (offset .scratch) word before
        (by simp [width, offset, hLane]) (by simp [offset, hLane])
        (by simp [width, offset, hLane]) hScratchZero
  have hCopied : copied width = arity := setValue_same ..
  have hInc : (incrementBy width 1).RunsValues word 1 copied widened := by
    simpa only [hCopied, copied, widened, setValue_replace] using
      runsValues_incrementBy width 1 word copied
  have hOffsetZero (lane : ReverseWindowLane) (hl : lane ≠ .inputLength)
      (hb : lane ≠ .base) (hw : lane ≠ .width) : widened (offset lane) = 0 := by
    exact (setValue_other (by simpa [width, offset, hLane] using hw) ..).trans
      (hZero (.offset lane) (by simpa using hl) (by simpa using hb) (by simp))
  obtain ⟨offsetTicks, hOffsetTime, hOffsetRun⟩ := runsValues_reverseWindowRegister 4 offset
    (hLanes.comp fun _ _ h ↦ PreparedSeenLane.offset.inj h) word widened hOffsetZero
  have hOffsetLength : widened (offset .inputLength) = word.length := by
    exact (setValue_other (by simp [width, offset, hLane]) ..).trans hLength
  have hOffsetBase : widened (offset .base) = base := by
    simpa [widened, width, offset, setValue, hLane] using hBase
  have hOffsetWidth : widened (offset .width) = arity + 1 := setValue_same ..
  rw [hOffsetLength, hOffsetBase, hOffsetWidth] at hOffsetTime hOffsetRun
  have hPositionedWidth : positioned width = arity + 1 := by
    simp [positioned, position, width, offset, widened, setValue, hLane]
  have hDecValues : decrementValues width positioned = seeded := by
    funext r
    by_cases hr : r = width <;> simp [decrementValues, seeded, setValue, hr, hPositionedWidth]
  have hDec : (decrementLane width).RunsValues word 1 positioned seeded := by
    simpa only [hDecValues] using runsValues_decrementLane width word positioned
  have hSeedPosition : seeded (scan .position) = reverse := by
    simp [seeded, positioned, scan, preparedSeenScanLane, position, width, offset, setValue, hLane]
  have hCounter := (readMergeRequestFields_eq_some_iff.mp hFields).1.counter
  have hSeedWidth : seeded (scan .width) = arity := setValue_same ..
  have hSeedHigh : seeded (scan .high) = 0 := by
    simp [seeded, positioned, widened, scan, preparedSeenScanLane, position, width, offset,
      setValue, hLane, hHighZero]
  have hSeedLow : seeded (scan .lowerOnes) = 0 := by
    simp [seeded, positioned, widened, scan, preparedSeenScanLane, position, width, offset,
      setValue, hLane, hLowZero]
  have hSeedIndex : seeded (scan .lookupIndex) = 0 := by
    simp [seeded, positioned, widened, scan, preparedSeenScanLane, position, width, offset,
      setValue, hLane, hIndexZero]
  have hSeedScratch : seeded (scan .scratch) = 0 := by
    simp [seeded, positioned, widened, scan, preparedSeenScanLane, position, width, offset,
      setValue, hLane, hScratchZero]
  obtain ⟨scanTicks, hScanTime, scanned, hScanRun, hResult, hInRange⟩ :=
    runsValues_seenFieldRegister_packed scan (hLanes.comp preparedSeenScanLane_injective)
      hFields candidate cert seeded (by rw [hSeedPosition, hCounter]) hSeedWidth hSeedHigh
      hSeedLow hSeedIndex hSeedScratch
  let after := setValue position 0 scanned
  have hFinal {r : R} (hr : r ≠ position) : after r = scanned r := setValue_other hr ..
  have hFinalHigh : after (lanes .high) = scanned (scan .high) :=
    hFinal (by simp [position, offset, hLane])
  have hFinalLow : after (lanes .lowerOnes) = scanned (scan .lowerOnes) :=
    hFinal (by simp [position, offset, hLane])
  have hFrame (r : R) (hh : r ≠ lanes .high) (hl : r ≠ lanes .lowerOnes) :
      after r = before r := by
    by_cases hPos : r = position
    · subst r
      exact (setValue_same ..).trans hPositionZero.symm
    by_cases hWidth : r = width
    · subst r
      rw [hFinal hPos, show scanned width = 0 from hResult.widthZero]
      exact hWidthZero.symm
    rw [hFinal hPos, hResult.frame r hPos hWidth hh hl]
    simp [seeded, positioned, widened, setValue, hWidth, hPos]
  have hPositionBound : scanned position ≤ word.length + 4 * (arity + 1) := by
    have hp := hResult.position
    change scanned position = seeded (scan .position) + 4 *
      (fields.counter.dropLast.length + 1) at hp
    rw [hp, hSeedPosition, List.length_dropLast, hCounter]
    have hBound : reverse ≤ word.length := (Nat.sub_le ..).trans (Nat.sub_le ..)
    change reverse + 4 * (arity + 1 - 1 + 1) ≤ word.length + 4 * (arity + 1)
    omega
  have hClear := runsValues_clearSeenPosition position word scanned
  have hRun := (((((hCopy.seq hInc).seq hOffsetRun).seq hDec).seq hScanRun).seq hClear)
  refine ⟨_, ?_, after, hRun, hFinalHigh.trans hResult.highBit,
    hFinalLow.trans hResult.lowerOnes, ?_, hFrame⟩
  · change scanTicks ≤ seenFieldRegisterCost word.length arity at hScanTime
    change _ ≤ preparedSeenRegisterCost word.length base arity
    unfold preparedSeenRegisterCost
    omega
  · simpa only [hFinalHigh, hFinalLow] using hInRange

end PvsNP.MCSP
