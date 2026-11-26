module

public import PvsNP.TuringMachine.Registers.LessThan
public import PvsNP.TuringMachine.Registers.Subtract

import Mathlib.Data.List.Nodup

/-! # Register checks for the lengths of a merge request body -/

public section

namespace PvsNP.MCSP

open RegisterMachine RegisterMachine.Fragment

/-- The supplied lengths, computed extents, failure count, and shared workspace. -/
inductive RequestShapeLane where
  | arity | bodyLength | oldLength | candidateWidth | candidateLength
  | minimum | maximum | prefixLength | failures
  | leftCopy | rightCopy | scratch
  deriving DecidableEq

variable {R : Type}

private def addShapePair (left right target scratch : R) (offset : Nat) : Fragment R :=
  ((add left target scratch).seq (add right target scratch)).seq (incrementBy target offset)

private def countShapeLess (lanes : RequestShapeLane → R) (left right : RequestShapeLane) :
    Fragment R :=
  ifLess (lanes left) (lanes right) (lanes .leftCopy) (lanes .rightCopy) (lanes .scratch)
    (incrementBy (lanes .failures) 1) skip

private def countCandidateMismatch (lanes : RequestShapeLane → R) : Fragment R :=
  ifEqual (lanes .candidateLength) (lanes .candidateWidth) (lanes .leftCopy) (lanes .rightCopy)
    (lanes .scratch) skip (incrementBy (lanes .failures) 1)

/-- Compute the body bounds and prefix length, and count failed extent checks. -/
def requestShapeRegister (lanes : RequestShapeLane → R) : Fragment R :=
  let lower := addShapePair (lanes .arity) (lanes .oldLength) (lanes .minimum) (lanes .scratch) 2
  let upper := addShapePair (lanes .minimum) (lanes .candidateWidth) (lanes .maximum)
    (lanes .scratch) 0
  let pref := (add (lanes .bodyLength) (lanes .prefixLength) (lanes .scratch)).seq
    (subtract (lanes .minimum) (lanes .prefixLength) (lanes .leftCopy) (lanes .scratch))
  let aboveMinimum := countShapeLess lanes .bodyLength .minimum
  let belowMaximum := countShapeLess lanes .maximum .bodyLength
  (((((lower.seq upper).seq pref).seq aboveMinimum).seq belowMaximum).seq
    (countCandidateMismatch lanes))

@[expose] def requestShapeRegisterCost (arity body old expected actual : Nat) : Nat :=
  40 * (arity + body + old + expected + actual + 3)

theorem requestShapeRegisterCost_polynomiallyBounded {arity body old expected actual : Nat → Nat}
    (hArity : PolynomiallyBounded arity) (hBody : PolynomiallyBounded body)
    (hOld : PolynomiallyBounded old) (hExpected : PolynomiallyBounded expected)
    (hActual : PolynomiallyBounded actual) :
    PolynomiallyBounded (fun n ↦ requestShapeRegisterCost (arity n) (body n) (old n)
      (expected n) (actual n)) :=
  (PolynomiallyBounded.const 40).mul
    (((((hArity.add hBody).add hOld).add hExpected).add hActual).add (PolynomiallyBounded.const 3))

/-- Extents and the exact eligibility test, with a frame for the original data. -/
structure RequestShapeRegisterResult (lanes : RequestShapeLane → R) (before after : R → Nat) :
    Prop where
  minimum : after (lanes .minimum) = before (lanes .arity) + 2 + before (lanes .oldLength)
  maximum : after (lanes .maximum) = after (lanes .minimum) + before (lanes .candidateWidth)
  prefixLength : after (lanes .prefixLength) = before (lanes .bodyLength) - after (lanes .minimum)
  failures : after (lanes .failures) =
    (decide (before (lanes .bodyLength) < after (lanes .minimum))).toNat +
    (decide (after (lanes .maximum) < before (lanes .bodyLength))).toNat +
    (decide (before (lanes .candidateLength) ≠ before (lanes .candidateWidth))).toNat
  valid : after (lanes .failures) = 0 ↔
    after (lanes .minimum) ≤ before (lanes .bodyLength) ∧
    before (lanes .bodyLength) ≤ after (lanes .maximum) ∧
    before (lanes .candidateLength) = before (lanes .candidateWidth)
  frame : ∀ r, r ≠ lanes .minimum → r ≠ lanes .maximum → r ≠ lanes .prefixLength →
    r ≠ lanes .failures → after r = before r

variable [DecidableEq R]

private theorem runsValues_addShapePair (left right target scratch : R) (offset : Nat)
    (x : BinaryWord) (v : R → Nat) (hLT : left ≠ target) (hLS : left ≠ scratch)
    (hRT : right ≠ target) (hRS : right ≠ scratch) (hTS : target ≠ scratch)
    (hTarget : v target = 0) (hScratch : v scratch = 0) :
    (addShapePair left right target scratch offset).RunsValues x
      (5 * v left + 2 + (5 * v right + 2) + offset) v
      (setValue target (v left + offset + v right) v) := by
  let first := setValue target (v left) v
  let total := setValue target (v left + v right) v
  have hFirst : (add left target scratch).RunsValues x (5 * v left + 2) v first := by
    simpa only [hTarget, Nat.zero_add, first] using
      runsValues_add left target scratch x v hLT hLS hTS hScratch
  have hRight : first right = v right := setValue_other hRT ..
  have hTarget' : first target = v left := setValue_same ..
  have hScratch' : first scratch = 0 := (setValue_other hTS.symm ..).trans hScratch
  have hSecond : (add right target scratch).RunsValues x (5 * v right + 2) first total := by
    simpa only [hRight, hTarget', first, total, setValue_replace] using
      runsValues_add right target scratch x first hRT hRS hTS hScratch'
  have hTotal : total target = v left + v right := setValue_same ..
  have hRun := (hFirst.seq hSecond).seq (runsValues_incrementBy target offset x total)
  simpa only [addShapePair, hTotal, total, setValue_replace, Nat.add_right_comm] using hRun

private def shapeCompareLanes (left right : RequestShapeLane) : Fin 5 → RequestShapeLane :=
  ([left, right, .leftCopy, .rightCopy, .scratch] : List RequestShapeLane).get

private theorem runsValues_countShapeLess (lanes : RequestShapeLane → R)
    (hLanes : Function.Injective lanes) (left right : RequestShapeLane)
    (hDistinct : [left, right, .leftCopy, .rightCopy, .scratch].Nodup) (x : BinaryWord)
    (v : R → Nat) (hLeftCopy : v (lanes .leftCopy) = 0) (hRightCopy : v (lanes .rightCopy) = 0)
    (hScratch : v (lanes .scratch) = 0) :
    let bad := (decide (v (lanes left) < v (lanes right))).toNat
    (countShapeLess lanes left right).RunsValues x
      (ifEqualTime (v (lanes left)) (v (lanes right)) + bad) v
      (setValue (lanes .failures) (v (lanes .failures) + bad) v) := by
  let more := incrementBy (lanes .failures) 1
  let test := lanes ∘ shapeCompareLanes left right
  have hTest : Function.Injective test := hLanes.comp hDistinct.injective_get
  let bad := (decide (v (lanes left) < v (lanes right))).toNat
  have hBranch : (if v (lanes left) < v (lanes right) then more else skip).RunsValues
      x bad v (setValue (lanes .failures) (v (lanes .failures) + bad) v) := by
    by_cases h : v (lanes left) < v (lanes right)
    · simpa only [ite_eq_left h, bad, decide_eq_true h, Bool.toNat_true, more] using
        runsValues_incrementBy (lanes .failures) 1 x v
    · simpa only [ite_eq_right h, bad, decide_eq_false h, Bool.toNat_false, Nat.add_zero,
        setValue_current] using (runsValues_skip x v)
  exact runsValues_ifLess test hTest more skip x v hLeftCopy hRightCopy hScratch hBranch

private theorem runsValues_countCandidateMismatch (lanes : RequestShapeLane → R)
    (hLanes : Function.Injective lanes) (x : BinaryWord) (v : R → Nat)
    (hLeftCopy : v (lanes .leftCopy) = 0) (hRightCopy : v (lanes .rightCopy) = 0)
    (hScratch : v (lanes .scratch) = 0) :
    let left := v (lanes .candidateLength)
    let right := v (lanes .candidateWidth)
    let bad := (decide (left ≠ right)).toNat
    (countCandidateMismatch lanes).RunsValues x (ifEqualTime left right + bad) v
      (setValue (lanes .failures) (v (lanes .failures) + bad) v) := by
  have hNe {a b : RequestShapeLane} (h : a ≠ b) : lanes a ≠ lanes b := fun e ↦ h (hLanes e)
  let more := incrementBy (lanes .failures) 1
  dsimp only
  intro output
  let cfg : Config R Unit := ⟨none, v, none, output⟩
  by_cases h : v (lanes .candidateLength) = v (lanes .candidateWidth)
  · have hRun := run_ifEqual_eq (left := lanes .candidateLength) (right := lanes .candidateWidth)
      (equal := skip) (different := more) x (hNe (by decide)) (hNe (by decide))
      (hNe (by decide)) (hNe (by decide)) (hNe (by decide)) (hNe (by decide))
      (hNe (by decide)) (hNe (by decide)) cfg hLeftCopy hRightCopy hScratch h
      (runsValues_skip x v output) rfl
    simpa [countCandidateMismatch, h, cfg, more, setValue_current] using hRun
  · have hRun := run_ifEqual_ne (left := lanes .candidateLength) (right := lanes .candidateWidth)
      (equal := skip) (different := more) x (hNe (by decide)) (hNe (by decide))
      (hNe (by decide)) (hNe (by decide)) (hNe (by decide)) (hNe (by decide))
      (hNe (by decide)) (hNe (by decide)) cfg hLeftCopy hRightCopy hScratch h
      (runsValues_incrementBy (lanes .failures) 1 x v output) rfl
    simpa [countCandidateMismatch, h, cfg, more] using hRun

/-- Validate a request's body and candidate extents from their unary lengths. -/
theorem runsValues_requestShapeRegister (lanes : RequestShapeLane → R)
    (hLanes : Function.Injective lanes) (x : BinaryWord) (before : R → Nat)
    (hZero : ∀ lane ∈ ([.minimum, .maximum, .prefixLength, .failures,
      .leftCopy, .rightCopy, .scratch] : List RequestShapeLane), before (lanes lane) = 0) :
    ∃ ticks ≤ requestShapeRegisterCost (before (lanes .arity)) (before (lanes .bodyLength))
        (before (lanes .oldLength)) (before (lanes .candidateWidth))
        (before (lanes .candidateLength)),
      ∃ after : R → Nat, (requestShapeRegister lanes).RunsValues x ticks before after ∧
        RequestShapeRegisterResult lanes before after := by
  let arity := before (lanes .arity)
  let body := before (lanes .bodyLength)
  let old := before (lanes .oldLength)
  let expected := before (lanes .candidateWidth)
  let actual := before (lanes .candidateLength)
  let minimum := arity + 2 + old
  let maximum := minimum + expected
  let badLower := (decide (body < minimum)).toNat
  let badUpper := (decide (maximum < body)).toNat
  let badCandidate := (decide (actual ≠ expected)).toNat
  have hNe {a b : RequestShapeLane} (h : a ≠ b) : lanes a ≠ lanes b := fun e ↦ h (hLanes e)
  have hLane (a b : RequestShapeLane) : lanes a = lanes b ↔ a = b :=
    ⟨fun e ↦ hLanes e, congrArg lanes⟩
  have hMinZero := hZero .minimum (by simp)
  have hMaxZero := hZero .maximum (by simp)
  have hPrefixZero := hZero .prefixLength (by simp)
  have hFailureZero := hZero .failures (by simp)
  have hLeftZero := hZero .leftCopy (by simp)
  have hRightZero := hZero .rightCopy (by simp)
  have hScratchZero := hZero .scratch (by simp)
  let lowered := setValue (lanes .minimum) minimum before
  have hLower : (addShapePair (lanes .arity) (lanes .oldLength) (lanes .minimum)
      (lanes .scratch) 2).RunsValues x (5 * arity + 2 + (5 * old + 2) + 2) before lowered :=
    runsValues_addShapePair (lanes .arity) (lanes .oldLength) (lanes .minimum) (lanes .scratch)
      2 x before (hNe (by decide)) (hNe (by decide)) (hNe (by decide)) (hNe (by decide))
      (hNe (by decide)) hMinZero hScratchZero
  have hLowerMin : lowered (lanes .minimum) = minimum := setValue_same ..
  have hLowerExpected : lowered (lanes .candidateWidth) = expected :=
    setValue_other (hNe (by decide)) ..
  let bounded := setValue (lanes .maximum) maximum lowered
  have hUpper : (addShapePair (lanes .minimum) (lanes .candidateWidth) (lanes .maximum)
      (lanes .scratch) 0).RunsValues x
      (5 * minimum + 2 + (5 * expected + 2) + 0) lowered bounded := by
    have hEmpty : lowered (lanes .maximum) = 0 :=
      (setValue_other (hNe (by decide)) ..).trans hMaxZero
    have hScratch : lowered (lanes .scratch) = 0 :=
      (setValue_other (hNe (by decide)) ..).trans hScratchZero
    simpa only [hLowerMin, hLowerExpected, bounded, maximum, Nat.add_zero] using
      runsValues_addShapePair (lanes .minimum) (lanes .candidateWidth) (lanes .maximum)
        (lanes .scratch) 0 x lowered (hNe (by decide)) (hNe (by decide)) (hNe (by decide))
        (hNe (by decide)) (hNe (by decide)) hEmpty hScratch
  have hBoundedBody : bounded (lanes .bodyLength) = body := by
    simp [bounded, lowered, setValue, hLane, body]
  have hBoundedPref : bounded (lanes .prefixLength) = 0 := by
    simp [bounded, lowered, setValue, hLane, hPrefixZero]
  have hBoundedScratch : bounded (lanes .scratch) = 0 := by
    simp [bounded, lowered, setValue, hLane, hScratchZero]
  let copied := setValue (lanes .prefixLength) body bounded
  have hCopy : (add (lanes .bodyLength) (lanes .prefixLength) (lanes .scratch)).RunsValues
      x (5 * body + 2) bounded copied := by
    simpa only [hBoundedBody, hBoundedPref, Nat.zero_add, copied] using
      runsValues_add (lanes .bodyLength) (lanes .prefixLength) (lanes .scratch) x bounded
        (hNe (by decide)) (hNe (by decide)) (hNe (by decide)) hBoundedScratch
  let shaped := setValue (lanes .prefixLength) (body - minimum) bounded
  have hSubtract : (subtract (lanes .minimum) (lanes .prefixLength) (lanes .leftCopy)
      (lanes .scratch)).RunsValues x (7 * minimum + 3) copied shaped := by
    have hCopiedLeft : copied (lanes .leftCopy) = 0 := by
      simp [copied, bounded, lowered, setValue, hLane, hLeftZero]
    have hCopiedScratch : copied (lanes .scratch) = 0 :=
      (setValue_other (hNe (by decide)) ..).trans hBoundedScratch
    have hCopiedMin : copied (lanes .minimum) = minimum := by
      simp [copied, bounded, lowered, setValue, hLane]
    have hCopiedPref : copied (lanes .prefixLength) = body := setValue_same ..
    simpa only [hCopiedMin, hCopiedPref, copied, shaped, setValue_replace] using
      runsValues_subtract (lanes .minimum) (lanes .prefixLength) (lanes .leftCopy)
        (lanes .scratch) x copied (hNe (by decide)) (hNe (by decide)) (hNe (by decide))
        (hNe (by decide)) hCopiedLeft hCopiedScratch
  have hShapedFrame {r : R} (hm : r ≠ lanes .minimum) (hx : r ≠ lanes .maximum)
      (hp : r ≠ lanes .prefixLength) : shaped r = before r := by
    simp [shaped, bounded, lowered, setValue, hm, hx, hp]
  have hShapedMin : shaped (lanes .minimum) = minimum := by
    simp [shaped, bounded, lowered, setValue, hLane]
  have hShapedMax : shaped (lanes .maximum) = maximum := by
    simp [shaped, bounded, setValue, hLane]
  have hShapedBody : shaped (lanes .bodyLength) = body :=
    hShapedFrame (hNe (by decide)) (hNe (by decide)) (hNe (by decide))
  let withFailures (bad : Nat) := setValue (lanes .failures) bad shaped
  have hFailureFrame (bad : Nat) (r : RequestShapeLane) (hr : r ≠ .failures) :
      withFailures bad (lanes r) = shaped (lanes r) := setValue_other (hNe hr) ..
  have hWithLeft (bad : Nat) : withFailures bad (lanes .leftCopy) = 0 :=
    (hFailureFrame bad .leftCopy (by decide)).trans
      ((hShapedFrame (hNe (by decide)) (hNe (by decide)) (hNe (by decide))).trans hLeftZero)
  have hWithRight (bad : Nat) : withFailures bad (lanes .rightCopy) = 0 :=
    (hFailureFrame bad .rightCopy (by decide)).trans
      ((hShapedFrame (hNe (by decide)) (hNe (by decide)) (hNe (by decide))).trans hRightZero)
  have hWithScratch (bad : Nat) : withFailures bad (lanes .scratch) = 0 :=
    (hFailureFrame bad .scratch (by decide)).trans
      ((hShapedFrame (hNe (by decide)) (hNe (by decide)) (hNe (by decide))).trans hScratchZero)
  have hWithValue (bad : Nat) : withFailures bad (lanes .failures) = bad := setValue_same ..
  have hWithZero : withFailures 0 = shaped := by
    have hShapedZero : shaped (lanes .failures) = 0 :=
      (hShapedFrame (hNe (by decide)) (hNe (by decide)) (hNe (by decide))).trans hFailureZero
    simpa only [withFailures, hShapedZero] using setValue_current (lanes .failures) shaped
  have hCheckLess (l r : RequestShapeLane) (hl : l ≠ .failures) (hr : r ≠ .failures)
      (hDistinct : [l, r, .leftCopy, .rightCopy, .scratch].Nodup) (bad : Nat) :
      let next := (decide (shaped (lanes l) < shaped (lanes r))).toNat
      (countShapeLess lanes l r).RunsValues x
        (ifEqualTime (shaped (lanes l)) (shaped (lanes r)) + next)
        (withFailures bad) (withFailures (bad + next)) := by
    have hRun := runsValues_countShapeLess lanes hLanes l r hDistinct x (withFailures bad)
      (hWithLeft bad) (hWithRight bad) (hWithScratch bad)
    simpa only [hFailureFrame bad l hl, hFailureFrame bad r hr, hWithValue,
      withFailures, setValue_replace] using hRun
  have hCheckLower : (countShapeLess lanes .bodyLength .minimum).RunsValues x
      (ifEqualTime body minimum + badLower) shaped (withFailures badLower) := by
    simpa only [hShapedBody, hShapedMin, hWithZero, Nat.zero_add, badLower] using
      hCheckLess .bodyLength .minimum (by decide) (by decide) (by decide) 0
  have hCheckUpper : (countShapeLess lanes .maximum .bodyLength).RunsValues x
      (ifEqualTime maximum body + badUpper) (withFailures badLower)
      (withFailures (badLower + badUpper)) := by
    simpa only [hShapedBody, hShapedMax, badUpper] using
      hCheckLess .maximum .bodyLength (by decide) (by decide) (by decide) badLower
  let checked := withFailures (badLower + badUpper)
  let after := withFailures (badLower + badUpper + badCandidate)
  have hCheckCandidate : (countCandidateMismatch lanes).RunsValues x
      (ifEqualTime actual expected + badCandidate) checked after := by
    have hActual : checked (lanes .candidateLength) = actual :=
      (hFailureFrame _ .candidateLength (by decide)).trans
        (hShapedFrame (hNe (by decide)) (hNe (by decide)) (hNe (by decide)))
    have hExpected : checked (lanes .candidateWidth) = expected :=
      (hFailureFrame _ .candidateWidth (by decide)).trans
        (hShapedFrame (hNe (by decide)) (hNe (by decide)) (hNe (by decide)))
    have hRun := runsValues_countCandidateMismatch lanes hLanes x checked (hWithLeft _)
      (hWithRight _) (hWithScratch _)
    simpa only [hActual, hExpected, checked, after, hWithValue, withFailures,
      setValue_replace, badCandidate] using hRun
  have hRun := ((((hLower.seq hUpper).seq (hCopy.seq hSubtract)).seq hCheckLower).seq
    hCheckUpper).seq hCheckCandidate
  refine ⟨_, ?_, after, hRun, ?_⟩
  · have hLo : badLower ≤ 1 := Bool.toNat_le _
    have hHi : badUpper ≤ 1 := Bool.toNat_le _
    have hCand : badCandidate ≤ 1 := Bool.toNat_le _
    unfold requestShapeRegisterCost ifEqualTime
    dsimp only [minimum, maximum] at *
    omega
  · have hMin : after (lanes .minimum) = minimum :=
      (hFailureFrame _ .minimum (by decide)).trans hShapedMin
    have hMax : after (lanes .maximum) = maximum :=
      (hFailureFrame _ .maximum (by decide)).trans hShapedMax
    have hPref : after (lanes .prefixLength) = body - minimum :=
      (hFailureFrame _ .prefixLength (by decide)).trans (setValue_same ..)
    have hBad : after (lanes .failures) = badLower + badUpper + badCandidate := setValue_same ..
    refine ⟨hMin, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hMax, hMin]
    · rw [hPref, hMin]
    · rw [hBad, hMin, hMax]
    · rw [hBad, hMin, hMax]
      simp [badLower, badUpper, badCandidate, body, actual, expected, and_assoc]
    · intro r hm hx hp hf
      exact (setValue_other hf ..).trans (hShapedFrame hm hx hp)

end PvsNP.MCSP
