module

public import PvsNP.MCSP.TraceInputRegister
public import PvsNP.TuringMachine.Registers.Affine
public import PvsNP.TuringMachine.Registers.Subtract

import all PvsNP.MCSP.DescriptionOffsetRegister
import all PvsNP.TuringMachine.Registers.ReverseWindow

/-! # Calculate the reverse addresses of trace input fields -/

public section

namespace PvsNP.MCSP

open RegisterMachine RegisterMachine.Fragment

/-- Inputs, three reverse cursors, and restored workspace. -/
inductive TraceInputPositionLane where
  | arity | oldCount | newCount | certificateLength
  | rowPosition | tracePosition (old : Bool)
  | distance | predecessor | work | scratch
  deriving DecidableEq

variable {R : Type}

private def traceInputRowPositionRegister (lanes : TraceInputPositionLane → R) : Fragment R :=
  let distance := lanes .distance
  let predecessor := lanes .predecessor
  let work := lanes .work
  let scratch := lanes .scratch
  let last := copyPredecessor (lanes .certificateLength) distance scratch
  let rowIndex := copyPredecessor (lanes .arity) predecessor scratch
  let subtractIndex := subtract predecessor distance work scratch
  let stride := accumulateAffine distance (lanes .rowPosition) work scratch 2 0
  (((((last.seq rowIndex).seq subtractIndex).seq stride).seq (clearReverseLane distance)).seq
    (clearReverseLane predecessor))

private def traceInputTracePositionsRegister (lanes : TraceInputPositionLane → R) : Fragment R :=
  let work := lanes .work
  let scratch := lanes .scratch
  let old := lanes (.tracePosition true)
  let new := lanes (.tracePosition false)
  let newArity := accumulateAffine (lanes .arity) new work scratch 2 2
  let newCount := accumulateAffine (lanes .newCount) new work scratch 2 0
  let startOld := add new old scratch
  let oldArity := accumulateAffine (lanes .arity) old work scratch 2 0
  let oldCount := accumulateAffine (lanes .oldCount) old work scratch 2 0
  ((((newArity.seq newCount).seq startOld).seq oldArity).seq oldCount)

/-- Compute the cursors from the measured certificate length and circuit counts. -/
def traceInputPositionRegister (lanes : TraceInputPositionLane → R) : Fragment R :=
  (traceInputRowPositionRegister lanes).seq (traceInputTracePositionsRegister lanes)

@[expose] def traceInputPositionRegisterCost (certificateLength arity oldCount newCount : Nat) :
    Nat :=
  16 * certificateLength + 43 * arity + 10 * oldCount + 20 * newCount + 70

theorem traceInputPositionRegisterCost_polynomiallyBounded
    {certificateLength arity oldCount newCount : Nat → Nat}
    (hLength : PolynomiallyBounded certificateLength) (hArity : PolynomiallyBounded arity)
    (hOld : PolynomiallyBounded oldCount) (hNew : PolynomiallyBounded newCount) :
    PolynomiallyBounded (fun n ↦ traceInputPositionRegisterCost (certificateLength n)
      (arity n) (oldCount n) (newCount n)) := by
  let lit := PolynomiallyBounded.const
  exact (((((lit 16).mul hLength).add ((lit 43).mul hArity)).add ((lit 10).mul hOld)).add
    ((lit 20).mul hNew)).add (lit 70)

/-- Only the three cursor destinations may differ after the preparation. -/
structure TraceInputPositionRegisterResult (lanes : TraceInputPositionLane → R)
    (before after : R → Nat) : Prop where
  row : after (lanes .rowPosition) =
    traceInputRowPosition (before (lanes .certificateLength)) (before (lanes .arity))
  old : after (lanes (.tracePosition true)) =
    2 * ((before (lanes .arity) + before (lanes .oldCount)) +
      (before (lanes .arity) + before (lanes .newCount)) + 1)
  candidate : after (lanes (.tracePosition false)) =
    2 * (before (lanes .arity) + before (lanes .newCount) + 1)
  frame : ∀ r, r ≠ lanes .rowPosition → (∀ side, r ≠ lanes (.tracePosition side)) →
    after r = before r

variable [DecidableEq R]

private theorem runsValues_traceInputRowPositionRegister (lanes : TraceInputPositionLane → R)
    (hLanes : Function.Injective lanes) (word : BinaryWord) (v : R → Nat)
    (hDistance : v (lanes .distance) = 0) (hPredecessor : v (lanes .predecessor) = 0)
    (hWork : v (lanes .work) = 0) (hScratch : v (lanes .scratch) = 0)
    (hRow : v (lanes .rowPosition) = 0) :
    let L := v (lanes .certificateLength)
    let n := v (lanes .arity)
    ∃ ticks ≤ 16 * L + 13 * n + 20,
      (traceInputRowPositionRegister lanes).RunsValues word ticks v
        (setValue (lanes .rowPosition) (traceInputRowPosition L n) v) := by
  let L := v (lanes .certificateLength)
  let n := v (lanes .arity)
  let delta := L - 1 - (n - 1)
  let distance := lanes .distance
  let predecessor := lanes .predecessor
  let work := lanes .work
  let scratch := lanes .scratch
  let row := lanes .rowPosition
  let v1 := setValue distance (L - 1) v
  let v2 := setValue predecessor (n - 1) v1
  let v3 := setValue distance delta v2
  let v4 := setValue row (2 * delta) v3
  let v5 := setValue distance 0 v4
  let final := setValue row (2 * delta) v
  have hLane (a b : TraceInputPositionLane) : lanes a = lanes b ↔ a = b :=
    ⟨fun e ↦ hLanes e, congrArg lanes⟩
  have h1 := runsValues_copyPredecessor (lanes .certificateLength) distance scratch word v
    (by simp [distance, hLane]) (by simp [scratch, hLane]) (by simp [distance, scratch, hLane])
    hDistance hScratch
  have h2 := runsValues_copyPredecessor (lanes .arity) predecessor scratch word v1
    (by simp [predecessor, hLane]) (by simp [scratch, hLane])
    (by simp [predecessor, scratch, hLane])
    (by simp [v1, setValue, distance, predecessor, hLane, hPredecessor])
    (by simp [v1, setValue, distance, scratch, hLane, hScratch])
  rw [show v1 (lanes .arity) = n by simp [v1, setValue, distance, hLane, n]] at h2
  have hPred : v2 predecessor = n - 1 := setValue_same ..
  have hLast : v2 distance = L - 1 := by
    simp [v2, v1, setValue, distance, predecessor, hLane]
  have h3 := runsValues_subtract predecessor distance work scratch word v2
    (by simp [predecessor, work, hLane]) (by simp [predecessor, scratch, hLane])
    (by simp [work, scratch, hLane]) (by simp [distance, work, hLane])
    (by simp [v2, v1, setValue, work, distance, predecessor, hLane, hWork])
    (by simp [v2, v1, setValue, scratch, distance, predecessor, hLane, hScratch])
  rw [hPred, hLast] at h3
  have hDelta : v3 distance = delta := setValue_same ..
  have hNodup : [distance, row, work, scratch].Nodup :=
    ((by decide : ([.distance, .rowPosition, .work, .scratch] :
      List TraceInputPositionLane).Nodup)).map hLanes
  have h4 := runsValues_accumulateAffine distance row work scratch 2 0 word v3 hNodup
    (by simp [v3, v2, v1, setValue, work, distance, predecessor, hLane, hWork])
    (by simp [v3, v2, v1, setValue, scratch, distance, predecessor, hLane, hScratch])
  have hRowZero : v3 row = 0 := by
    simp [v3, v2, v1, setValue, row, distance, predecessor, hLane, hRow]
  rw [hDelta, hRowZero, Nat.zero_add, Nat.add_zero] at h4
  have hDistance4 : v4 distance = delta := by
    simp [v4, v3, setValue, row, distance, hLane]
  have h5 : (clearReverseLane distance).RunsValues word (delta + 1) v4 v5 := by
    simpa only [hDistance4, v5] using runsValues_clearReverseLane distance word v4
  have hPred5 : v5 predecessor = n - 1 := by
    simp [v5, v4, v3, v2, setValue, row, distance, predecessor, hLane]
  have hRestore : setValue predecessor 0 v5 = final := by
    funext r
    by_cases hd : r = distance
    · subst r
      simp [v5, final, setValue, distance, predecessor, row, hLane, hDistance]
    by_cases hp : r = predecessor
    · subst r
      simp [final, setValue, predecessor, row, hLane, hPredecessor]
    simp [v5, v4, v3, v2, v1, final, setValue, hd, hp]
  have h6 := runsValues_clearReverseLane predecessor word v5
  rw [hPred5, hRestore] at h6
  have hRun := ((((h1.seq h2).seq h3).seq h4).seq h5).seq h6
  have hCost : (5 * L + 2 + 1) + (5 * n + 2 + 1) + (7 * (n - 1) + 3) +
      affineTime 2 0 delta + (delta + 1) + (n - 1 + 1) ≤ 16 * L + 13 * n + 20 := by
    unfold affineTime delta
    omega
  exact ⟨_, hCost, hRun⟩

private theorem runsValues_traceInputTracePositionsRegister
    (lanes : TraceInputPositionLane → R) (hLanes : Function.Injective lanes)
    (word : BinaryWord) (v : R → Nat) (hWork : v (lanes .work) = 0)
    (hScratch : v (lanes .scratch) = 0) (hOld : v (lanes (.tracePosition true)) = 0)
    (hCandidate : v (lanes (.tracePosition false)) = 0) :
    let n := v (lanes .arity)
    let o := v (lanes .oldCount)
    let c := v (lanes .newCount)
    (traceInputTracePositionsRegister lanes).RunsValues word (30 * n + 10 * o + 20 * c + 50) v
      (setValue (lanes (.tracePosition true)) (2 * ((n + o) + (n + c) + 1))
        (setValue (lanes (.tracePosition false)) (2 * (n + c + 1)) v)) := by
  let n := v (lanes .arity)
  let o := v (lanes .oldCount)
  let c := v (lanes .newCount)
  let work := lanes .work
  let scratch := lanes .scratch
  let old := lanes (.tracePosition true)
  let new := lanes (.tracePosition false)
  let newStart := 2 * n + 2
  let newPosition := 2 * (n + c + 1)
  let oldPartial := newPosition + 2 * n
  let oldPosition := 2 * ((n + o) + (n + c) + 1)
  let v1 := setValue new newStart v
  let v2 := setValue new newPosition v
  let v3 := setValue old newPosition v2
  let v4 := setValue old oldPartial v2
  let final := setValue old oldPosition v2
  have hLane (a b : TraceInputPositionLane) : lanes a = lanes b ↔ a = b :=
    ⟨fun e ↦ hLanes e, congrArg lanes⟩
  have runAffine (source target : TraceInputPositionLane) (constant : Nat) (values : R → Nat)
      (hNames : [source, target, .work, .scratch].Nodup)
      (hw : values work = 0) (hs : values scratch = 0) :
      (accumulateAffine (lanes source) (lanes target) work scratch 2 constant).RunsValues word
        (affineTime 2 constant (values (lanes source))) values
        (setValue (lanes target) (values (lanes target) + 2 * values (lanes source) + constant)
          values) :=
    runsValues_accumulateAffine (lanes source) (lanes target) work scratch 2 constant word
      values (hNames.map hLanes) hw hs
  have h1 : (accumulateAffine (lanes .arity) new work scratch 2 2).RunsValues word
      (affineTime 2 2 n) v v1 := by
    simpa only [v1, newStart, hCandidate, Nat.zero_add] using
      runAffine .arity (.tracePosition false) 2 v (by decide) hWork hScratch
  have h2 : (accumulateAffine (lanes .newCount) new work scratch 2 0).RunsValues word
      (affineTime 2 0 c) v1 v2 := by
    have hSource : v1 (lanes .newCount) = c := by simp [v1, new, setValue, hLane, c]
    have hTarget : v1 new = newStart := setValue_same ..
    have hDestination : newStart + 2 * c = newPosition := by
      unfold newStart newPosition
      omega
    have hRun := runAffine .newCount (.tracePosition false) 0 v1 (by decide)
      (by simp [v1, new, work, setValue, hLane, hWork])
      (by simp [v1, new, scratch, setValue, hLane, hScratch])
    change (accumulateAffine (lanes .newCount) new work scratch 2 0).RunsValues word
      (affineTime 2 0 (v1 (lanes .newCount))) v1
      (setValue new (v1 new + 2 * v1 (lanes .newCount) + 0) v1) at hRun
    rw [hSource, hTarget, Nat.add_zero, hDestination] at hRun
    simpa only [v1, v2, setValue_replace] using hRun
  have h3 : (add new old scratch).RunsValues word (5 * newPosition + 2) v2 v3 := by
    have hValue : v2 new = newPosition := setValue_same ..
    have hTarget : v2 old = 0 := by simp [v2, new, old, setValue, hLane, hOld]
    simpa only [hValue, hTarget, Nat.zero_add, v3] using
      runsValues_add new old scratch word v2
        (by simp [new, old, hLane]) (by simp [new, scratch, hLane])
        (by simp [old, scratch, hLane]) (by simp [v2, new, scratch, setValue, hLane, hScratch])
  have h4 : (accumulateAffine (lanes .arity) old work scratch 2 0).RunsValues word
      (affineTime 2 0 n) v3 v4 := by
    have hSource : v3 (lanes .arity) = n := by simp [v3, v2, new, old, setValue, hLane, n]
    have hTarget : v3 old = newPosition := setValue_same ..
    have hRun := runAffine .arity (.tracePosition true) 0 v3 (by decide)
      (by simp [v3, v2, new, old, work, setValue, hLane, hWork])
      (by simp [v3, v2, new, old, scratch, setValue, hLane, hScratch])
    change (accumulateAffine (lanes .arity) old work scratch 2 0).RunsValues word
      (affineTime 2 0 (v3 (lanes .arity))) v3
      (setValue old (v3 old + 2 * v3 (lanes .arity) + 0) v3) at hRun
    rw [hSource, hTarget, Nat.add_zero] at hRun
    simpa only [oldPartial, v3, v4, setValue_replace] using hRun
  have h5 : (accumulateAffine (lanes .oldCount) old work scratch 2 0).RunsValues word
      (affineTime 2 0 o) v4 final := by
    have hSource : v4 (lanes .oldCount) = o := by
      simp [v4, v2, new, old, setValue, hLane, o]
    have hTarget : v4 old = oldPartial := setValue_same ..
    have hDestination : oldPartial + 2 * o = oldPosition := by
      unfold oldPartial newPosition oldPosition
      omega
    have hRun := runAffine .oldCount (.tracePosition true) 0 v4 (by decide)
      (by simp [v4, v2, new, old, work, setValue, hLane, hWork])
      (by simp [v4, v2, new, old, scratch, setValue, hLane, hScratch])
    change (accumulateAffine (lanes .oldCount) old work scratch 2 0).RunsValues word
      (affineTime 2 0 (v4 (lanes .oldCount))) v4
      (setValue old (v4 old + 2 * v4 (lanes .oldCount) + 0) v4) at hRun
    rw [hSource, hTarget, Nat.add_zero, hDestination] at hRun
    simpa only [v4, final, setValue_replace] using hRun
  dsimp only
  change (traceInputTracePositionsRegister lanes).RunsValues word _ v final
  have hCost : affineTime 2 2 n + affineTime 2 0 c + (5 * newPosition + 2) +
      affineTime 2 0 n + affineTime 2 0 o = 30 * n + 10 * o + 20 * c + 50 := by
    unfold affineTime newPosition
    omega
  rw [← hCost]
  exact (((h1.seq h2).seq h3).seq h4).seq h5

/-- The preparation preserves all four inputs and restores the workspace. -/
theorem runsValues_traceInputPositionRegister
    (lanes : TraceInputPositionLane → R) (hLanes : Function.Injective lanes)
    (word : BinaryWord) (before : R → Nat)
    (hZero : ∀ lane, lane ∉ [.arity, .oldCount, .newCount, .certificateLength] →
      before (lanes lane) = 0) :
    let L := before (lanes .certificateLength)
    let n := before (lanes .arity)
    let o := before (lanes .oldCount)
    let c := before (lanes .newCount)
    ∃ ticks ≤ traceInputPositionRegisterCost L n o c, ∃ after,
      (traceInputPositionRegister lanes).RunsValues word ticks before after ∧
        TraceInputPositionRegisterResult lanes before after := by
  let L := before (lanes .certificateLength)
  let n := before (lanes .arity)
  let o := before (lanes .oldCount)
  let c := before (lanes .newCount)
  let row := lanes .rowPosition
  let old := lanes (.tracePosition true)
  let new := lanes (.tracePosition false)
  let withRow := setValue row (traceInputRowPosition L n) before
  let withNew := setValue new (2 * (n + c + 1)) withRow
  let after := setValue old (2 * ((n + o) + (n + c) + 1)) withNew
  have hLane (a b : TraceInputPositionLane) : lanes a = lanes b ↔ a = b :=
    ⟨fun e ↦ hLanes e, congrArg lanes⟩
  obtain ⟨rowTicks, hRowTime, hRow⟩ :=
    runsValues_traceInputRowPositionRegister lanes hLanes word before
      (hZero _ (by simp)) (hZero _ (by simp)) (hZero _ (by simp)) (hZero _ (by simp))
      (hZero _ (by simp))
  have hRestored (lane : TraceInputPositionLane) (h : lane ≠ .rowPosition) :
      withRow (lanes lane) = before (lanes lane) :=
    setValue_other (fun e ↦ h (hLanes e)) ..
  have hMoreZero (lane : TraceInputPositionLane) (h : lane ≠ .rowPosition)
      (hInit : lane ∉ [.arity, .oldCount, .newCount, .certificateLength]) :
      withRow (lanes lane) = 0 := (hRestored lane h).trans (hZero lane hInit)
  have hBoth := runsValues_traceInputTracePositionsRegister lanes hLanes word withRow
    (hMoreZero _ (by simp) (by simp)) (hMoreZero _ (by simp) (by simp))
    (hMoreZero _ (by simp) (by simp)) (hMoreZero _ (by simp) (by simp))
  rw [hRestored .arity (by simp), hRestored .oldCount (by simp), hRestored .newCount (by simp)]
    at hBoth
  refine ⟨rowTicks + (30 * n + 10 * o + 20 * c + 50), ?_, after,
    hRow.seq hBoth, ?_⟩
  · change rowTicks ≤ 16 * L + 13 * n + 20 at hRowTime
    change _ ≤ traceInputPositionRegisterCost L n o c
    unfold traceInputPositionRegisterCost
    omega
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simp [after, withNew, withRow, row, new, old, setValue, hLane, L, n]
    · exact setValue_same ..
    · simp [after, withNew, new, old, setValue, hLane, n, c]
    · intro r hr ht
      exact (setValue_other (ht true) ..).trans
        ((setValue_other (ht false) ..).trans (setValue_other hr ..))

/-- Identify the three prepared positions and the preserved arity with the corresponding
input scan registers. -/
structure TraceInputPositionWiring (positions : TraceInputPositionLane → R)
    (scan : TraceInputLane → R) : Prop where
  arity : scan .arity = positions .arity
  rowPosition : scan .rowPosition = positions .rowPosition
  tracePosition : ∀ side, scan (.tracePosition side) = positions (.tracePosition side)

omit [DecidableEq R] in
theorem TraceInputPositionRegisterResult.traceInputSeed
    {positions : TraceInputPositionLane → R} {scan : TraceInputLane → R}
    (hLanes : Function.Injective positions) (hWiring : TraceInputPositionWiring positions scan)
    {before after : R → Nat} (hRun : TraceInputPositionRegisterResult positions before after)
    {cert : BinaryWord} {arity oldCount newCount : Nat}
    (hLayout : MergeTraceCertificateLayout arity oldCount newCount cert)
    (hArity : before (positions .arity) = arity)
    (hOld : before (positions .oldCount) = oldCount)
    (hNew : before (positions .newCount) = newCount)
    (hLength : before (positions .certificateLength) = cert.length) :
    TraceInputSeed scan cert arity oldCount after := by
  have hExtent : cert.length = arity + 1 + (arity + oldCount) + (arity + newCount) + 2 :=
    hLayout.length_eq
  refine ⟨?_, ?_, ?_⟩
  · rw [hWiring.arity, hRun.frame _ (fun e ↦ by cases hLanes e)
      (fun _ e ↦ by cases hLanes e), hArity]
  · rw [hWiring.rowPosition, hRun.row, hLength, hArity]
  · intro old
    rw [hWiring.tracePosition]
    cases old
    · rw [hRun.candidate, hArity, hNew]
      simp only [traceInputPosition, Bool.false_eq_true, ite_false,
        mergeTraceCertificateNewOffset, mergeTraceCertificateOldOffset]
      omega
    · rw [hRun.old, hArity, hOld, hNew]
      simp only [traceInputPosition, ite_true, mergeTraceCertificateOldOffset]
      omega

/-- A framed certificate bounds all four input magnitudes by its own length. -/
theorem traceInputPositionRegisterCost_le_of_layout {cert : BinaryWord}
    {arity oldCount newCount : Nat} (h : MergeTraceCertificateLayout arity oldCount newCount cert) :
    traceInputPositionRegisterCost cert.length arity oldCount newCount ≤ 89 * cert.length + 70 := by
  have hExtent : cert.length = arity + 1 + (arity + oldCount) + (arity + newCount) + 2 :=
    h.length_eq
  unfold traceInputPositionRegisterCost
  omega

end PvsNP.MCSP
