module

public import PvsNP.MCSP.TraceCertificateLayout
public import PvsNP.TuringMachine.Registers.StridedField

import all PvsNP.MCSP.CheckedDescriptionRegister

/-! # Compare the low row bits with both input-wire traces -/

public section

namespace PvsNP.MCSP

open Circuits RegisterMachine RegisterMachine.Fragment

variable {R : Type}

private def opposedTraceCompareIteration (lanes : Fin 6 → R) : Fragment R :=
  (compareIteration lanes).seq
    ((incrementBy (lanes 0) 3).seq (decrementLane (lanes 1)))

private def opposedTraceCompare (lanes : Fin 6 → R) : Fragment R :=
  countdown (lanes 2) (opposedTraceCompareIteration lanes)

private def opposedTraceCompareCost (length width : Nat) : Nat :=
  width * (14 * length + 22) + 1

variable [DecidableEq R]

private def opposedTraceCompareIterationValues (lanes : Fin 6 → R) (a b : Bool)
    (before : R → Nat) : R → Nat :=
  let compared := compareIterationValues lanes a b before
  decrementValues (lanes 1) (setValue (lanes 0) (compared (lanes 0) + 3) compared)

private theorem runsValues_opposedTraceCompareIteration (lanes : Fin 6 → R)
    (hLanes : Function.Injective lanes) (x : BinaryWord) (before : R → Nat) (a b : Bool)
    (hLeft : x.reverse[before (lanes 0)]? = some a)
    (hRight : x.reverse[before (lanes 1)]? = some b)
    (hIndex : before (lanes 3) = 0) (hWork : before (lanes 4) = 0)
    (hOld : before (lanes 5) ≤ 2) :
    ∃ ticks ≤ 14 * x.length + 21,
      (opposedTraceCompareIteration lanes).RunsValues x ticks before
        (opposedTraceCompareIterationValues lanes a b before) := by
  obtain ⟨ticks, hTicks, hRun⟩ := runsValues_compareIteration lanes hLanes x before a b
    hLeft hRight hIndex hWork hOld
  let compared := compareIterationValues lanes a b before
  let moved := setValue (lanes 0) (compared (lanes 0) + 3) compared
  exact ⟨ticks + (3 + 1), by omega, hRun.seq
    ((runsValues_incrementBy (lanes 0) 3 x compared).seq
      (runsValues_decrementLane (lanes 1) x moved))⟩

private theorem runsValues_opposedTraceCompare_words (lanes : Fin 6 → R)
    (hLanes : Function.Injective lanes) (x left right : BinaryWord) (before : R → Nat)
    (hLeftPos : 0 < before (lanes 0))
    (hWidth : left.length = right.length) (hCount : before (lanes 2) = left.length)
    (hIndex : before (lanes 3) = 0) (hWork : before (lanes 4) = 0)
    (hOrder : before (lanes 5) ≤ 2)
    (hLeft : ∀ i, i < left.length → x.reverse[before (lanes 0) + 2 * i]? = left[i]?)
    (hRight : ∀ i, i < right.length → x.reverse[before (lanes 1) - 2 * i]? = right[i]?) :
    ∃ ticks ≤ opposedTraceCompareCost x.length left.length, ∃ after : R → Nat,
      (opposedTraceCompare lanes).RunsValues x ticks before after ∧
      after (lanes 2) = 0 ∧ after (lanes 5) = compareLittleEndian (before (lanes 5)) left right ∧
      after (lanes 0) = before (lanes 0) + 2 * left.length ∧
      after (lanes 1) = before (lanes 1) - 2 * left.length ∧
      ∀ r, r ≠ lanes 0 → r ≠ lanes 1 → r ≠ lanes 2 → r ≠ lanes 5 → after r = before r := by
  have hLane (i j : Fin 6) : lanes i = lanes j ↔ i = j := ⟨fun e ↦ hLanes e, congrArg lanes⟩
  let loop := opposedTraceCompare lanes
  induction left generalizing right before with
  | nil =>
    have hNil : right = [] := List.length_eq_zero_iff.mp hWidth.symm
    subst right
    refine ⟨1, by simp [opposedTraceCompareCost], before, ?_, hCount, rfl,
      by simp, by simp, fun _ _ _ _ _ ↦ rfl⟩
    intro output
    exact run_countdown_zero (body := opposedTraceCompareIteration lanes)
      rfl hCount
  | cons a left ih =>
    cases right with
    | nil => simp at hWidth
    | cons b right =>
      have hSame : left.length = right.length := by
        simpa only [List.length_cons, Nat.add_right_cancel_iff] using hWidth
      let tested := decrementValues (lanes 2) before
      have hTestL : tested (lanes 0) = before (lanes 0) := by simp [tested, decrementValues, hLane]
      have hTestR : tested (lanes 1) = before (lanes 1) := by simp [tested, decrementValues, hLane]
      have hTestI : tested (lanes 3) = 0 := by simp [tested, decrementValues, hLane, hIndex]
      have hTestW : tested (lanes 4) = 0 := by simp [tested, decrementValues, hLane, hWork]
      have hTestO : tested (lanes 5) = before (lanes 5) := by simp [tested, decrementValues, hLane]
      have hThisL := hLeft 0 (by simp)
      have hThisR := hRight 0 (by simp)
      obtain ⟨bodyTicks, hBodyTicks, hBody⟩ := runsValues_opposedTraceCompareIteration
        lanes hLanes x tested a b
        (by simpa only [hTestL, Nat.mul_zero, Nat.add_zero, List.getElem?_cons_zero] using hThisL)
        (by simpa only [hTestR, Nat.mul_zero, Nat.sub_zero, List.getElem?_cons_zero] using hThisR)
        hTestI hTestW (hTestO.symm ▸ hOrder)
      let advanced := opposedTraceCompareIterationValues lanes a b tested
      have hNextL : advanced (lanes 0) = before (lanes 0) + 2 := by
        simp [advanced, opposedTraceCompareIterationValues, compareIterationValues, hTestL,
          decrementValues, setValue, hLane]
        omega
      have hNextR : advanced (lanes 1) = before (lanes 1) - 2 := by
        simp [advanced, opposedTraceCompareIterationValues, compareIterationValues, hTestR,
          decrementValues, setValue, hLane]
        omega
      have hNextCount : advanced (lanes 2) = left.length := by
        simp [advanced, opposedTraceCompareIterationValues, compareIterationValues, tested,
          decrementValues, setValue, hLane, hCount]
      have hNextI : advanced (lanes 3) = 0 := by
        simp [advanced, opposedTraceCompareIterationValues, compareIterationValues, hTestI,
          decrementValues, setValue, hLane]
      have hNextW : advanced (lanes 4) = 0 := by
        simp [advanced, opposedTraceCompareIterationValues, compareIterationValues, hTestW,
          decrementValues, setValue, hLane]
      have hNextO : advanced (lanes 5) = setOrdering (before (lanes 5)) a b := by
        simp [advanced, opposedTraceCompareIterationValues, compareIterationValues, hTestO,
          decrementValues, setValue, hLane]
      have hTailL (i : Nat) (hi : i < left.length) :
          x.reverse[advanced (lanes 0) + 2 * i]? = left[i]? := by
        rw [hNextL, show before (lanes 0) + 2 + 2 * i =
          before (lanes 0) + 2 * (i + 1) by omega]
        exact hLeft (i + 1) (by simpa using hi)
      have hTailR (i : Nat) (hi : i < right.length) :
          x.reverse[advanced (lanes 1) - 2 * i]? = right[i]? := by
        rw [hNextR, Nat.sub_sub, show 2 + 2 * i = 2 * (i + 1) by omega]
        exact hRight (i + 1) (by simpa using hi)
      obtain ⟨tailTicks, hTailTicks, after, hTail, hZero, hResult, hEndL, hEndR, hFrame⟩ :=
        ih right advanced (by rw [hNextL]; omega) hSame hNextCount hNextI hNextW
          (hNextO.symm ▸ setOrdering_le_two _ _ _ hOrder) hTailL hTailR
      refine ⟨1 + bodyTicks + tailTicks, ?_, after, ?_, hZero, ?_, ?_, ?_, ?_⟩
      · rw [opposedTraceCompareCost, List.length_cons, Nat.succ_mul]
        unfold opposedTraceCompareCost at hTailTicks
        omega
      · intro output
        let start := loop.enter (⟨none, before, none, output⟩ : Config R Unit)
        have hPos : 0 < before (lanes 2) := by rw [hCount]; simp
        have hStep := run_countdown_iteration (counter := lanes 2) (cfg := start)
          rfl hPos (hBody output) rfl
        let mid := loop.enter (⟨none, advanced, none, output⟩ : Config R Unit)
        change RegisterMachine.run loop.close x (1 + bodyTicks) start = some mid at hStep
        change RegisterMachine.run loop.close x _ start = _
        rw [RegisterMachine.run_add, hStep, Option.bind_some]
        exact hTail output
      · rw [hResult, hNextO, compareLittleEndian]
      · rw [hEndL, hNextL, List.length_cons, Nat.mul_succ]
        omega
      · rw [hEndR, hNextR, Nat.sub_sub, List.length_cons, Nat.mul_succ]
        omega
      · intro r hl hr hc ho
        rw [hFrame r hl hr hc ho]
        simp [advanced, opposedTraceCompareIterationValues, compareIterationValues, tested,
          decrementValues, setValue, hl, hr, hc, ho]

private theorem runsValues_opposedTraceCompare (lanes : Fin 6 → R)
    (hLanes : Function.Injective lanes) (x left right : BinaryWord) (before : R → Nat)
    (hLeftPos : 0 < before (lanes 0))
    (hWidth : left.length = right.length) (hCount : before (lanes 2) = left.length)
    (hIndex : before (lanes 3) = 0) (hWork : before (lanes 4) = 0)
    (hOrder : before (lanes 5) = 0)
    (hLeft : ∀ i, i < left.length → x.reverse[before (lanes 0) + 2 * i]? = left[i]?)
    (hRight : ∀ i, i < right.length → x.reverse[before (lanes 1) - 2 * i]? = right[i]?) :
    ∃ ticks ≤ opposedTraceCompareCost x.length left.length, ∃ after : R → Nat,
      (opposedTraceCompare lanes).RunsValues x ticks before after ∧
      after (lanes 2) = 0 ∧
      (after (lanes 5) = 0 ↔ left = right) ∧
      after (lanes 0) = before (lanes 0) + 2 * left.length ∧
      after (lanes 1) = before (lanes 1) - 2 * left.length ∧
      ∀ r, r ≠ lanes 0 → r ≠ lanes 1 → r ≠ lanes 2 → r ≠ lanes 5 → after r = before r := by
  obtain ⟨ticks, hTicks, after, hRun, hZero, hResult, hEndL, hEndR, hFrame⟩ :=
    runsValues_opposedTraceCompare_words lanes hLanes x left right before
      hLeftPos hWidth hCount hIndex hWork (by rw [hOrder]; decide) hLeft hRight
  rw [compareLittleEndian_eq _ _ _ hWidth, hOrder] at hResult
  refine ⟨ticks, hTicks, after, hRun, hZero, ?_, hEndL, hEndR, hFrame⟩
  rw [hResult, ← fieldValue_eq_iff_of_length hWidth]
  rcases lt_trichotomy (fieldValue left) (fieldValue right) with h | h | h
  · simp [h, ne_of_lt h]
  · simp [h]
  · simp [h, Nat.not_lt.mpr h.le, ne_of_gt h]

/-- The Boolean side is true for the old trace and false for the candidate trace. -/
inductive TraceInputLane where
  | arity
  | rowPosition
  | tracePosition (old : Bool)
  | rowCursor (old : Bool)
  | traceCursor (old : Bool)
  | remaining (old : Bool)
  | index (old : Bool)
  | scratch (old : Bool)
  | mismatch (old : Bool)
  | failures
  deriving DecidableEq

/-- The reverse address of the most significant low row bit. -/
@[expose] def traceInputRowPosition (certificateLength arity : Nat) : Nat :=
  2 * (certificateLength - 1 - (arity - 1))

/-- The reverse address of the first input bit of a trace. -/
@[expose] def traceInputPosition (certificateLength arity oldCount : Nat) (old : Bool) : Nat :=
  let offset := if old then mergeTraceCertificateOldOffset arity
    else mergeTraceCertificateNewOffset arity oldCount
  2 * (certificateLength - 1 - offset)

/-- The per-side comparator registers, including its two working cursors. -/
@[expose] def traceInputScanLanes (old : Bool) : Fin 6 → TraceInputLane :=
  ([.rowCursor old, .traceCursor old, .remaining old, .index old, .scratch old,
      .mismatch old] : List TraceInputLane).get

theorem traceInputScanLanes_injective (old : Bool) :
    Function.Injective (traceInputScanLanes old) := by
  cases old <;> decide

private theorem traceInputScanLanes_other {a b : Bool} (h : a ≠ b) (i j : Fin 6) :
    traceInputScanLanes a i ≠ traceInputScanLanes b j := by
  have hTF : ∀ i j : Fin 6, traceInputScanLanes true i ≠ traceInputScanLanes false j := by
    decide
  cases a <;> cases b
  · exact False.elim (h rfl)
  · exact (hTF j i).symm
  · exact hTF i j
  · exact False.elim (h rfl)

private theorem traceInputSeed_ne_scan (old : Bool) (i : Fin 6) :
    TraceInputLane.arity ≠ traceInputScanLanes old i ∧
    TraceInputLane.rowPosition ≠ traceInputScanLanes old i ∧
    (∀ side, TraceInputLane.tracePosition side ≠ traceInputScanLanes old i) ∧
    TraceInputLane.failures ≠ traceInputScanLanes old i := by
  have h : ∀ old : Bool, ∀ i : Fin 6,
    TraceInputLane.arity ≠ traceInputScanLanes old i ∧
    TraceInputLane.rowPosition ≠ traceInputScanLanes old i ∧
    (∀ side, TraceInputLane.tracePosition side ≠ traceInputScanLanes old i) ∧
    TraceInputLane.failures ≠ traceInputScanLanes old i := by decide
  exact h old i

/-- Addresses supplied by certificate layout preparation. The originals are preserved. -/
structure TraceInputSeed (lanes : TraceInputLane → R) (cert : BinaryWord)
    (arity oldCount : Nat) (before : R → Nat) : Prop where
  arityValue : before (lanes .arity) = arity
  rowPosition : before (lanes .rowPosition) = traceInputRowPosition cert.length arity
  tracePosition : ∀ old, before (lanes (.tracePosition old)) =
    traceInputPosition cert.length arity oldCount old

private def traceInputScan (lanes : TraceInputLane → R) (old : Bool) : Fragment R :=
  let reads := lanes ∘ traceInputScanLanes old
  let row := add (lanes .rowPosition) (reads 0) (reads 4)
  let trace := add (lanes (.tracePosition old)) (reads 1) (reads 4)
  let count := add (lanes .arity) (reads 2) (reads 4)
  ((row.seq trace).seq count).seq (opposedTraceCompare reads)

private def collectTraceInputFailures (lanes : TraceInputLane → R) : Fragment R :=
  (countNonzero (lanes (.mismatch true)) (lanes .failures)).seq
    (countNonzero (lanes (.mismatch false)) (lanes .failures))

/-- Compare both trace prefixes from their prepared reverse positions. -/
def traceInputRegister (lanes : TraceInputLane → R) : Fragment R :=
  ((traceInputScan lanes true).seq (traceInputScan lanes false)).seq
    (collectTraceInputFailures lanes)

private def traceInputScanCost (length arity : Nat) : Nat :=
  2 * (5 * length + 2) + (5 * arity + 2) + opposedTraceCompareCost length arity

/-- Bound the two scans and the constant-time check of their reports. -/
@[expose] def traceInputRegisterCost (length arity : Nat) : Nat :=
  2 * (2 * (5 * length + 2) + (5 * arity + 2) + (arity * (14 * length + 22) + 1)) + 6

theorem traceInputRegisterCost_polynomiallyBounded {length arity : Nat → Nat}
    (hLength : PolynomiallyBounded length) (hArity : PolynomiallyBounded arity) :
    PolynomiallyBounded (fun n ↦ traceInputRegisterCost (length n) (arity n)) := by
  let lit := PolynomiallyBounded.const
  have hAddresses := (lit 2).mul (((lit 5).mul hLength).add (lit 2))
  have hCount := ((lit 5).mul hArity).add (lit 2)
  have hRead := (hArity.mul (((lit 14).mul hLength).add (lit 22))).add (lit 1)
  exact ((lit 2).mul ((hAddresses.add hCount).add hRead)).add (lit 6)

private theorem runsValues_traceInputScan (lanes : TraceInputLane → R)
    (hLanes : Function.Injective lanes) (word expected traceBits : BinaryWord) (old : Bool)
    (v : R → Nat) (hWidth : expected.length = traceBits.length)
    (hArity : v (lanes .arity) = expected.length)
    (hRowPos : 0 < v (lanes .rowPosition)) (hRowBound : v (lanes .rowPosition) ≤ word.length)
    (hTraceBound : v (lanes (.tracePosition old)) ≤ word.length)
    (hZero : ∀ i, v (lanes (traceInputScanLanes old i)) = 0)
    (hRow : ∀ i, i < expected.length →
      word.reverse[v (lanes .rowPosition) + 2 * i]? = expected[i]?)
    (hTrace : ∀ i, i < traceBits.length →
      word.reverse[v (lanes (.tracePosition old)) - 2 * i]? = traceBits[i]?) :
    ∃ ticks ≤ traceInputScanCost word.length expected.length, ∃ after,
      (traceInputScan lanes old).RunsValues word ticks v after ∧
      (after (lanes (.mismatch old)) = 0 ↔ traceBits = expected) ∧
      ∀ r, (∀ i, r ≠ lanes (traceInputScanLanes old i)) → after r = v r := by
  let reads := lanes ∘ traceInputScanLanes old
  let row := lanes .rowPosition
  let firstTrace := lanes (.tracePosition old)
  let count := lanes .arity
  let rowPos := v row
  let tracePos := v firstTrace
  let v1 := setValue (reads 0) rowPos v
  let v2 := setValue (reads 1) tracePos v1
  let v3 := setValue (reads 2) expected.length v2
  have hReads : Function.Injective reads := hLanes.comp (traceInputScanLanes_injective old)
  have hNe (i j : Fin 6) (h : i ≠ j) : reads i ≠ reads j := fun e ↦ h (hReads e)
  have hRowNe (i : Fin 6) : row ≠ reads i :=
    fun e ↦ (traceInputSeed_ne_scan old i).2.1 (hLanes e)
  have hTraceNe (i : Fin 6) : firstTrace ≠ reads i :=
    fun e ↦ (traceInputSeed_ne_scan old i).2.2.1 old (hLanes e)
  have hCountNe (i : Fin 6) : count ≠ reads i :=
    fun e ↦ (traceInputSeed_ne_scan old i).1 (hLanes e)
  have h1 : (add row (reads 0) (reads 4)).RunsValues word (5 * rowPos + 2) v v1 := by
    have hInit : v (reads 0) = 0 := hZero 0
    simpa only [rowPos, v1, hInit, Nat.zero_add] using
      runsValues_add row (reads 0) (reads 4) word v (hRowNe 0) (hRowNe 4)
        (hNe 0 4 (by decide)) (hZero 4)
  have hv1 (r : R) (hr : r ≠ reads 0) : v1 r = v r := setValue_other hr ..
  have h2 : (add firstTrace (reads 1) (reads 4)).RunsValues word (5 * tracePos + 2) v1 v2 := by
    have hInit : v1 (reads 1) = 0 := (hv1 _ (hNe 1 0 (by decide))).trans (hZero 1)
    have hWork : v1 (reads 4) = 0 := (hv1 _ (hNe 4 0 (by decide))).trans (hZero 4)
    simpa only [hv1 firstTrace (hTraceNe 0), hInit, Nat.zero_add, v2, tracePos] using
      runsValues_add firstTrace (reads 1) (reads 4) word v1 (hTraceNe 1) (hTraceNe 4)
        (hNe 1 4 (by decide)) hWork
  have hv2 (r : R) (h1 : r ≠ reads 0) (h2 : r ≠ reads 1) : v2 r = v r :=
    (setValue_other h2 ..).trans (hv1 r h1)
  have h3 : (add count (reads 2) (reads 4)).RunsValues word (5 * expected.length + 2) v2 v3 := by
    have hInit : v2 (reads 2) = 0 :=
      (hv2 _ (hNe 2 0 (by decide)) (hNe 2 1 (by decide))).trans (hZero 2)
    have hWork : v2 (reads 4) = 0 :=
      (hv2 _ (hNe 4 0 (by decide)) (hNe 4 1 (by decide))).trans (hZero 4)
    have hArity' : v2 count = expected.length :=
      (hv2 count (hCountNe 0) (hCountNe 1)).trans hArity
    simpa only [hArity', hInit, Nat.zero_add, v3] using
      runsValues_add count (reads 2) (reads 4) word v2 (hCountNe 2) (hCountNe 4)
        (hNe 2 4 (by decide)) hWork
  have hv3 (r : R) (h0 : r ≠ reads 0) (h1 : r ≠ reads 1) (h2 : r ≠ reads 2) : v3 r = v r :=
    (setValue_other h2 ..).trans (hv2 r h0 h1)
  have hRow' : v3 (reads 0) = rowPos :=
    (setValue_other (hNe 0 2 (by decide)) ..).trans
      ((setValue_other (hNe 0 1 (by decide)) ..).trans (setValue_same ..))
  have hTrace' : v3 (reads 1) = tracePos :=
    (setValue_other (hNe 1 2 (by decide)) ..).trans (setValue_same ..)
  have hScanZero (i : Fin 6) (h0 : i ≠ 0) (h1 : i ≠ 1) (h2 : i ≠ 2) : v3 (reads i) = 0 :=
    (hv3 _ (hNe i 0 h0) (hNe i 1 h1) (hNe i 2 h2)).trans (hZero i)
  obtain ⟨ticks, hTicks, after, hCompare, _, hMatch, _, _, hFrame⟩ :=
    runsValues_opposedTraceCompare reads hReads word expected traceBits v3
      (by rwa [hRow']) hWidth (setValue_same ..)
      (hScanZero 3 (by decide) (by decide) (by decide))
      (hScanZero 4 (by decide) (by decide) (by decide))
      (hScanZero 5 (by decide) (by decide) (by decide))
      (by rwa [hRow']) (by rwa [hTrace'])
  refine ⟨_, ?_, after, ((h1.seq h2).seq h3).seq hCompare, ?_, ?_⟩
  · unfold traceInputScanCost
    change rowPos ≤ word.length at hRowBound
    change tracePos ≤ word.length at hTraceBound
    omega
  · exact hMatch.trans eq_comm
  · intro r h
    exact (hFrame r (h 0) (h 1) (h 2) (h 5)).trans (hv3 r (h 0) (h 1) (h 2))

private theorem runsValues_collectTraceInputFailures (lanes : TraceInputLane → R)
    (hLanes : Function.Injective lanes) (word : BinaryWord) (before : R → Nat)
    (hZero : before (lanes .failures) = 0) :
    let badOld := (decide (before (lanes (.mismatch true)) ≠ 0)).toNat
    let badNew := (decide (before (lanes (.mismatch false)) ≠ 0)).toNat
    ∃ ticks ≤ 6, (collectTraceInputFailures lanes).RunsValues word ticks before
      (setValue (lanes .failures) (badOld + badNew) before) := by
  let old := lanes (.mismatch true)
  let new := lanes (.mismatch false)
  let failures := lanes .failures
  let badOld := (decide (before old ≠ 0)).toNat
  let badNew := (decide (before new ≠ 0)).toNat
  let mid := setValue failures badOld before
  have hMid : (countNonzero old failures).RunsValues word (1 + 2 * badOld) before mid := by
    simpa only [hZero, Nat.zero_add, old, failures, badOld, mid] using
      runsValues_countNonzero old failures word before
  have hNew : mid new = before new := setValue_other (fun e ↦ by cases hLanes e) ..
  have hEnd : (countNonzero new failures).RunsValues word (1 + 2 * badNew) mid
      (setValue failures (badOld + badNew) before) := by
    simpa only [hNew, mid, setValue_same, setValue_replace, badNew] using
      runsValues_countNonzero new failures word mid
  have small (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide
  have hOld : badOld ≤ 1 := small _
  have hCandidate : badNew ≤ 1 := small _
  exact ⟨_, by omega, hMid.seq hEnd⟩

private def traceInputPrefix (arity oldCount newCount : Nat) (cert : BinaryWord)
    (old : Bool) : BinaryWord :=
  if old then (mergeTraceCertificateOldTrace arity oldCount cert).take arity
  else (mergeTraceCertificateNewTrace arity oldCount newCount cert).take arity

/-- The physical input comparison of both traces is exact on a framed certificate.
Only the comparator registers and the combined failure register may change. -/
theorem runsValues_traceInputRegister (lanes : TraceInputLane → R)
    (hLanes : Function.Injective lanes) (query : BinaryWord) {cert : BinaryWord}
    {arity oldCount newCount : Nat}
    (hLayout : MergeTraceCertificateLayout arity oldCount newCount cert)
    (before : R → Nat) (hSeed : TraceInputSeed lanes cert arity oldCount before)
    (hZero : ∀ old i, before (lanes (traceInputScanLanes old i)) = 0)
    (hFailures : before (lanes .failures) = 0) :
    let word := packedPair query cert
    ∃ ticks ≤ traceInputRegisterCost word.length arity, ∃ after,
      (traceInputRegister lanes).RunsValues word ticks before after ∧
      (after (lanes (.mismatch true)) = 0 ↔
        (mergeTraceCertificateOldTrace arity oldCount cert).take arity =
          mergeTraceCertificateInputBits arity cert) ∧
      (after (lanes (.mismatch false)) = 0 ↔
        (mergeTraceCertificateNewTrace arity oldCount newCount cert).take arity =
          mergeTraceCertificateInputBits arity cert) ∧
      (after (lanes .failures) = 0 ↔
        (mergeTraceCertificateOldTrace arity oldCount cert).take arity =
          mergeTraceCertificateInputBits arity cert ∧
        (mergeTraceCertificateNewTrace arity oldCount newCount cert).take arity =
          mergeTraceCertificateInputBits arity cert) ∧
      ∀ r, (∀ old i, r ≠ lanes (traceInputScanLanes old i)) → r ≠ lanes .failures →
        after r = before r := by
  let word := packedPair query cert
  let expected := mergeTraceCertificateInputBits arity cert
  let tracePrefix := traceInputPrefix arity oldCount newCount cert
  have hLen : cert.length = arity + 1 + (arity + oldCount) + (arity + newCount) + 2 :=
    hLayout.length_eq
  have hExpected : expected.length = arity := by
    unfold expected mergeTraceCertificateInputBits
    rw [List.length_reverse, List.length_take_of_le (by omega)]
  have hPrefix (old : Bool) : (tracePrefix old).length = arity := by
    cases old
    · change ((mergeTraceCertificateNewTrace arity oldCount newCount cert).take arity).length =
        arity
      rw [List.length_take_of_le (by rw [hLayout.split.2.2]; omega)]
    · change ((mergeTraceCertificateOldTrace arity oldCount cert).take arity).length = arity
      rw [List.length_take_of_le (by rw [hLayout.split.2.1]; omega)]
  have hRowPos : 0 < before (lanes .rowPosition) := by
    rw [hSeed.rowPosition, traceInputRowPosition]
    omega
  have hWordLength : word.length = 2 * (query.length + cert.length + 1) :=
    length_packedPair ..
  have hRowBound : before (lanes .rowPosition) ≤ word.length := by
    rw [hSeed.rowPosition, traceInputRowPosition, hWordLength]
    omega
  have hTraceBound (old : Bool) : before (lanes (.tracePosition old)) ≤ word.length := by
    rw [hSeed.tracePosition, traceInputPosition, hWordLength]
    omega
  have hRow (i : Nat) (hi : i < expected.length) :
      word.reverse[before (lanes .rowPosition) + 2 * i]? = expected[i]? := by
    have hi' : i < arity := hExpected ▸ hi
    have hPos : traceInputRowPosition cert.length arity + 2 * i =
        2 * (cert.length - 1 - (arity - 1 - i)) := by
      unfold traceInputRowPosition
      omega
    have hin : arity - 1 - i < cert.length := by omega
    rw [hSeed.rowPosition, hPos, getElem?_reverse_packedPair_certificate _ _ hin]
    exact (mergeTraceCertificateInputBits_getElem? hLayout hi').symm
  have hTrace (old : Bool) (i : Nat) (hi : i < (tracePrefix old).length) :
      word.reverse[before (lanes (.tracePosition old)) - 2 * i]? = (tracePrefix old)[i]? := by
    have hi' : i < arity := hPrefix old ▸ hi
    let offset := if old then mergeTraceCertificateOldOffset arity
      else mergeTraceCertificateNewOffset arity oldCount
    have hPos : traceInputPosition cert.length arity oldCount old - 2 * i =
        2 * (cert.length - 1 - (offset + i)) := by
      change 2 * (cert.length - 1 - offset) - 2 * i = _
      omega
    have hin : offset + i < cert.length := by
      cases old <;> simp [offset, mergeTraceCertificateOldOffset,
        mergeTraceCertificateNewOffset] <;> omega
    rw [hSeed.tracePosition, hPos, getElem?_reverse_packedPair_certificate _ _ hin]
    cases old
    · change cert[offset + i]? =
        ((mergeTraceCertificateNewTrace arity oldCount newCount cert).take arity)[i]?
      rw [List.getElem?_take_of_lt hi', mergeTraceCertificateNewTrace,
        List.getElem?_take_of_lt (by omega : i < arity + newCount), List.getElem?_drop]
      rfl
    · change cert[offset + i]? =
        ((mergeTraceCertificateOldTrace arity oldCount cert).take arity)[i]?
      rw [List.getElem?_take_of_lt hi', mergeTraceCertificateOldTrace,
        List.getElem?_take_of_lt (by omega : i < arity + oldCount), List.getElem?_drop]
      rfl
  have hWidth (old : Bool) : expected.length = (tracePrefix old).length :=
    hExpected.trans (hPrefix old).symm
  obtain ⟨oldTicks, hOldCost, withOld, hOldRun, hOld, hOldFrame⟩ :=
    runsValues_traceInputScan lanes hLanes word expected (tracePrefix true) true before
      (hWidth true)
      (hSeed.arityValue.trans hExpected.symm) hRowPos hRowBound (hTraceBound true) (hZero true)
      hRow (hTrace true)
  have hOldOther (i : Fin 6) : withOld (lanes (traceInputScanLanes false i)) =
      before (lanes (traceInputScanLanes false i)) :=
    hOldFrame _ (fun j e ↦ traceInputScanLanes_other (by decide : false ≠ true) i j (hLanes e))
  have hOldN : withOld (lanes .arity) = before (lanes .arity) :=
    hOldFrame _ (fun i e ↦ (traceInputSeed_ne_scan true i).1 (hLanes e))
  have hOldRow : withOld (lanes .rowPosition) = before (lanes .rowPosition) :=
    hOldFrame _ (fun i e ↦ (traceInputSeed_ne_scan true i).2.1 (hLanes e))
  have hOldNew : withOld (lanes (.tracePosition false)) = before (lanes (.tracePosition false)) :=
    hOldFrame _ (fun i e ↦ (traceInputSeed_ne_scan true i).2.2.1 false (hLanes e))
  obtain ⟨newTicks, hNewCost, both, hNewRun, hNew, hNewFrame⟩ :=
    runsValues_traceInputScan lanes hLanes word expected (tracePrefix false) false withOld
      (hWidth false)
      (hOldN.trans (hSeed.arityValue.trans hExpected.symm)) (hOldRow.symm ▸ hRowPos)
      (hOldRow.symm ▸ hRowBound) (hOldNew.symm ▸ hTraceBound false)
      (fun i ↦ (hOldOther i).trans (hZero false i))
      (by rw [hOldRow]; exact hRow) (by rw [hOldNew]; exact hTrace false)
  have hBothFrame (r : R) (h : ∀ old i, r ≠ lanes (traceInputScanLanes old i)) :
      both r = before r := (hNewFrame r (h false)).trans (hOldFrame r (h true))
  have hBothFailures : both (lanes .failures) = 0 :=
    (hBothFrame _ (fun old i e ↦ (traceInputSeed_ne_scan old i).2.2.2 (hLanes e))).trans hFailures
  obtain ⟨endTicks, hEndCost, hEndRun⟩ :=
    runsValues_collectTraceInputFailures lanes hLanes word both hBothFailures
  let badOld := (decide (both (lanes (.mismatch true)) ≠ 0)).toNat
  let badNew := (decide (both (lanes (.mismatch false)) ≠ 0)).toNat
  let after := setValue (lanes .failures) (badOld + badNew) both
  have hOldSame : both (lanes (.mismatch true)) = withOld (lanes (.mismatch true)) :=
    hNewFrame _ (fun i e ↦ traceInputScanLanes_other (by decide : true ≠ false) 5 i (hLanes e))
  have hFinishFrame (r : R) (h : r ≠ lanes .failures) : after r = both r :=
    setValue_other h ..
  have hBothOld : both (lanes (.mismatch true)) = 0 ↔ tracePrefix true = expected := by
    rw [hOldSame]
    exact hOld
  refine ⟨oldTicks + newTicks + endTicks, ?_, after, (hOldRun.seq hNewRun).seq hEndRun,
    ?_, ?_, ?_, ?_⟩
  · rw [hExpected] at hOldCost hNewCost
    change oldTicks + newTicks + endTicks ≤ traceInputRegisterCost word.length arity
    unfold traceInputRegisterCost
    unfold traceInputScanCost opposedTraceCompareCost at hOldCost hNewCost
    omega
  · rw [hFinishFrame _ (fun e ↦ by cases hLanes e)]
    exact hBothOld
  · rw [hFinishFrame _ (fun e ↦ by cases hLanes e)]
    exact hNew
  · change after (lanes .failures) = 0 ↔ tracePrefix true = expected ∧ tracePrefix false = expected
    rw [show after (lanes .failures) = badOld + badNew from setValue_same ..]
    simp [badOld, badNew, Nat.add_eq_zero_iff, hBothOld, hNew]
  · intro r h hf
    exact (hFinishFrame r hf).trans (hBothFrame r h)

end PvsNP.MCSP
