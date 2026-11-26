module

public import PvsNP.CookLevin.Generator.Row

/-! # Countdown traversal for all tableau rows -/

@[expose] public section

namespace PvsNP.CookLevin

open RegisterMachine RegisterMachine.Fragment

/-- Prepend all row constraints, visiting the horizon row first and row zero last. -/
def tableauRowsOutput (states symbols width stride horizon : Nat) (suffix : BinaryWord) :
    BinaryWord :=
  (List.range (horizon + 1)).reverse.foldl
    (fun acc t ↦ tableauRowOutput states symbols width stride t acc) suffix

/-- The numeric row loop matches the indexed and named row traversal. -/
theorem tableauRowsOutput_eq (states symbols width stride horizon : Nat) (suffix : BinaryWord)
    (hStride : stride = Tableau.atomStride states width symbols) :
    tableauRowsOutput states symbols width stride horizon suffix =
      Traversal.foldNatDesc (fun acc t ↦ FiniteTable.foldRowClauses
        (fun out (clause : CNF.Clause (Tableau.Atom (Fin states) (Fin symbols) width)) ↦
          true :: (CNFCode.encodeClause (clause.map (CNF.Literal.map indexedAtomName)) ++ out))
        acc t) suffix (horizon + 1) := by
  rw [Traversal.foldNatDesc_eq]
  simp only [tableauRowsOutput, tableauRowOutput_eq states symbols width stride _ _ hStride]

variable {R : Type} (lanes : RowLane ↪ R)

local notation "T" => lanes RowLane.time
local notation "D" => lanes RowLane.stride
local notation "W" => lanes RowLane.width
local notation "P" => lanes RowLane.position
local notation "A" => lanes RowLane.preparationScratch

/-- Initialize the countdown from the persistent horizon and emit every row. -/
def rowsFragment (horizon : R) (states symbols : Nat) : Fragment R :=
  ((add horizon T A).seq (incrementBy T 1)).seq (countdown T (rowFragment lanes states symbols))

variable [DecidableEq R]

/-- Budget for the initial copy and the countdown at a uniform row cost. -/
def rowsTimeBound (horizon : R) (v : R → Nat) (states symbols : Nat) : Nat :=
  (5 * v horizon + 2) + 1 +
    ((v horizon + 1) * (rowTimeBound lanes (setValue T (v horizon) v) states symbols + 1) + 1)

private theorem readyAtTime (v : R → Nat) (t : Nat) (hReady : RowReady lanes v) :
    RowReady lanes (setValue T t v) := by
  have fixed (lane : RowPreparationLane) (hNe : rowPreparationCode lane ≠ .time) :
      setValue T t v (rowPreparationLanes lanes lane) = v (rowPreparationLanes lanes lane) :=
    setValue_other (lanes.injective.ne hNe) t v
  have fieldFixed (lane : ExactlyOneLane) :
      setValue T t v (rowFieldLanes lanes lane) = v (rowFieldLanes lanes lane) :=
    setValue_other (lanes.injective.ne (show RowLane.field lane ≠ .time from fun eq ↦ by
      cases eq)) t v
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact (fixed .base (by decide)).trans hReady.prepare.base
  · exact (fixed .count (by decide)).trans hReady.prepare.count
  · exact (fixed .multiplier (by decide)).trans hReady.prepare.multiplier
  · exact (fixed .scratch (by decide)).trans hReady.prepare.scratch
  · simpa only [ExactlyOneScratchZero, fieldFixed] using hReady.work
  · exact (fieldFixed .left).trans hReady.left
  · exact (fieldFixed .right).trans hReady.right

private theorem preparedFieldTimeBound_mono_pair {prepCost prepUpper base baseUpper count : Nat}
    (hPrep : prepCost ≤ prepUpper) (hBase : base ≤ baseUpper) :
    preparedFieldTimeBound prepCost base count ≤ preparedFieldTimeBound prepUpper baseUpper count :=
  Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add (Nat.add_le_add hPrep (exactlyOneFieldTimeBound_mono hBase (Nat.le_refl _)))
      hBase) _) _

/-- With width and stride fixed, the row budget grows monotonically in the row time. -/
theorem rowTimeBound_mono_time (v : R → Nat) (states symbols : Nat)
    {t upper : Nat} (hTime : t ≤ upper) :
    rowTimeBound lanes (setValue T t v) states symbols ≤
      rowTimeBound lanes (setValue T upper v) states symbols := by
  let nameTime (t : Nat) := accumulateNameTime t (v D) + states
  let widthTime := 5 * v W + 2
  let cellPrep (t : Nat) :=
    nameTime t + widthTime + symbols + (symbols * (5 * v W + 3) + 1) + symbols
  let cellBase (t : Nat) := t * v D + states + v W + v W * symbols
  have hName : nameTime t ≤ nameTime upper := by
    unfold nameTime accumulateNameTime
    have hCopy := Nat.mul_le_mul_left 5 hTime
    have hProduct := Nat.mul_le_mul_right (5 * v D + 3) hTime
    omega
  have hBase := Nat.mul_le_mul_right (v D) hTime
  have hState := preparedFieldTimeBound_mono_pair (count := states) hName hBase
  have hHead := preparedFieldTimeBound_mono_pair (count := v W)
    (Nat.add_le_add_right hName widthTime) (Nat.add_le_add_right hBase states)
  have hCellPrep : cellPrep t ≤ cellPrep upper := by unfold cellPrep; omega
  have hCellBase : cellBase t ≤ cellBase upper := by unfold cellBase; omega
  have hCell := preparedFieldTimeBound_mono_pair (count := symbols) hCellPrep hCellBase
  have hRows := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left
    (Nat.add_le_add_right (Nat.mul_le_mul_left (v W) (Nat.add_le_add_right hCell 1)) 1)
    widthTime) hHead) hState
  simpa [rowTimeBound, rowCellFieldTimeBound, RowPreparationLanes.cellTime,
    RowPreparationLanes.headTime, RowPreparationLanes.stateTime, rowPreparationLanes,
    rowPreparationCode, setValue, lanes.injective.eq_iff, nameTime, widthTime, cellPrep, cellBase]
    using hRows

/-- The finite row loop preserves the whole valuation and emits all rows within its budget. -/
theorem run_rowsFragment (horizon : R) (states symbols : Nat) (x suffix : BinaryWord)
    (v : R → Nat) (hHorizon : ∀ lane, horizon ≠ lanes lane)
    (hTime : v T = 0) (hReady : RowReady lanes v) (hPosition : v P = 0) :
    ∃ cost ≤ rowsTimeBound lanes horizon v states symbols,
      (rowsFragment lanes horizon states symbols).RunsOutput x cost v v suffix
        (tableauRowsOutput states symbols (v W) (v D) (v horizon) suffix) := by
  let copied := setValue T (v horizon) v
  let initialized := setValue T (v horizon + 1) v
  let rowBudget := rowTimeBound lanes copied states symbols
  let rowOutput (out : BinaryWord) (i : Nat) :=
    tableauRowOutput states symbols (v W) (v D) i out
  have hCopy : (add horizon T A).RunsValues x (5 * v horizon + 2) v copied := by
    simpa only [copied, hTime, Nat.zero_add] using
      runsValues_add horizon T A x v (hHorizon .time) (hHorizon .preparationScratch)
        (lanes.injective.ne (by decide)) hReady.prepare.scratch
  have hInc : (incrementBy T 1).RunsValues x 1 copied initialized := by
    simpa only [copied, initialized, setValue_same, setValue_replace] using
      runsValues_incrementBy T 1 x copied
  have hInitialize := (hCopy.seq hInc).withOutput suffix
  have hInitial : initialized T = v horizon + 1 := setValue_same ..
  have hBody (i : Nat) (hi : i < initialized T) (out : BinaryWord) :
      ∃ cost ≤ rowBudget,
        (rowFragment lanes states symbols).RunsOutput x cost (setValue T i initialized)
          (setValue T i initialized) out (rowOutput out i) := by
    let current := setValue T i v
    have hCurrentPosition : current P = 0 :=
      (setValue_other (lanes.injective.ne (by decide)) ..).trans hPosition
    obtain ⟨cost, hCost, hRun⟩ := run_rowFragment lanes states symbols x out current
      (readyAtTime lanes v i hReady) hCurrentPosition
    have hLimit : i ≤ v horizon := by rw [hInitial] at hi; omega
    have hWidth : current W = v W := setValue_other (lanes.injective.ne (by decide)) ..
    have hStride : current D = v D := setValue_other (lanes.injective.ne (by decide)) ..
    have hCurrent : current T = i := setValue_same ..
    rw [hWidth, hStride, hCurrent] at hRun
    refine ⟨cost, hCost.trans (rowTimeBound_mono_time lanes v states symbols hLimit), ?_⟩
    simpa only [initialized, setValue_replace, rowOutput] using hRun
  obtain ⟨cost, hCost, hRun⟩ := runsOutput_countdown T (rowFragment lanes states symbols)
    x initialized rowBudget rowOutput hBody suffix
  have hClear : setValue T 0 initialized = v := by
    simpa only [initialized, setValue_replace, hTime] using setValue_current T v
  rw [hInitial] at hCost
  rw [hClear, hInitial] at hRun
  exact ⟨_, Nat.add_le_add_left hCost _, hInitialize.seq hRun⟩

/-- The row-loop budget is polynomial in the persistent dimensions. -/
theorem rowsTimeBound_polynomiallyBounded (horizon : R) (states symbols : Nat)
    {v : Nat → R → Nat} (hHorizon : PolynomiallyBounded (fun n ↦ v n horizon))
    (hStride : PolynomiallyBounded (fun n ↦ v n D))
    (hWidth : PolynomiallyBounded (fun n ↦ v n W)) :
    PolynomiallyBounded (fun n ↦ rowsTimeBound lanes horizon (v n) states symbols) := by
  let lit := PolynomiallyBounded.const
  let atHorizon (n : Nat) := setValue T (v n horizon) (v n)
  have ht : PolynomiallyBounded (fun n ↦ atHorizon n T) := by
    simpa only [atHorizon, setValue_same] using hHorizon
  have hd : PolynomiallyBounded (fun n ↦ atHorizon n D) := by
    simpa [atHorizon, setValue, lanes.injective.eq_iff] using hStride
  have hw : PolynomiallyBounded (fun n ↦ atHorizon n W) := by
    simpa [atHorizon, setValue, lanes.injective.eq_iff] using hWidth
  have hRow := rowTimeBound_polynomiallyBounded lanes ht hd hw states symbols
  have hInit := (((lit 5).mul hHorizon).add (lit 2)).add (lit 1)
  exact hInit.add (((hHorizon.add (lit 1)).mul (hRow.add (lit 1))).add (lit 1))

end PvsNP.CookLevin
