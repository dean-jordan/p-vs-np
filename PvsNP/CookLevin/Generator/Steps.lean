module

public import PvsNP.CookLevin.Generator.StepSection

/-! # The complete transition section -/

@[expose] public section

namespace PvsNP.CookLevin

open RegisterMachine Fragment

variable {R : Type} (lanes : StepSectionLane ↪ R)

local notation "T" => lanes (StepSectionLane.parameter StepPreparationLane.time)
local notation "D" => lanes (StepSectionLane.parameter StepPreparationLane.stride)
local notation "W" => lanes (StepSectionLane.parameter StepPreparationLane.width)
local notation "S" => lanes (StepSectionLane.parameter StepPreparationLane.scratch)

/-- Copy the horizon and visit its transition times from the largest down to zero. -/
abbrev stepsFragment {states symbols certificates : Nat} (horizon : R)
    (table : FiniteTable states symbols certificates) : Fragment R :=
  (add horizon T S).seq (countdown T (stepSectionFragment lanes table))

/-- Charge each step the budget at the horizon. -/
def stepsTimeBound (states symbols width stride horizon : Nat) : Nat :=
  5 * horizon + 2 + (horizon * (stepTimeBound states symbols width stride horizon + 1) + 1)

theorem stepsTimeBound_polynomiallyBounded (states symbols : Nat)
    {width stride horizon : Nat → Nat} (hw : PolynomiallyBounded width)
    (hd : PolynomiallyBounded stride) (ht : PolynomiallyBounded horizon) :
    PolynomiallyBounded
      (fun n ↦ stepsTimeBound states symbols (width n) (stride n) (horizon n)) := by
  let lit := PolynomiallyBounded.const
  have copy := ((lit 5).mul ht).add (lit 2)
  have body := stepTimeBound_polynomiallyBounded states symbols hw hd ht
  exact copy.add ((ht.mul (body.add (lit 1))).add (lit 1))

/-- The transition loops emit exactly the indexed transition section and restore the valuation. -/
theorem run_stepsFragment [DecidableEq R] {states symbols certificates : Nat} (horizon : R)
    (table : FiniteTable states symbols certificates) (x suffix : BinaryWord) (v : R → Nat)
    (hHorizonFresh : ∀ lane, horizon ≠ lanes lane) (hTimeZero : v T = 0)
    (hStride : v D = Tableau.atomStride states (v W) symbols) (hReady : StepSectionReady lanes v) :
    ∃ cost ≤ stepsTimeBound states symbols (v W) (v D) (v horizon),
      (stepsFragment lanes horizon table).RunsOutput x cost v v suffix
        (table.transitionOutput (v W) (v horizon) suffix) := by
  let bound := stepTimeBound states symbols (v W) (v D) (v horizon)
  let update (out : BinaryWord) (t : Nat) :=
    table.foldStepClauses (emitIndexedClause (width := v W)) out t
  have hBody (t : Nat) (ht : t < v horizon) (out : BinaryWord) :
      ∃ cost ≤ bound, (stepSectionFragment lanes table).RunsOutput x cost
        (setValue T t v) (setValue T t v) out (update out t) := by
    let atTime := setValue T t v
    have hT : atTime T = t := setValue_same ..
    have hW : atTime W = v W := by simp [atTime, setValue]
    have hD : atTime D = v D := by simp [atTime, setValue]
    have hAtReady : StepSectionReady lanes atTime := by
      intro lane hNotTime hNotStride hNotWidth
      exact (setValue_other (lanes.injective.ne hNotTime) t v).trans
        (hReady lane hNotTime hNotStride hNotWidth)
    have hAtStride : atTime D = Tableau.atomStride states (atTime W) symbols := by
      rw [hD, hW, hStride]
    obtain ⟨cost, hCost, hRun⟩ := run_stepSectionFragment lanes table x out atTime
      hAtStride hAtReady
    rw [hW, hD, hT] at hCost
    refine ⟨cost, hCost.trans (stepTimeBound_mono_time states symbols (v W) (v D)
      (Nat.le_of_lt ht)), ?_⟩
    rw [hW, hT] at hRun
    exact hRun
  have hScratch : v S = 0 := hReady _ (by decide) (by decide) (by decide)
  have h := runsOutput_initializedCountdown horizon T S (stepSectionFragment lanes table)
    x v bound update (hHorizonFresh _) (hHorizonFresh _) (lanes.injective.ne (by decide))
    hTimeZero hScratch hBody suffix
  simpa only [FiniteTable.transitionOutput, Traversal.foldNatDesc_eq, update, stepsFragment,
    stepsTimeBound, bound] using h

end PvsNP.CookLevin
