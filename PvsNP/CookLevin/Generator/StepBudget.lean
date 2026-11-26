module

public import PvsNP.CookLevin.Generator.StepCopies
public import PvsNP.CookLevin.Generator.StepPreparation
public import PvsNP.CookLevin.Generator.StepUpdates

/-! # The uniform budget for one tableau transition -/

@[expose] public section

namespace PvsNP.CookLevin

open RegisterMachine.Fragment

/-- The sum bounds all six persistent name bases for a transition. -/
def stepBaseSum (states width stride time : Nat) : Nat :=
  let current := time * stride
  let next := (time + 1) * stride
  current + (current + states) + (current + states + width) +
    next + (next + states) + (next + states + width)

/-- Numeric form of the update leaf budget given an upper bound for its six bases. -/
def stepUpdateLeafTimeBoundNumeric (states symbols width base : Nat) : Nat :=
  let offset := stepUpdateOffsetBound states symbols width
  stepUpdatePrepareTimeBound states symbols width +
    (12 * offsetLiteralTime base offset + 6) + 5 * (offset + 1)

/-- Numeric budget for the update section with current and next row bases. -/
def stepUpdatesTimeBoundNumeric (states symbols width stride time : Nat) : Nat :=
  let leaf := stepUpdateLeafTimeBoundNumeric states symbols width
    (stepBaseSum states width stride time)
  states * ((5 * width + 2) + (width * (symbols * leaf + 1) + 1))

/-- The register-dependent budget is the numeric one at the initialized name bases. -/
theorem stepUpdatesTimeBound_eq_numeric {R : Type} (lanes : StepUpdateLane ↪ R) (v : R → Nat)
    {time states symbols width : Nat} (hBases : StepUpdateBases lanes v time states symbols width) :
    stepUpdatesTimeBound lanes states symbols v =
      stepUpdatesTimeBoundNumeric states symbols width (Tableau.atomStride states width symbols)
        time := by
  simp only [stepUpdatesTimeBound, stepUpdatesStateTimeBound, stepUpdateLeafTimeBound,
    stepUpdateBaseBound, stepUpdatesTimeBoundNumeric, stepUpdateLeafTimeBoundNumeric, stepBaseSum,
    hBases.width, hBases.state, hBases.head, hBases.cell, hBases.nextState, hBases.nextHead,
    hBases.nextCell]

/-- Preparation, copy clauses, update clauses, and cleanup for one step. -/
def stepTimeBound (states symbols width stride time : Nat) : Nat :=
  let current := time * stride
  let next := (time + 1) * stride
  stepPreparationTime time stride width states +
    stepCopiesTimeBound width symbols (current + states) (current + states + width)
      (next + states + width) +
    stepUpdatesTimeBoundNumeric states symbols width stride time +
    stepCleanupTime time stride width states

private theorem initializedCopyTimeBound_mono_body (width : Nat) {body upper : Nat}
    (h : body ≤ upper) : initializedCopyTimeBound width body ≤
      initializedCopyTimeBound width upper :=
  Nat.add_le_add_left (Nat.add_le_add_right
    (Nat.mul_le_mul_left width (Nat.add_le_add_right h 1)) 1) _

private theorem stepCopiesTimeBound_mono_bases (width symbols : Nat)
    {head cell nextCell headUpper cellUpper nextUpper : Nat}
    (hHead : head ≤ headUpper) (hCell : cell ≤ cellUpper) (hNext : nextCell ≤ nextUpper) :
    stepCopiesTimeBound width symbols head cell nextCell ≤
      stepCopiesTimeBound width symbols headUpper cellUpper nextUpper := by
  have hLeaf : copyAtTimeBound width symbols head cell nextCell ≤
      copyAtTimeBound width symbols headUpper cellUpper nextUpper := by
    simp only [copyAtTimeBound, offsetLiteralTime]
    omega
  have hSymbols : copySymbolsTimeBound width symbols head cell nextCell ≤
      copySymbolsTimeBound width symbols headUpper cellUpper nextUpper :=
    Nat.add_le_add_left (Nat.add_le_add_right
      (Nat.mul_le_mul_left symbols (Nat.add_le_add_right hLeaf 1)) 1) _
  exact initializedCopyTimeBound_mono_body width (initializedCopyTimeBound_mono_body width hSymbols)

private theorem stepUpdatesTimeBoundNumeric_mono_time (states symbols width stride : Nat)
    {time upper : Nat} (h : time ≤ upper) :
    stepUpdatesTimeBoundNumeric states symbols width stride time ≤
      stepUpdatesTimeBoundNumeric states symbols width stride upper := by
  have hCurrent := Nat.mul_le_mul_right stride h
  have hNext := Nat.mul_le_mul_right stride (Nat.add_le_add_right h 1)
  have hBase : stepBaseSum states width stride time ≤ stepBaseSum states width stride upper := by
    simp only [stepBaseSum]
    omega
  have hLeaf : stepUpdateLeafTimeBoundNumeric states symbols width
        (stepBaseSum states width stride time) ≤
      stepUpdateLeafTimeBoundNumeric states symbols width
        (stepBaseSum states width stride upper) := by
    simp only [stepUpdateLeafTimeBoundNumeric, offsetLiteralTime]
    omega
  exact Nat.mul_le_mul_left states (Nat.add_le_add_left (Nat.add_le_add_right
    (Nat.mul_le_mul_left width (Nat.add_le_add_right (Nat.mul_le_mul_left symbols hLeaf) 1)) 1) _)

/-- The time-step budget can be evaluated at the horizon for a uniform bound. -/
theorem stepTimeBound_mono_time (states symbols width stride : Nat) {time upper : Nat}
    (h : time ≤ upper) :
    stepTimeBound states symbols width stride time ≤
      stepTimeBound states symbols width stride upper := by
  have hCurrent := Nat.mul_le_mul_right stride h
  have hNext := Nat.mul_le_mul_right stride (Nat.add_le_add_right h 1)
  have hHead := Nat.add_le_add_right hCurrent states
  have hCell := Nat.add_le_add_right hHead width
  have hNextCell := Nat.add_le_add_right (Nat.add_le_add_right hNext states) width
  have hCopy := stepCopiesTimeBound_mono_bases width symbols hHead hCell hNextCell
  have hUpdate := stepUpdatesTimeBoundNumeric_mono_time states symbols width stride h
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add (stepPreparationTime_mono_time stride width states h)
      hCopy) hUpdate) (stepCleanupTime_mono_time stride width states h)

private theorem stepUpdateLeafTimeBoundNumeric_polynomiallyBounded (states symbols : Nat)
    {width base : Nat → Nat} (hWidth : PolynomiallyBounded width)
    (hBase : PolynomiallyBounded base) :
    PolynomiallyBounded (fun n ↦
      stepUpdateLeafTimeBoundNumeric states symbols (width n) (base n)) := by
  let lit := PolynomiallyBounded.const
  have hOffset := (((((lit states).add ((lit symbols).mul hWidth)).add (lit symbols)).add
    hWidth).add (lit 1))
  have hCopy := ((lit 5).mul hWidth).add (lit 2)
  have hCompare := ((lit 6).mul ((hWidth.add (lit 1)).add hWidth)).add (lit 6)
  have hMove := (lit 1).add (hCompare.add (lit 1))
  have hAffine := affineTime_polynomiallyBounded symbols symbols hWidth
  have hPrep := ((((((lit states).add (lit states)).add hAffine).add hAffine).add hCopy).add hMove)
  have hEmit := ((lit 12).mul (offsetLiteralTime_polynomiallyBounded hBase hOffset)).add (lit 6)
  exact (hPrep.add hEmit).add ((lit 5).mul (hOffset.add (lit 1)))

/-- The uniform step budget is polynomial in the width, stride, and time. -/
theorem stepTimeBound_polynomiallyBounded (states symbols : Nat)
    {width stride time : Nat → Nat} (hWidth : PolynomiallyBounded width)
    (hStride : PolynomiallyBounded stride) (hTime : PolynomiallyBounded time) :
    PolynomiallyBounded (fun n ↦ stepTimeBound states symbols (width n) (stride n) (time n)) := by
  let lit := PolynomiallyBounded.const
  have hCurrent := hTime.mul hStride
  have hNext := (hTime.add (lit 1)).mul hStride
  have hHead := hCurrent.add (lit states)
  have hCell := hHead.add hWidth
  have hNextHead := hNext.add (lit states)
  have hNextCell := hNextHead.add hWidth
  have hBase := ((((hCurrent.add hHead).add hCell).add hNext).add hNextHead).add hNextCell
  have hLeaf := stepUpdateLeafTimeBoundNumeric_polynomiallyBounded states symbols hWidth hBase
  have hUpdate := (lit states).mul (((((lit 5).mul hWidth).add (lit 2)).add
    ((hWidth.mul (((lit symbols).mul hLeaf).add (lit 1))).add (lit 1))))
  have hPrep := stepPreparationTime_polynomiallyBounded hTime hStride hWidth states
  have hCopy := stepCopiesTimeBound_polynomiallyBounded hWidth hHead hCell hNextCell symbols
  have hCleanup := stepCleanupTime_polynomiallyBounded hTime hStride hWidth states
  exact ((hPrep.add hCopy).add hUpdate).add hCleanup

end PvsNP.CookLevin
