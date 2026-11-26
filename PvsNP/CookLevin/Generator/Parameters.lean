module

public import PvsNP.CookLevin.Generator.InputParameters
public import PvsNP.CookLevin.Generator.StrideParameter
public import PvsNP.TuringMachine.Registers.ValueRuns

/-! # Finite register initialization for tableau enumeration -/

@[expose] public section

namespace PvsNP.CookLevin

open RegisterMachine

variable {R : Type}

/-- Compute the clock horizon from the encoded input bound, then the window width. -/
def windowParameters (lanes : ParameterLane ↪ R) (d : Nat) : Fragment R :=
  let clock := Fragment.power (lanes .pairBound) (lanes .horizon) (lanes .work) (lanes .scratch) d
  let overhead := Fragment.incrementBy (lanes .horizon) d
  let coverage := Fragment.add (lanes .pairBound) (lanes .horizon) (lanes .scratch)
  let halfWidth := Fragment.add (lanes .horizon) (lanes .width) (lanes .scratch)
  let center := Fragment.incrementBy (lanes .width) 1
  (((((clock.seq overhead).seq coverage).seq halfWidth).seq halfWidth).seq center)

/-- Initialization finishes with all size parameters needed by the clause loops. -/
def parameterPrelude (lanes : ParameterLane ↪ R) (k d states symbols : Nat) : Fragment R :=
  ((inputParameters lanes k).seq (windowParameters lanes d)).seq
    (strideParameter (lanes .width) (lanes .stride) (lanes .work) (lanes .scratch) states symbols)

/-- Count the instructions before the stride is computed. -/
def windowParameterTime (n k d : Nat) : Nat :=
  let a := inputBound n k
  let t := horizon n k d
  1 + powerTailTime a 1 d + d + (5 * a + 2) + (5 * t + 2) + (5 * t + 2) + 1

/-- Exact number of register instructions in the complete prelude. -/
def parameterTime (n k d states symbols : Nat) : Nat :=
  inputParameterTime n k + windowParameterTime n k d +
    strideParameterTime (2 * horizon n k d + 1) states symbols

theorem parameterTime_polynomiallyBounded (k d states symbols : Nat) :
    PolynomiallyBounded (fun n ↦ parameterTime n k d states symbols) := by
  let lit := PolynomiallyBounded.const
  let len := PolynomiallyBounded.id
  have pairs : PolynomiallyBounded (fun n ↦ inputBound n k) := (len.add (lit 1)).add (len.pow k)
  have ticks := horizon_polynomiallyBounded k d
  have width := ((lit 2).mul ticks).add (lit 1)
  have addTime {f : Nat → Nat} (h : PolynomiallyBounded f) :
      PolynomiallyBounded (fun n ↦ 5 * f n + 2) := ((lit 5).mul h).add (lit 2)
  have power := powerTailTime_polynomiallyBounded pairs (lit 1) d
  have window := ((((((lit 1).add power).add (lit d)).add (addTime pairs)).add
    (addTime ticks)).add (addTime ticks)).add (lit 1)
  have stride := strideParameterTime_polynomiallyBounded width states symbols
  exact ((inputParameterTime_polynomiallyBounded k).add window).add stride

variable [DecidableEq R]

/-- The valuation after the clock and window width are initialized. -/
def windowParameterValues (lanes : ParameterLane ↪ R) (n k d : Nat) : R → Nat :=
  let t := horizon n k d
  setValue (lanes .width) (2 * t + 1) (setValue (lanes .horizon) t
    (inputParameterValues lanes n k))

/-- The full valuation. Each register outside the six parameters is still zero. -/
def parameterValues (lanes : ParameterLane ↪ R) (n k d states symbols : Nat) : R → Nat :=
  setValue (lanes .stride) (Tableau.atomStride states (2 * horizon n k d + 1) symbols)
    (windowParameterValues lanes n k d)

private theorem setValue_overwrite (r : R) (a b : Nat) (v : R → Nat) :
    setValue r b (setValue r a v) = setValue r b v := by
  funext s
  by_cases h : s = r <;> simp [setValue, h]

private theorem windowValues_run (lanes : ParameterLane ↪ R) (k d : Nat) (x : BinaryWord) :
    (windowParameters lanes d).RunsValues x (windowParameterTime x.length k d)
      (inputParameterValues lanes x.length k) (windowParameterValues lanes x.length k d) := by
  let a := inputBound x.length k
  let t := horizon x.length k d
  let A := lanes .pairBound
  let T := lanes .horizon
  let W := lanes .width
  let U := lanes .work
  let Z := lanes .scratch
  let v₀ := inputParameterValues lanes x.length k
  let v₁ := setValue T (a ^ d) v₀
  let v₂ := setValue T (a ^ d + d) v₀
  let v₃ := setValue T t v₀
  let v₄ := setValue W t v₃
  let v₅ := setValue W (2 * t) v₃
  let v₆ := setValue W (2 * t + 1) v₃
  have ne {i j : ParameterLane} (h : i ≠ j) : lanes i ≠ lanes j :=
    fun he ↦ h (lanes.injective he)
  have ha : v₀ A = a := by simp [v₀, A, a, inputParameterValues]
  have ht : v₀ T = 0 := by
    simp [v₀, T, inputParameterValues, setValue]
  have hu : v₀ U = 0 := by
    simp [v₀, U, inputParameterValues, setValue]
  have hz : v₀ Z = 0 := by
    simp [v₀, Z, inputParameterValues, setValue]
  have hw : v₀ W = 0 := by
    simp [v₀, W, inputParameterValues, setValue]
  have h₁ : (Fragment.power A T U Z d).RunsValues x (1 + powerTailTime a 1 d) v₀ v₁ := by
    simpa only [ha, v₁] using Fragment.runsValues_power A T U Z d x v₀
      (ne (by decide)) (ne (by decide)) (ne (by decide)) (ne (by decide)) (ne (by decide))
      (ne (by decide)) ht hu hz
  have h₂ : (Fragment.incrementBy T d).RunsValues x d v₁ v₂ := by
    simpa only [v₁, v₂, setValue_same, setValue_overwrite] using
      Fragment.runsValues_incrementBy T d x v₁
  have h₃ : (Fragment.add A T Z).RunsValues x (5 * a + 2) v₂ v₃ := by
    have hv : v₂ A = a := (setValue_other (ne (by decide) : A ≠ T) _ _).trans ha
    have hZero : v₂ Z = 0 := (setValue_other (ne (by decide) : Z ≠ T) _ _).trans hz
    simpa only [hv, v₂, v₃, setValue_same, setValue_overwrite, t, horizon] using
      Fragment.runsValues_add A T Z x v₂ (ne (by decide)) (ne (by decide)) (ne (by decide)) hZero
  have h₄ : (Fragment.add T W Z).RunsValues x (5 * t + 2) v₃ v₄ := by
    have hv : v₃ W = 0 := (setValue_other (ne (by decide) : W ≠ T) _ _).trans hw
    have hZero : v₃ Z = 0 := (setValue_other (ne (by decide) : Z ≠ T) _ _).trans hz
    simpa only [hv, v₃, v₄, setValue_same, Nat.zero_add] using
      Fragment.runsValues_add T W Z x v₃ (ne (by decide)) (ne (by decide)) (ne (by decide)) hZero
  have h₅ : (Fragment.add T W Z).RunsValues x (5 * t + 2) v₄ v₅ := by
    have hv : v₄ T = t := by simp [v₄, v₃, T, W, setValue]
    have hZero : v₄ Z = 0 :=
      (setValue_other (ne (by decide) : Z ≠ W) t v₃).trans
        ((setValue_other (ne (by decide) : Z ≠ T) t v₀).trans hz)
    simpa only [hv, v₄, v₅, setValue_same, setValue_overwrite, Nat.two_mul] using
      Fragment.runsValues_add T W Z x v₄ (ne (by decide)) (ne (by decide)) (ne (by decide)) hZero
  have h₆ : (Fragment.incrementBy W 1).RunsValues x 1 v₅ v₆ := by
    simpa only [v₅, v₆, setValue_same, setValue_overwrite] using
      Fragment.runsValues_incrementBy W 1 x v₅
  exact ((((h₁.seq h₂).seq h₃).seq h₄).seq h₅).seq h₆

private theorem strideValues_run (lanes : ParameterLane ↪ R) (k d states symbols : Nat)
    (x : BinaryWord) :
    (strideParameter (lanes .width) (lanes .stride) (lanes .work) (lanes .scratch)
      states symbols).RunsValues x
      (strideParameterTime (2 * horizon x.length k d + 1) states symbols)
      (windowParameterValues lanes x.length k d)
      (parameterValues lanes x.length k d states symbols) := by
  let v := windowParameterValues lanes x.length k d
  have ne {i j : ParameterLane} (h : i ≠ j) : lanes i ≠ lanes j :=
    fun he ↦ h (lanes.injective he)
  have hw : v (lanes .width) = 2 * horizon x.length k d + 1 := by
    simp [v, windowParameterValues]
  have hu : v (lanes .work) = 0 := by
    simp [v, windowParameterValues, inputParameterValues, setValue]
  have hs : v (lanes .stride) = 0 := by
    simp [v, windowParameterValues, inputParameterValues, setValue]
  have hz : v (lanes .scratch) = 0 := by
    simp [v, windowParameterValues, inputParameterValues, setValue]
  simpa only [hw, parameterValues, v] using
    runsValues_strideParameter (lanes .width) (lanes .stride) (lanes .work) (lanes .scratch)
      states symbols x v (ne (by decide)) (ne (by decide)) (ne (by decide)) (ne (by decide))
        (ne (by decide)) (ne (by decide)) hu hs hz

/-- The complete prelude starts with zero registers and computes the tableau parameters. -/
theorem run_parameterPrelude (lanes : ParameterLane ↪ R) (k d states symbols : Nat)
    (x : BinaryWord) :
    (parameterPrelude lanes k d states symbols).RunsValues x
      (parameterTime x.length k d states symbols)
      (fun _ ↦ 0) (parameterValues lanes x.length k d states symbols) :=
  ((runsValues_inputParameters lanes k x).seq (windowValues_run lanes k d x)).seq
    (strideValues_run lanes k d states symbols x)

/-- Read any of the named prelude registers after initialization. -/
theorem parameterValues_at (lanes : ParameterLane ↪ R) (n k d states symbols : Nat)
    (lane : ParameterLane) :
    parameterValues lanes n k d states symbols (lanes lane) =
      match lane with
      | .length => n
      | .capacity => n ^ k
      | .pairBound => inputBound n k
      | .horizon => horizon n k d
      | .width => 2 * horizon n k d + 1
      | .stride => Tableau.atomStride states (2 * horizon n k d + 1) symbols
      | .work | .scratch => 0 := by
  cases lane <;> simp [parameterValues, windowParameterValues, inputParameterValues, setValue]

/-- Buffers reserved for later clause loops remain zero. -/
theorem parameterValues_outside (lanes : ParameterLane ↪ R) (n k d states symbols : Nat)
    (r : R) (h : ∀ lane, r ≠ lanes lane) :
    parameterValues lanes n k d states symbols r = 0 := by
  simp [parameterValues, windowParameterValues, inputParameterValues, setValue, h]

end PvsNP.CookLevin
