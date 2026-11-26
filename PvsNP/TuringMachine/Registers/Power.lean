module

public import PvsNP.Complexity.TimeBounds
public import PvsNP.TuringMachine.Registers.Fragments
public import PvsNP.TuringMachine.Registers.Move
public import PvsNP.TuringMachine.Registers.Multiply

public import Mathlib.Basic.Finite.Prod

/-! # A finite register program for a fixed power

The exponent determines the number of control blocks. Each block consumes
the current result while multiplying it by the base, then moves the product
back into the result register. The base and scratch registers are preserved.
-/

@[expose] public section

namespace PvsNP.RegisterMachine

/-- The running phases of one multiplication and transfer. -/
inductive PowerPhase where
  | multiply | takeAdd | addTarget | addScratch | restore | addSource | move | moveOne

private def powerPhaseCode : PowerPhase → Fin 8
  | .multiply => 0
  | .takeAdd => 1
  | .addTarget => 2
  | .addScratch => 3
  | .restore => 4
  | .addSource => 5
  | .move => 6
  | .moveOne => 7

instance : Finite PowerPhase :=
  Finite.of_injective powerPhaseCode (by
    intro a b h
    cases a <;> cases b <;> simp_all [powerPhaseCode])

/-- An initialization label and eight labels for each multiplication. -/
abbrev PowerLabel (exponent : Nat) := Fin 1 ⊕ (Fin exponent × PowerPhase)

variable {R : Type}

/-- Enter the indexed multiplication block or exit if all blocks have run. -/
def powerStage (exponent i : Nat) : Option (PowerLabel exponent) :=
  if h : i < exponent then some (.inr (⟨i, h⟩, .multiply)) else none

/-- The code of the fixed-power block; `none` is a normal exit. -/
def powerCode (base result accumulator scratch : R) (exponent : Nat) :
    PowerLabel exponent → Instruction R (Option (PowerLabel exponent))
  | .inl _ => .inc result (powerStage exponent 0)
  | .inr (i, phase) =>
    let here (p : PowerPhase) := some (.inr (i, p))
    match phase with
    | .multiply => .dec result (here .move) (here .takeAdd)
    | .takeAdd => .dec base (here .restore) (here .addTarget)
    | .addTarget => .inc accumulator (here .addScratch)
    | .addScratch => .inc scratch (here .takeAdd)
    | .restore => .dec scratch (here .multiply) (here .addSource)
    | .addSource => .inc base (here .restore)
    | .move => .dec accumulator (powerStage exponent (i.val + 1)) (here .moveOne)
    | .moveOne => .inc result (here .move)

/-- The power block can be linked to another fragment at its normal exit. -/
abbrev Fragment.power (base result accumulator scratch : R) (exponent : Nat) : Fragment R where
  Label := PowerLabel exponent
  finiteLabel := inferInstanceAs (Finite (Fin 1 ⊕ (Fin exponent × PowerPhase)))
  entry := some (.inl 0)
  code := powerCode base result accumulator scratch exponent

/-- Cost of the remaining multiplication blocks when the current result is `value`. -/
def powerTailTime (base value : Nat) : Nat → Nat
  | 0 => 0
  | exponent + 1 => value * (7 * base + 3) + 2 + powerTailTime base (value * base) exponent

/-- The cost is polynomial when the exponent is fixed and the initial values are polynomial. -/
theorem powerTailTime_polynomiallyBounded {base value : Nat → Nat}
    (hBase : PolynomiallyBounded base) (hValue : PolynomiallyBounded value) (exponent : Nat) :
    PolynomiallyBounded (fun n ↦ powerTailTime (base n) (value n) exponent) := by
  induction exponent generalizing value with
  | zero => exact PolynomiallyBounded.const 0
  | succ exponent ih =>
    exact ((hValue.mul (((PolynomiallyBounded.const 7).mul hBase).add
      (PolynomiallyBounded.const 3))).add (PolynomiallyBounded.const 2)).add
        (ih (hValue.mul hBase))

variable [DecidableEq R]

/-- Replace the value of one register while preserving all others. -/
def setValue (reg : R) (value : Nat) (values : R → Nat) : R → Nat :=
  fun r ↦ if r = reg then value else values r

@[simp] theorem setValue_same (reg : R) (value : Nat) (values : R → Nat) :
    setValue reg value values reg = value := by simp [setValue]

theorem setValue_other {reg r : R} (h : r ≠ reg) (value : Nat) (values : R → Nat) :
    setValue reg value values r = values r := by simp [setValue, h]

variable {base result accumulator scratch : R} {exponent : Nat}

local notation "P" => Fragment.close (Fragment.power base result accumulator scratch exponent)

private def stageMultiply (i : Fin exponent) :
    MultiplyRules P result base accumulator scratch where
  entry := some (.inr (i, .multiply))
  next := some (.inr (i, .move))
  add := {
    entry := some (.inr (i, .takeAdd))
    addTarget := some (.inr (i, .addTarget))
    addScratch := some (.inr (i, .addScratch))
    restore := some (.inr (i, .restore))
    addSource := some (.inr (i, .addSource))
    next := some (.inr (i, .multiply))
    takeSource := rfl
    writeTarget := rfl
    writeScratch := rfl
    takeScratch := rfl
    writeSource := rfl }
  takeMultiplier := rfl
  addReturns := rfl

private def stageMove (i : Fin exponent) : MoveRules P accumulator result where
  entry := some (.inr (i, .move))
  write := some (.inr (i, .moveOne))
  next := powerStage exponent (i.val + 1)
  takeSource := rfl
  writeTarget := rfl

variable (x : BinaryWord)
  (hRB : result ≠ base) (hRA : result ≠ accumulator) (hRS : result ≠ scratch)
  (hBA : base ≠ accumulator) (hBS : base ≠ scratch) (hAS : accumulator ≠ scratch)

include hRB hRA hRS hBA hBS hAS in
private theorem run_stage (i : Fin exponent) {cfg : Config R (Option (PowerLabel exponent))}
    (hPC : cfg.pc = some (some (.inr (i, .multiply))))
    (hAcc : cfg.values accumulator = 0) (hScratch : cfg.values scratch = 0) :
    run P x (cfg.values result * (7 * cfg.values base + 3) + 2) cfg = some
      { cfg with
        pc := some (powerStage exponent (i.val + 1))
        values := setValue result (cfg.values result * cfg.values base) cfg.values } := by
  let mid : Config R (Option (PowerLabel exponent)) := { cfg with
    pc := some (some (.inr (i, .move)))
    values := multiplyValues result base accumulator cfg.values }
  have hMultiply : run P x (cfg.values result * (5 * cfg.values base + 3) + 1) cfg = some mid :=
    run_multiply (stageMultiply i) x hRB hRA hRS hBA hBS hAS hPC hScratch
  have hMidAccum : mid.values accumulator = cfg.values result * cfg.values base := by
    simp [mid, multiplyValues, hRA.symm, hAcc]
  have hMidZero : mid.values result = 0 := by simp [mid, multiplyValues]
  have hMove := run_move (stageMove (base := base) (scratch := scratch) i) x hRA.symm
    (cfg := mid) rfl
  rw [hMidAccum] at hMove
  have hValues : moveValues accumulator result mid.values =
      setValue result (cfg.values result * cfg.values base) cfg.values := by
    funext r
    by_cases hResult : r = result
    · subst r
      simp only [moveValues, ite_eq_right hRA, ite_true, hMidZero, hMidAccum, Nat.zero_add,
        setValue_same]
    by_cases hAccum : r = accumulator
    · subst r
      simp [moveValues, setValue, hResult, hAcc]
    simp [moveValues, setValue, mid, multiplyValues, hResult, hAccum]
  have hTime : cfg.values result * (7 * cfg.values base + 3) + 2 =
      (cfg.values result * (5 * cfg.values base + 3) + 1) +
        (2 * (cfg.values result * cfg.values base) + 1) := by
    rw [show 7 * cfg.values base + 3 = (5 * cfg.values base + 3) + 2 * cfg.values base by omega,
      Nat.mul_add, ← Nat.mul_assoc (cfg.values result) 2, Nat.mul_comm (cfg.values result) 2,
      Nat.mul_assoc]
    omega
  rw [hTime, run_add, hMultiply, Option.bind_some, hMove, hValues]
  rfl

include hRB hRA hRS hBA hBS hAS in
private theorem run_stages (remaining i : Nat) (hIndex : i + remaining = exponent)
    {cfg : Config R (Option (PowerLabel exponent))}
    (hPC : cfg.pc = some (powerStage exponent i))
    (hAcc : cfg.values accumulator = 0) (hScratch : cfg.values scratch = 0) :
    run P x (powerTailTime (cfg.values base) (cfg.values result) remaining) cfg = some
      { cfg with
        pc := some none
        values := setValue result (cfg.values result * cfg.values base ^ remaining) cfg.values
      } := by
  induction remaining generalizing i cfg with
  | zero =>
    have hExit : cfg.pc = some none := by
      simpa [powerStage, show ¬i < exponent by omega] using hPC
    have hIdentity : setValue result (cfg.values result) cfg.values = cfg.values := by
      funext r
      by_cases h : r = result <;> simp [setValue, h]
    simp only [powerTailTime, run_zero, Nat.pow_zero, Nat.mul_one, hIdentity]
    cases cfg
    congr
  | succ remaining ih =>
    have hi : i < exponent := by omega
    let mid : Config R (Option (PowerLabel exponent)) := { cfg with
      pc := some (powerStage exponent (i + 1))
      values := setValue result (cfg.values result * cfg.values base) cfg.values }
    have hRun : run P x (cfg.values result * (7 * cfg.values base + 3) + 2) cfg = some mid :=
      run_stage x hRB hRA hRS hBA hBS hAS ⟨i, hi⟩ (by simpa [powerStage, hi] using hPC)
        hAcc hScratch
    have hRest := ih (i + 1) (by omega) (cfg := mid) rfl
      (by simp [mid, hRA.symm, hAcc, setValue_other])
      (by simp [mid, hRS.symm, hScratch, setValue_other])
    have hMidBase : mid.values base = cfg.values base := setValue_other hRB.symm _ _
    have hMidResult : mid.values result = cfg.values result * cfg.values base := setValue_same ..
    have hValues : setValue result (mid.values result * mid.values base ^ remaining) mid.values =
        setValue result (cfg.values result * cfg.values base ^ (remaining + 1)) cfg.values := by
      funext r
      by_cases h : r = result
      · subst r
        simp only [setValue_same, hMidResult, hMidBase, Nat.mul_assoc, Nat.pow_succ']
      · simp [mid, setValue_other h]
    rw [hValues, hMidBase, hMidResult] at hRest
    rw [powerTailTime, run_add, hRun, Option.bind_some]
    exact hRest

include hRB hRA hRS hBA hBS hAS in
/-- Starting with zero work registers, compute a fixed power and reach normal exit. -/
theorem run_power {cfg : Config R (Option (PowerLabel exponent))}
    (hPC : cfg.pc = some (some (.inl 0))) (hResult : cfg.values result = 0)
    (hAcc : cfg.values accumulator = 0) (hScratch : cfg.values scratch = 0) :
    run P x (1 + powerTailTime (cfg.values base) 1 exponent) cfg = some
      { cfg with
        pc := some none
        values := setValue result (cfg.values base ^ exponent) cfg.values } := by
  let mid : Config R (Option (PowerLabel exponent)) := { cfg with
    pc := some (powerStage exponent 0)
    values := incrementValues result cfg.values }
  have hCode : P (some (.inl 0)) = .inc result (powerStage exponent 0) := rfl
  have hInit : run P x 1 cfg = some mid := by
    rw [run_succ, step_inc hPC hCode, Option.bind_some, run_zero]
  have hRest := run_stages x hRB hRA hRS hBA hBS hAS exponent 0 (Nat.zero_add _) (cfg := mid) rfl
    (by simp [mid, incrementValues, hRA.symm, hAcc])
    (by simp [mid, incrementValues, hRS.symm, hScratch])
  have hMidBase : mid.values base = cfg.values base := by
    simp [mid, incrementValues, hRB.symm]
  have hMidResult : mid.values result = 1 := by simp [mid, incrementValues, hResult]
  have hValues : setValue result (mid.values result * mid.values base ^ exponent) mid.values =
      setValue result (cfg.values base ^ exponent) cfg.values := by
    funext r
    by_cases h : r = result
    · subst r
      simp [hMidResult, hMidBase]
    · simp [mid, setValue, incrementValues, h]
  rw [hValues, hMidBase, hMidResult] at hRest
  rw [run_add, hInit, Option.bind_some]
  exact hRest

end PvsNP.RegisterMachine
