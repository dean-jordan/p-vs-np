module

public import PvsNP.TuringMachine.Registers.Add

/-! # Counted register multiplication

Each positive test consumes one unit of the multiplier and adds the
multiplicand to the accumulator. The zero test exits the loop.
-/

@[expose] public section

namespace PvsNP.RegisterMachine

variable {R L : Type} [DecidableEq R]

/-- Program rules for multiplying by repeated addition. -/
structure MultiplyRules (program : L → Instruction R L)
    (multiplier multiplicand accumulator scratch : R) where
  entry : L
  next : L
  add : AddRules program multiplicand accumulator scratch
  takeMultiplier : program entry = .dec multiplier next add.entry
  addReturns : add.next = entry

/-- Consume the multiplier and add the product to the accumulator. -/
def multiplyValues (multiplier multiplicand accumulator : R) (values : R → Nat) : R → Nat :=
  fun r ↦ if r = multiplier then 0 else if r = accumulator then
    values r + values multiplier * values multiplicand else values r

/-- Multiplication consumes the multiplier, restores the scratch register, and preserves
the multiplicand, cursor and output. -/
theorem run_multiply {program : L → Instruction R L}
    {multiplier multiplicand accumulator scratch : R}
    (rules : MultiplyRules program multiplier multiplicand accumulator scratch) (x : BinaryWord)
    (hMP : multiplier ≠ multiplicand) (hMA : multiplier ≠ accumulator)
    (hMS : multiplier ≠ scratch) (hPA : multiplicand ≠ accumulator)
    (hPS : multiplicand ≠ scratch) (hAS : accumulator ≠ scratch)
    {cfg : Config R L} (hPC : cfg.pc = some rules.entry) (hScratch : cfg.values scratch = 0) :
    run program x (cfg.values multiplier * (5 * cfg.values multiplicand + 3) + 1) cfg = some
      { cfg with
        pc := some rules.next
        values := multiplyValues multiplier multiplicand accumulator cfg.values } := by
  generalize hAmount : cfg.values multiplier = amount
  induction amount generalizing cfg with
  | zero =>
    have hValues : multiplyValues multiplier multiplicand accumulator cfg.values = cfg.values := by
      funext r
      by_cases hr : r = multiplier
      · subst r
        simp [multiplyValues, hAmount]
      · simp [multiplyValues, hr, hAmount]
    rw [hValues]
    simp only [Nat.zero_mul, run, Option.bind_some,
      step_dec_zero (x := x) hPC rules.takeMultiplier hAmount]
  | succ amount ih =>
    have hPos : 0 < cfg.values multiplier := hAmount ▸ Nat.succ_pos amount
    let decCfg := { cfg with
      pc := some rules.add.entry
      values := decrementValues multiplier cfg.values }
    have hDec : run program x 1 cfg = some decCfg := by
      simp only [run, Option.bind_some, step_dec_pos hPC rules.takeMultiplier hPos]
      rfl
    have hDecScratch : decCfg.values scratch = 0 := by
      simp [decCfg, decrementValues, hMS.symm, hScratch]
    have hDecMultiplicand : decCfg.values multiplicand = cfg.values multiplicand := by
      simp [decCfg, decrementValues, hMP.symm]
    have hAdd := run_add_register rules.add x hPA hPS hAS (cfg := decCfg) rfl hDecScratch
    rw [hDecMultiplicand] at hAdd
    let mid := { cfg with
      pc := some rules.entry
      values := addValues multiplicand accumulator decCfg.values }
    have hRound : run program x (5 * cfg.values multiplicand + 3) cfg = some mid := by
      rw [show 5 * cfg.values multiplicand + 3 = 1 + (5 * cfg.values multiplicand + 2) by omega,
        run_add, hDec, Option.bind_some, hAdd, rules.addReturns]
    have hMidMultiplier : mid.values multiplier = amount := by
      simp [mid, addValues, decCfg, decrementValues, hMA, hAmount]
    have hMidMultiplicand : mid.values multiplicand = cfg.values multiplicand := by
      simp [mid, addValues, decCfg, decrementValues, hPA, hMP.symm]
    have hMidScratch : mid.values scratch = 0 := by
      simp [mid, addValues, decCfg, decrementValues, hAS.symm, hMS.symm, hScratch]
    have hRest := ih (cfg := mid) rfl hMidScratch hMidMultiplier
    rw [hMidMultiplicand] at hRest
    have hValues : multiplyValues multiplier multiplicand accumulator mid.values =
        multiplyValues multiplier multiplicand accumulator cfg.values := by
      funext r
      by_cases hm : r = multiplier
      · subst r
        simp [multiplyValues]
      by_cases ha : r = accumulator
      · subst r
        have hMidAccumulator : mid.values accumulator =
            cfg.values accumulator + cfg.values multiplicand := by
          simp [mid, addValues, decCfg, decrementValues, hMA.symm, hMP.symm]
        simp only [multiplyValues, ite_eq_right hMA.symm, ite_true, hMidAccumulator,
          hMidMultiplier, hMidMultiplicand, hAmount, Nat.succ_mul]
        omega
      simp [multiplyValues, mid, addValues, decCfg, decrementValues, hm, ha]
    have hTime : (amount + 1) * (5 * cfg.values multiplicand + 3) + 1 =
        (5 * cfg.values multiplicand + 3) + (amount * (5 * cfg.values multiplicand + 3) + 1) := by
      rw [Nat.succ_mul]
      omega
    rw [hTime, run_add, hRound, Option.bind_some, hRest, hValues]

end PvsNP.RegisterMachine
