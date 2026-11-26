module

public import PvsNP.TuringMachine.Registers.OutputRuns

/-! # Subtracting one preserved register from another -/

@[expose] public section

namespace PvsNP.RegisterMachine.Fragment

variable {R : Type}

/-- Spend one temporary unit for each truncated decrement of the target. -/
abbrev subtractLoop (target work : R) : Fragment R where
  Label := Bool
  entry := some false
  code
    | false => .dec work none (some true)
    | true => .dec target (some false) (some false)

/-- Copy the subtrahend, subtract it, and clear the working copy. -/
abbrev subtract (source target work scratch : R) : Fragment R :=
  (add source work scratch).seq (subtractLoop target work)

variable [DecidableEq R]

private theorem run_subtractLoop (target work : R) (x : BinaryWord) (hTW : target ≠ work)
    {cfg : (subtractLoop target work).Cfg} (hPC : cfg.pc = some (some false)) :
    (subtractLoop target work).run x (2 * cfg.values work + 1) cfg =
      some ⟨some none,
        setValue work 0 (setValue target (cfg.values target - cfg.values work) cfg.values),
        cfg.cursor, cfg.output⟩ := by
  let P := (subtractLoop target work).close
  generalize hCount : cfg.values work = count
  induction count generalizing cfg with
  | zero =>
    have hStep := step_dec_zero (program := P) (x := x) (next := some true) hPC rfl hCount
    change RegisterMachine.run P x 1 cfg = _
    rw [RegisterMachine.run_succ P x 0, hStep, Option.bind_some, RegisterMachine.run_zero,
      Nat.sub_zero, setValue_current, ← hCount, setValue_current]
  | succ count ih =>
    let mid : (subtractLoop target work).Cfg := { cfg with
      pc := some (some true), values := decrementValues work cfg.values }
    let next : (subtractLoop target work).Cfg := { mid with
      pc := some (some false), values := decrementValues target mid.values }
    have hStep := step_dec_pos (program := P) (x := x) (zero := none)
      (next := some true) hPC rfl (Nat.pos_of_ne_zero (by omega))
    have hStepTarget : step P x mid = some next := by
      by_cases hZero : mid.values target = 0
      · have hSame : decrementValues target mid.values = mid.values := by
          funext r
          by_cases h : r = target
          · subst r
            simp [decrementValues, hZero]
          · simp [decrementValues, h]
        simpa only [next, hSame] using step_dec_zero (program := P) (x := x)
          (cfg := mid) (label := some true) (next := some false) rfl rfl hZero
      · exact step_dec_pos (cfg := mid) (label := some true) (zero := some false)
          rfl rfl (Nat.pos_of_ne_zero hZero)
    have hNextWork : next.values work = count := by
      simp [next, mid, decrementValues, hTW.symm, hCount]
    have hNextTarget : next.values target = cfg.values target - 1 := by
      simp [next, mid, decrementValues, hTW]
    have hRest := ih (cfg := next) rfl hNextWork
    have hValues :
        setValue work 0 (setValue target (next.values target - count) next.values) =
          setValue work 0 (setValue target (cfg.values target - (count + 1)) cfg.values) := by
      funext r
      by_cases hW : r = work
      · subst r
        simp
      · by_cases hT : r = target
        · subst r
          simp [setValue_other hTW, hNextTarget, Nat.sub_sub]
          omega
        · simp [next, mid, setValue, decrementValues, hW, hT]
    change RegisterMachine.run P x (2 * (count + 1) + 1) cfg = _
    change RegisterMachine.run P x (2 * count + 1) next = _ at hRest
    rw [show 2 * (count + 1) + 1 = ((2 * count + 1) + 1) + 1 by omega,
      RegisterMachine.run_succ, hStep, Option.bind_some, RegisterMachine.run_succ,
      hStepTarget, Option.bind_some, hRest, hValues]

/-- Subtract the preserved source in seven instructions per source unit and three fixed steps. -/
theorem runsValues_subtract (source target work scratch : R) (x : BinaryWord) (v : R → Nat)
    (hSW : source ≠ work) (hSS : source ≠ scratch) (hWS : work ≠ scratch)
    (hTW : target ≠ work) (hWork : v work = 0) (hScratch : v scratch = 0) :
    (subtract source target work scratch).RunsValues x (7 * v source + 3)
      v (setValue target (v target - v source) v) := by
  let copied := setValue work (v source) v
  have hCopy : (add source work scratch).RunsValues x (5 * v source + 2) v copied := by
    simpa only [copied, hWork, Nat.zero_add] using
      runsValues_add source work scratch x v hSW hSS hWS hScratch
  have hLoop : (subtractLoop target work).RunsValues x (2 * v source + 1)
      copied (setValue target (v target - v source) v) := by
    intro suffix
    let cfg : Config R Unit := ⟨none, copied, none, suffix⟩
    have hRun := run_subtractLoop target work x hTW
      (cfg := (subtractLoop target work).enter cfg) rfl
    have hValues :
        setValue work 0 (setValue target (v target - v source) copied) =
          setValue target (v target - v source) v := by
      funext r
      by_cases hW : r = work
      · subst r
        simp [setValue_other hTW.symm, hWork]
      · by_cases hT : r = target
        · subst r
          simp [setValue_other hTW]
        · simp [copied, setValue, hW, hT]
    have hCopiedWork : copied work = v source := setValue_same ..
    have hCopiedTarget : copied target = v target := setValue_other hTW ..
    change (subtractLoop target work).run x (2 * copied work + 1) _ =
      some ⟨some none, setValue work 0 (setValue target (copied target - copied work) copied),
        none, suffix⟩ at hRun
    rw [hCopiedWork, hCopiedTarget, hValues] at hRun
    exact hRun
  rw [show 7 * v source + 3 = (5 * v source + 2) + (2 * v source + 1) by omega]
  exact hCopy.seq hLoop

end PvsNP.RegisterMachine.Fragment
