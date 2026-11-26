module

public import PvsNP.TuringMachine.Registers.Program

/-! # Moving a unary register value

Each positive test transfers one unit from the source to the target.
The zero test leaves the source empty and continues at the successor label.
-/

@[expose] public section

namespace PvsNP.RegisterMachine

variable {R L : Type} [DecidableEq R]

/-- The two internal instructions in a destructive register transfer. -/
structure MoveRules (program : L → Instruction R L) (source target : R) where
  entry : L
  write : L
  next : L
  takeSource : program entry = .dec source next write
  writeTarget : program write = .inc target entry

/-- Add the source to the target and empty the source. -/
def moveValues (source target : R) (values : R → Nat) : R → Nat :=
  fun r ↦ if r = source then 0 else if r = target then values r + values source else values r

/-- A destructive transfer takes two instructions per unit and one final test. -/
theorem run_move {program : L → Instruction R L} {source target : R}
    (rules : MoveRules program source target) (x : BinaryWord) (hDistinct : source ≠ target)
    {cfg : Config R L} (hPC : cfg.pc = some rules.entry) :
    run program x (2 * cfg.values source + 1) cfg = some
      { cfg with pc := some rules.next, values := moveValues source target cfg.values } := by
  generalize hCount : cfg.values source = count
  induction count generalizing cfg with
  | zero =>
    have hValues : moveValues source target cfg.values = cfg.values := by
      funext r
      by_cases hr : r = source
      · subst r
        simp [moveValues, hCount]
      · simp [moveValues, hr, hCount]
    rw [hValues]
    simp only [run, Option.bind_some, step_dec_zero (x := x) hPC rules.takeSource hCount]
  | succ count ih =>
    have hPos : 0 < cfg.values source := hCount ▸ Nat.succ_pos count
    let taken := { cfg with pc := some rules.write, values := decrementValues source cfg.values }
    let mid := { taken with
      pc := some rules.entry
      values := incrementValues target taken.values }
    have hFirst : run program x 2 cfg = some mid := by
      rw [run_succ, step_dec_pos hPC rules.takeSource hPos, Option.bind_some]
      change run program x 1 taken = some mid
      rw [run_succ, step_inc (cfg := taken) (x := x) rfl rules.writeTarget,
        Option.bind_some, run_zero]
    have hMid : mid.values source = count := by
      simp [mid, taken, incrementValues, decrementValues, hDistinct, hCount]
    have hValues : moveValues source target mid.values = moveValues source target cfg.values := by
      funext r
      by_cases hs : r = source
      · simp [moveValues, hs]
      by_cases ht : r = target
      · subst r
        have hTarget : mid.values target = cfg.values target + 1 := by
          simp [mid, taken, incrementValues, decrementValues, hDistinct.symm]
        simp only [moveValues, ite_eq_right hDistinct.symm, ite_true, hMid, hTarget, hCount]
        omega
      · simp [moveValues, mid, taken, incrementValues, decrementValues, hs, ht]
    rw [show 2 * (count + 1) + 1 = 2 + (2 * count + 1) by omega,
      run_add, hFirst, Option.bind_some, ih (cfg := mid) rfl hMid, hValues]

end PvsNP.RegisterMachine
