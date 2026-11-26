module

public import PvsNP.TuringMachine.Registers.Program

/-! # Counted register clearing -/

@[expose] public section

namespace PvsNP.RegisterMachine

variable {R L : Type} [DecidableEq R]

/-- Set one register to zero. -/
def clearValues (lane : R) (values : R → Nat) : R → Nat :=
  fun r ↦ if r = lane then 0 else values r

theorem clearValues_of_zero {lane : R} {values : R → Nat} (hZero : values lane = 0) :
    clearValues lane values = values := by
  funext r
  by_cases hr : r = lane
  · subst r
    simp [clearValues, hZero]
  · simp [clearValues, hr]

private theorem clearValues_decrement (lane : R) (values : R → Nat) :
    clearValues lane (decrementValues lane values) = clearValues lane values := by
  funext r
  by_cases hr : r = lane <;> simp [clearValues, decrementValues, hr]

/-- A decrement loop clears the register in one instruction per unit and one final zero test. -/
theorem run_clear {program : L → Instruction R L} (x : BinaryWord)
    {lane : R} {entry next : L} (hRule : program entry = .dec lane next entry)
    {cfg : Config R L} (hPC : cfg.pc = some entry) :
    run program x (cfg.values lane + 1) cfg = some
      { cfg with pc := some next, values := clearValues lane cfg.values } := by
  generalize hCount : cfg.values lane = count
  induction count generalizing cfg with
  | zero =>
    rw [clearValues_of_zero hCount]
    simp only [run, Option.bind_some, step_dec_zero (x := x) hPC hRule hCount]
  | succ n ih =>
    have hPos : 0 < cfg.values lane := hCount ▸ Nat.succ_pos n
    let mid := { cfg with pc := some entry, values := decrementValues lane cfg.values }
    have hDec : run program x 1 cfg = some mid := by
      simp only [run, Option.bind_some, step_dec_pos hPC hRule hPos]
      rfl
    have hMid : mid.values lane = n := by simp [mid, decrementValues, hCount]
    have hRest := ih (cfg := mid) rfl hMid
    have hTime : n + 1 + 1 = 1 + (n + 1) := by omega
    rw [hTime, run_add, hDec, Option.bind_some, hRest]
    exact congrArg (fun values ↦ some { cfg with pc := some next, values })
      (clearValues_decrement lane cfg.values)

end PvsNP.RegisterMachine
