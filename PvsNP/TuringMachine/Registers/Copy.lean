module

public import PvsNP.TuringMachine.Registers.Add

/-! # Counted register copy -/

@[expose] public section

namespace PvsNP.RegisterMachine

variable {R L : Type} [DecidableEq R]

/-- Replace the target value with the source value. -/
def copyValues (source target : R) (values : R → Nat) : R → Nat :=
  fun r ↦ if r = target then values source else values r

/-- Copy takes five instructions per source unit and two zero tests. -/
theorem run_copy {program : L → Instruction R L} {source target scratch : R}
    (rules : CopyRules program source target scratch) (x : BinaryWord)
    (hST : source ≠ target) (hSW : source ≠ scratch) (hTW : target ≠ scratch)
    {cfg : Config R L} (hPC : cfg.pc = some rules.entry)
    (hTarget : cfg.values target = 0) (hScratch : cfg.values scratch = 0) :
    run program x (5 * cfg.values source + 2) cfg = some
      { cfg with pc := some rules.next, values := copyValues source target cfg.values } := by
  have hValues : addValues source target cfg.values = copyValues source target cfg.values := by
    funext r
    by_cases hr : r = target
    · subst r
      simp [addValues, copyValues, hTarget]
    · simp [addValues, copyValues, hr]
  rw [← hValues]
  exact run_add_register rules x hST hSW hTW hPC hScratch

end PvsNP.RegisterMachine
