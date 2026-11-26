module

public import PvsNP.TuringMachine.Registers.Program

/-! # Counted register addition

The first loop adds the source to the target and a scratch register.
The second loop restores the source from the scratch register.
-/

@[expose] public section

namespace PvsNP.RegisterMachine

variable {R L : Type} [DecidableEq R]

/-- Program labels and instructions for adding through a scratch register. -/
structure CopyRules (program : L → Instruction R L) (source target scratch : R) where
  entry : L
  addTarget : L
  addScratch : L
  restore : L
  addSource : L
  next : L
  takeSource : program entry = .dec source restore addTarget
  writeTarget : program addTarget = .inc target addScratch
  writeScratch : program addScratch = .inc scratch entry
  takeScratch : program restore = .dec scratch next addSource
  writeSource : program addSource = .inc source restore

/-- Addition uses the same program as copying into an empty target. -/
abbrev AddRules (program : L → Instruction R L) (source target scratch : R) :=
  CopyRules program source target scratch

/-- Add the source value to the target value. -/
def addValues (source target : R) (values : R → Nat) : R → Nat :=
  fun r ↦ if r = target then values r + values source else values r

variable {program : L → Instruction R L} {source target scratch : R}
variable (rules : AddRules program source target scratch) (x : BinaryWord)

private def transferResult (source target scratch : R) (values : R → Nat) : R → Nat :=
  fun r ↦ if r = source then 0 else if r = target ∨ r = scratch then
    values r + values source else values r

private def restoreResult (source scratch : R) (values : R → Nat) : R → Nat :=
  fun r ↦ if r = scratch then 0 else if r = source then values r + values scratch else values r

private def transferRound (source target scratch : R) (values : R → Nat) : R → Nat :=
  incrementValues scratch (incrementValues target (decrementValues source values))

private def restoreRound (source scratch : R) (values : R → Nat) : R → Nat :=
  incrementValues source (decrementValues scratch values)

private theorem run_transfer_round {cfg : Config R L}
    (hPC : cfg.pc = some rules.entry) (hPos : 0 < cfg.values source) :
    run program x 3 cfg = some
      { cfg with
        pc := some rules.entry
        values := transferRound source target scratch cfg.values } := by
  let decCfg := { cfg with pc := some rules.addTarget, values := decrementValues source cfg.values }
  let targetCfg := { decCfg with
    pc := some rules.addScratch
    values := incrementValues target decCfg.values }
  have hDec : step program x cfg = some decCfg := step_dec_pos hPC rules.takeSource hPos
  have hTarget : step program x decCfg = some targetCfg := step_inc rfl rules.writeTarget
  have hScratch : step program x targetCfg = some
      { cfg with
        pc := some rules.entry
        values := transferRound source target scratch cfg.values } :=
    step_inc rfl rules.writeScratch
  simp only [run, hDec, hTarget, hScratch, Option.bind_some]

private theorem run_restore_round {cfg : Config R L}
    (hPC : cfg.pc = some rules.restore) (hPos : 0 < cfg.values scratch) :
    run program x 2 cfg = some
      { cfg with
        pc := some rules.restore
        values := restoreRound source scratch cfg.values } := by
  let decCfg := { cfg with
    pc := some rules.addSource
    values := decrementValues scratch cfg.values }
  have hDec : step program x cfg = some decCfg := step_dec_pos hPC rules.takeScratch hPos
  have hSource : step program x decCfg = some
      { cfg with pc := some rules.restore, values := restoreRound source scratch cfg.values } :=
    step_inc rfl rules.writeSource
  simp only [run, hDec, hSource, Option.bind_some]

private theorem transferResult_round (values : R → Nat)
    (hST : source ≠ target) (hSW : source ≠ scratch) (hTW : target ≠ scratch)
    (hPos : 0 < values source) :
    transferResult source target scratch (transferRound source target scratch values) =
      transferResult source target scratch values := by
  funext r
  by_cases hs : r = source
  · subst r
    simp [transferResult]
  by_cases ht : r = target
  · subst r
    simp [transferResult, transferRound, incrementValues, decrementValues, hST, hST.symm,
      hSW, hTW]; omega
  by_cases hw : r = scratch
  · subst r
    simp [transferResult, transferRound, incrementValues, decrementValues, hST, hSW,
      hSW.symm, hTW.symm]; omega
  simp [transferResult, transferRound, incrementValues, decrementValues, hs, ht, hw]

private theorem restoreResult_round (values : R → Nat) (hSW : source ≠ scratch)
    (hPos : 0 < values scratch) :
    restoreResult source scratch (restoreRound source scratch values) =
      restoreResult source scratch values := by
  funext r
  by_cases hw : r = scratch
  · subst r
    simp [restoreResult]
  by_cases hs : r = source
  · subst r
    simp [restoreResult, restoreRound, incrementValues, decrementValues, hSW, hSW.symm]; omega
  simp [restoreResult, restoreRound, incrementValues, decrementValues, hw, hs]

private theorem run_transfer (hST : source ≠ target) (hSW : source ≠ scratch)
    (hTW : target ≠ scratch) {cfg : Config R L} (hPC : cfg.pc = some rules.entry) :
    run program x (3 * cfg.values source + 1) cfg = some
      { cfg with
        pc := some rules.restore
        values := transferResult source target scratch cfg.values } := by
  generalize hAmount : cfg.values source = amount
  induction amount generalizing cfg with
  | zero =>
    have hDone : transferResult source target scratch cfg.values = cfg.values := by
      funext r
      by_cases hs : r = source
      · subst r
        simp [transferResult, hAmount]
      · simp [transferResult, hs, hAmount]
    rw [hDone]
    simp only [run, Option.bind_some,
      step_dec_zero (x := x) hPC rules.takeSource hAmount]
  | succ amount ih =>
    have hPos : 0 < cfg.values source := hAmount ▸ Nat.succ_pos amount
    let mid := { cfg with
      pc := some rules.entry
      values := transferRound source target scratch cfg.values }
    have hRound : run program x 3 cfg = some mid := run_transfer_round rules x hPC hPos
    have hLeft : mid.values source = amount := by
      simp [mid, transferRound, incrementValues, decrementValues, hSW, hST, hAmount]
    have hRest := ih (cfg := mid) rfl hLeft
    have hValues : transferResult source target scratch mid.values =
        transferResult source target scratch cfg.values :=
      transferResult_round cfg.values hST hSW hTW hPos
    have hTime : 3 * (amount + 1) + 1 = 3 + (3 * amount + 1) := by omega
    rw [hTime, run_add, hRound, Option.bind_some, hRest, hValues]

private theorem run_restore (hSW : source ≠ scratch) {cfg : Config R L}
    (hPC : cfg.pc = some rules.restore) :
    run program x (2 * cfg.values scratch + 1) cfg = some
      { cfg with pc := some rules.next, values := restoreResult source scratch cfg.values } := by
  generalize hAmount : cfg.values scratch = amount
  induction amount generalizing cfg with
  | zero =>
    have hDone : restoreResult source scratch cfg.values = cfg.values := by
      funext r
      by_cases hw : r = scratch
      · subst r
        simp [restoreResult, hAmount]
      · simp [restoreResult, hw, hAmount]
    rw [hDone]
    simp only [run, Option.bind_some,
      step_dec_zero (x := x) hPC rules.takeScratch hAmount]
  | succ amount ih =>
    have hPos : 0 < cfg.values scratch := hAmount ▸ Nat.succ_pos amount
    let mid := { cfg with
      pc := some rules.restore
      values := restoreRound source scratch cfg.values }
    have hRound : run program x 2 cfg = some mid := run_restore_round rules x hPC hPos
    have hLeft : mid.values scratch = amount := by
      simp [mid, restoreRound, incrementValues, decrementValues, hSW.symm, hAmount]
    have hRest := ih (cfg := mid) rfl hLeft
    have hValues : restoreResult source scratch mid.values =
        restoreResult source scratch cfg.values :=
      restoreResult_round cfg.values hSW hPos
    have hTime : 2 * (amount + 1) + 1 = 2 + (2 * amount + 1) := by omega
    rw [hTime, run_add, hRound, Option.bind_some, hRest, hValues]

/-- Addition takes five instructions per source unit and two zero tests. It restores the
source and scratch registers and preserves the cursor and output. -/
theorem run_add_register (hST : source ≠ target) (hSW : source ≠ scratch) (hTW : target ≠ scratch)
    {cfg : Config R L} (hPC : cfg.pc = some rules.entry)
    (hScratch : cfg.values scratch = 0) :
    run program x (5 * cfg.values source + 2) cfg = some
      { cfg with pc := some rules.next, values := addValues source target cfg.values } := by
  let mid := { cfg with
    pc := some rules.restore
    values := transferResult source target scratch cfg.values }
  have hMid : run program x (3 * cfg.values source + 1) cfg = some mid :=
    run_transfer rules x hST hSW hTW hPC
  have hCount : mid.values scratch = cfg.values source := by
    simp [mid, transferResult, hSW.symm, hScratch]
  have hFinish := run_restore rules x hSW (cfg := mid) rfl
  rw [hCount] at hFinish
  have hValues : restoreResult source scratch mid.values = addValues source target cfg.values := by
    funext r
    by_cases hw : r = scratch
    · subst r
      simp [restoreResult, addValues, hTW.symm, hScratch]
    by_cases hs : r = source
    · subst r
      simp [restoreResult, addValues, mid, transferResult, hSW, hSW.symm, hST, hScratch]
    by_cases ht : r = target
    · subst r
      simp [restoreResult, addValues, mid, transferResult, hTW, hST.symm]
    simp [restoreResult, addValues, mid, transferResult, hw, hs, ht]
  have hTime : 5 * cfg.values source + 2 = (3 * cfg.values source + 1) +
      (2 * cfg.values source + 1) := by omega
  rw [hTime, run_add, hMid, Option.bind_some, hFinish, hValues]

end PvsNP.RegisterMachine
