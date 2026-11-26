module

public import PvsNP.TuringMachine.Registers.Countdown
public import PvsNP.TuringMachine.Registers.ValueRuns

/-! # Composing register fragments that produce output -/

@[expose] public section

namespace PvsNP.RegisterMachine.Fragment

variable {R : Type} [DecidableEq R]

/-- A normal run from a specified tape valuation and output suffix, with unmarked input. -/
def RunsOutput (f : Fragment R) (x : BinaryWord) (cost : Nat) (before after : R → Nat)
    (suffix output : BinaryWord) : Prop :=
  f.run x cost (f.enter (⟨none, before, none, suffix⟩ : Config R Unit)) =
    some ⟨some none, after, none, output⟩

theorem RunsOutput.seq {f g : Fragment R} {x : BinaryWord} {m n : Nat}
    {a b c : R → Nat} {suffix mid output : BinaryWord}
    (hFirst : f.RunsOutput x m a b suffix mid) (hSecond : g.RunsOutput x n b c mid output) :
    (f.seq g).RunsOutput x (m + n) a c suffix output :=
  run_seq hFirst rfl hSecond rfl

theorem RunsValues.withOutput {f : Fragment R} {x : BinaryWord} {cost : Nat}
    {before after : R → Nat} (h : f.RunsValues x cost before after) (suffix : BinaryWord) :
    f.RunsOutput x cost before after suffix suffix := h suffix

theorem runsOutput_skip (x : BinaryWord) (values : R → Nat) (suffix : BinaryWord) :
    (skip : Fragment R).RunsOutput x 0 values values suffix suffix := rfl

theorem setValue_current (reg : R) (v : R → Nat) : setValue reg (v reg) v = v := by
  funext r
  by_cases h : r = reg <;> simp [setValue, h]

theorem setValue_replace (reg : R) (a b : Nat) (v : R → Nat) :
    setValue reg b (setValue reg a v) = setValue reg b v := by
  funext r
  by_cases h : r = reg <;> simp [setValue, h]

/-- A descending output loop consumes its count and otherwise preserves its valuation.
The given body specification applies at each decremented index. -/
theorem runsOutput_countdown (counter : R) (body : Fragment R) (x : BinaryWord)
    (before : R → Nat) (bound : Nat) (update : BinaryWord → Nat → BinaryWord)
    (hBody : ∀ i, i < before counter → ∀ suffix,
      ∃ cost ≤ bound, body.RunsOutput x cost (setValue counter i before)
        (setValue counter i before) suffix (update suffix i)) (suffix : BinaryWord) :
    ∃ cost ≤ before counter * (bound + 1) + 1,
      (countdown counter body).RunsOutput x cost before (setValue counter 0 before) suffix
        ((List.range (before counter)).reverse.foldl update suffix) := by
  let inv (i : Nat) (acc : BinaryWord) (v : R → Nat) (cursor : Option Nat) (out : BinaryWord) :=
    v = setValue counter i before ∧ cursor = none ∧ out = acc ∧ i ≤ before counter
  let start : (countdown counter body).Cfg := ⟨some (some none), before, none, suffix⟩
  have hStep (i : Nat) (acc : BinaryWord) (cfg : (countdown counter body).Cfg)
      (hCount : cfg.values counter = i + 1)
      (hInv : inv (i + 1) acc cfg.values cfg.cursor cfg.output) :
      ∃ ticks ≤ bound, ∃ next : body.Cfg,
        body.run x ticks (countdownBodyStart counter body cfg) = some next ∧
        next.pc = some none ∧ next.values counter = i ∧
        inv i (update acc i) next.values next.cursor next.output := by
    obtain ⟨hValues, hCursor, hOut, hLimit⟩ := hInv
    have hDecrement : decrementValues counter cfg.values = setValue counter i before := by
      funext r
      by_cases hr : r = counter
      · subst r
        simp [decrementValues, hCount]
      · simp [decrementValues, hValues, setValue, hr]
    obtain ⟨ticks, hTicks, hRun⟩ := hBody i (by omega) acc
    let next : body.Cfg := ⟨some none, setValue counter i before, none, update acc i⟩
    refine ⟨ticks, hTicks, next, ?_, rfl, setValue_same .., rfl, rfl, rfl, by omega⟩
    simpa only [RunsOutput, countdownBodyStart, enter, hDecrement, hCursor, hOut, next] using hRun
  have hStart : inv (before counter) suffix start.values start.cursor start.output :=
    ⟨(setValue_current ..).symm, rfl, rfl, Nat.le_refl _⟩
  obtain ⟨costs, _, hCost, next, hRun, hExit, _, hInv⟩ :=
    run_countdown_model update inv bound hStep (cfg := start) rfl rfl hStart
  obtain ⟨hValues, hCursor, hOut, _⟩ := hInv
  refine ⟨_, hCost, ?_⟩
  have hNext : next = ⟨some none, setValue counter 0 before, none,
      (List.range (before counter)).reverse.foldl update suffix⟩ := by
    rcases next with ⟨pc, values, cursor, output⟩
    change pc = some none at hExit
    change values = setValue counter 0 before at hValues
    change cursor = none at hCursor
    change output = _ at hOut
    rw [hExit, hValues, hCursor, hOut]
  rw [hNext] at hRun
  exact hRun

/-- Copy a persistent count into an empty counter, then descend and clear that counter. -/
theorem runsOutput_initializedCountdown (source counter scratch : R) (body : Fragment R)
    (x : BinaryWord) (before : R → Nat) (bound : Nat) (update : BinaryWord → Nat → BinaryWord)
    (hSC : source ≠ counter) (hSS : source ≠ scratch) (hCS : counter ≠ scratch)
    (hCount : before counter = 0) (hScratch : before scratch = 0)
    (hBody : ∀ i, i < before source → ∀ suffix,
      ∃ cost ≤ bound, body.RunsOutput x cost (setValue counter i before)
        (setValue counter i before) suffix (update suffix i)) (suffix : BinaryWord) :
    ∃ cost ≤ (5 * before source + 2) + (before source * (bound + 1) + 1),
      ((add source counter scratch).seq (countdown counter body)).RunsOutput x cost before before
        suffix ((List.range (before source)).reverse.foldl update suffix) := by
  let initialized := setValue counter (before source) before
  have hInitialize : (add source counter scratch).RunsValues x (5 * before source + 2)
      before initialized := by
    simpa only [hCount, initialized, Nat.zero_add] using
      runsValues_add source counter scratch x before hSC hSS hCS hScratch
  have hInitial : initialized counter = before source := setValue_same ..
  have hStep : ∀ i, i < initialized counter → ∀ acc,
      ∃ cost ≤ bound, body.RunsOutput x cost (setValue counter i initialized)
        (setValue counter i initialized) acc (update acc i) := by
    intro i hi acc
    simpa only [initialized, setValue_replace] using hBody i (by rwa [hInitial] at hi) acc
  have hClear : setValue counter 0 initialized = before := by
    rw [show initialized = setValue counter (before source) before from rfl,
      setValue_replace, ← hCount, setValue_current]
  obtain ⟨ticks, hTicks, hRun⟩ := runsOutput_countdown counter body x initialized bound
    update hStep suffix
  rw [hInitial] at hTicks
  rw [hClear, hInitial] at hRun
  exact ⟨_, Nat.add_le_add_left hTicks _, (hInitialize.withOutput suffix).seq hRun⟩

end PvsNP.RegisterMachine.Fragment
