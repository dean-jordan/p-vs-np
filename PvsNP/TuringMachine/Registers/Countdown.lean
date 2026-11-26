module

public import PvsNP.TuringMachine.Registers.Fragments

/-! # Counted register program loops -/

@[expose] public section

namespace PvsNP.RegisterMachine.Fragment

variable {R : Type}

/-- Decrement the counter before running the body. The body's exit returns to
the test. A zero counter leaves the loop, and an empty body jumps back to the
test directly. -/
abbrev countdown (counter : R) (body : Fragment R) : Fragment R where
  Label := Option body.Label
  entry := some none
  code
    | none => .dec counter none (some body.entry)
    | some label => (body.code label).map some

variable [DecidableEq R]

/-- Enter the body with the already decremented counter. -/
def countdownBodyStart (counter : R) (body : Fragment R) (cfg : (countdown counter body).Cfg) :
    body.Cfg :=
  body.enter { cfg with values := decrementValues counter cfg.values }

/-- Testing a zero counter exits in one instruction, preserving all data. -/
theorem run_countdown_zero {counter : R} {body : Fragment R} {x : BinaryWord}
    {cfg : (countdown counter body).Cfg} (hPC : cfg.pc = some (some none))
    (hZero : cfg.values counter = 0) :
    (countdown counter body).run x 1 cfg = some { cfg with pc := some none } := by
  have hStep := step_dec_zero (program := (countdown counter body).close) (x := x)
    (reg := counter) (zero := none) (next := some body.entry) hPC rfl hZero
  change RegisterMachine.run (countdown counter body).close x 1 cfg = _
  rw [show (1 : Nat) = 0 + 1 by rfl, RegisterMachine.run_succ, hStep, Option.bind_some, run_zero]

/-- One positive test and a completed body return to the test after exactly
one more instruction than the body alone. -/
theorem run_countdown_iteration {counter : R} {body : Fragment R} {x : BinaryWord}
    {cfg : (countdown counter body).Cfg} {n : Nat} {next : body.Cfg}
    (hPC : cfg.pc = some (some none)) (hPos : 0 < cfg.values counter)
    (hRun : body.run x n (countdownBodyStart counter body cfg) = some next)
    (hExit : next.pc = some none) :
    (countdown counter body).run x (1 + n) cfg = some (next.map some) := by
  have hStep := step_dec_pos (program := (countdown counter body).close) (x := x)
    (reg := counter) (zero := none) (next := some body.entry) hPC rfl hPos
  have hBody := run_link some (target := (countdown counter body).close)
    (fun _ ↦ rfl) hRun hExit
  change RegisterMachine.run (countdown counter body).close x (1 + n) cfg = _
  rw [Nat.add_comm 1 n, RegisterMachine.run_succ, hStep, Option.bind_some]
  exact hBody

/-- Run the body at each index in descending order. The model invariant
relates the remaining count and accumulator to the program data. If each
body takes at most `bodyBound` instructions and preserves the decremented
counter, the loop uses exactly the sum of its body costs, one test per
iteration, and the final zero test. -/
theorem run_countdown_model {counter : R} {body : Fragment R} {x : BinaryWord} {σ : Type}
    (update : σ → Nat → σ) (Inv : Nat → σ → (R → Nat) → Option Nat → BinaryWord → Prop)
    (bodyBound : Nat)
    (hBody : ∀ (i : Nat) (acc : σ) (cfg : (countdown counter body).Cfg),
      cfg.values counter = i + 1 → Inv (i + 1) acc cfg.values cfg.cursor cfg.output →
      ∃ ticks ≤ bodyBound, ∃ next : body.Cfg,
        body.run x ticks (countdownBodyStart counter body cfg) = some next ∧
        next.pc = some none ∧ next.values counter = i ∧
        Inv i (update acc i) next.values next.cursor next.output)
    {count : Nat} {acc : σ} {cfg : (countdown counter body).Cfg}
    (hPC : cfg.pc = some (some none)) (hCount : cfg.values counter = count)
    (hInv : Inv count acc cfg.values cfg.cursor cfg.output) :
    ∃ costs : List Nat, costs.length = count ∧
      count + costs.sum + 1 ≤ count * (bodyBound + 1) + 1 ∧
      ∃ next : (countdown counter body).Cfg,
        (countdown counter body).run x (count + costs.sum + 1) cfg = some next ∧
        next.pc = some none ∧ next.values counter = 0 ∧
        Inv 0 ((List.range count).reverse.foldl update acc)
          next.values next.cursor next.output := by
  induction count generalizing acc cfg with
  | zero =>
    exact ⟨[], rfl, by simp, { cfg with pc := some none },
      run_countdown_zero hPC hCount, rfl, hCount, hInv⟩
  | succ remaining ih =>
    obtain ⟨ticks, hTicks, mid, hRun, hExit, hRemaining, hMid⟩ :=
      hBody remaining acc cfg hCount hInv
    have hMidPC : (mid.map some).pc = some (some none) := by simp [Config.map, hExit]
    obtain ⟨costs, hLength, hCost, next, hLoop, hNext, hZero, hFinal⟩ :=
      ih hMidPC hRemaining hMid
    have hIteration := run_countdown_iteration hPC (by omega) hRun hExit
    refine ⟨ticks :: costs, by simp [hLength], ?_, next, ?_, hNext, hZero, ?_⟩
    · simp only [List.sum_cons, Nat.add_mul, Nat.one_mul]
      omega
    · have hTotal : remaining + 1 + (ticks :: costs).sum + 1 =
          (1 + ticks) + (remaining + costs.sum + 1) := by
        simp only [List.sum_cons]
        omega
      change RegisterMachine.run (countdown counter body).close x _ cfg = _
      change RegisterMachine.run (countdown counter body).close x (1 + ticks) cfg =
        some (mid.map some) at hIteration
      rw [hTotal, RegisterMachine.run_add, hIteration, Option.bind_some]
      exact hLoop
    · simpa only [List.range_succ, List.reverse_append, List.reverse_singleton,
        List.singleton_append, List.foldl_cons] using hFinal

end PvsNP.RegisterMachine.Fragment
