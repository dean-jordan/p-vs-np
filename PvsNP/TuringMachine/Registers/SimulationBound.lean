module

public import PvsNP.TuringMachine.Registers.Simulation
public import PvsNP.TuringMachine.Transducer

/-!
# Polynomial simulation of register programs

Each abstract instruction grows the output and work bound by at most one.
Over a counted trace, the per-instruction tape costs therefore add up to a
quadratic bound in the instruction count and input length.
-/

@[expose] public section

namespace PvsNP.RegisterMachine

variable {R L : Type} [Finite R] [Finite L] [DecidableEq R]

/-- A successful counted register run has a matching counted tape run. -/
theorem Matches.run {entry : L} {program : L → Instruction R L} {x : BinaryWord}
    {work : Nat} {cfg next : Config R L} {tapeCfg : (control entry program).Config}
    (h : Matches entry program x work cfg tapeCfg) (hOut : cfg.output.length ≤ work)
    {steps : Nat} (hRun : RegisterMachine.run program x steps cfg = some next) :
    ∃ ticks ≤ steps * (2 * x.length + 3 * (work + steps) + 6),
      Matches entry program x (work + steps) next ((control entry program).run ticks tapeCfg) := by
  induction steps generalizing work cfg tapeCfg with
  | zero =>
    simp only [run_zero, Option.some.injEq] at hRun
    subst next
    exact ⟨0, Nat.zero_le _, h⟩
  | succ steps ih =>
    rw [run_succ] at hRun
    cases hStep : RegisterMachine.step program x cfg with
    | none => simp [hStep] at hRun
    | some mid =>
      simp only [hStep, Option.bind_some] at hRun
      obtain ⟨cost, hCost, hMid⟩ := h.step hOut hStep
      have hOut' : mid.output.length ≤ work + 1 :=
        Nat.le_trans (step_invariants hStep).2.1 (Nat.add_le_add_right hOut 1)
      obtain ⟨ticks, hTicks, hMatch⟩ := ih hMid hOut' hRun
      have hWork : work + 1 + steps = work + (steps + 1) := by omega
      rw [hWork] at hTicks hMatch
      refine ⟨cost + ticks, ?_, ?_⟩
      · have hCost' : cost ≤ 2 * x.length + 3 * (work + (steps + 1)) + 6 := by omega
        rw [Nat.add_mul, Nat.one_mul, Nat.add_comm cost ticks]
        exact Nat.add_le_add hTicks hCost'
      · simpa only [Machine.run_add] using hMatch

/-- A bound on tape ticks, including input preparation and the final instruction. -/
def simulationTime (input steps : Nat) : Nat :=
  input + 4 + steps * (2 * input + 3 * steps + 6)

theorem simulationTime_mono_steps (input : Nat) {steps bound : Nat} (h : steps ≤ bound) :
    simulationTime input steps ≤ simulationTime input bound := by
  unfold simulationTime
  exact Nat.add_le_add_left (Nat.mul_le_mul h (by omega)) _

theorem simulationTime_polynomiallyBounded {bound : Nat → Nat}
    (hBound : PolynomiallyBounded bound) :
    PolynomiallyBounded (fun n ↦ simulationTime n (bound n)) :=
  let hInput := PolynomiallyBounded.id
  let hConst := PolynomiallyBounded.const
  let hInstruction := (((hConst 2).mul hInput).add ((hConst 3).mul hBound)).add (hConst 6)
  (hInput.add (hConst 4)).add (hBound.mul hInstruction)

/-- A successful abstract halt gives an accepting tape halt with the same output. -/
theorem outputsAt_of_run {entry : L} {program : L → Instruction R L} {x : BinaryWord}
    {steps : Nat} {cfg : Config R L}
    (hRun : run program x steps (Config.initial entry) = some cfg) (hPC : cfg.pc = none) :
    ∃ ticks ≤ simulationTime x.length steps,
      (control entry program).OutputsAt x cfg.output ticks := by
  obtain ⟨ticks, hTicks, hMatch⟩ := (matches_start entry program x).run (Nat.zero_le _) hRun
  have hHalted := hMatch.halted hPC
  refine ⟨x.length + 4 + ticks, ?_, ?_⟩
  · simpa only [simulationTime, Nat.zero_add] using Nat.add_le_add_left hTicks (x.length + 4)
  · unfold Machine.OutputsAt
    rw [Machine.run_add, hHalted]
    exact ⟨rfl, rfl⟩

/-- A polynomially bounded total register program computes its function in Cook's model. -/
theorem polynomialTimeMap_of_run (entry : L) (program : L → Instruction R L)
    {f : BinaryWord → BinaryWord} {bound : Nat → Nat}
    (hBound : PolynomiallyBounded bound)
    (hRun : ∀ x, ∃ steps ≤ bound x.length, ∃ cfg,
      run program x steps (Config.initial entry) = some cfg ∧ cfg.pc = none ∧ cfg.output = f x) :
    PolynomialTimeMap f := by
  have hOutput (x : BinaryWord) : ∃ ticks ≤ simulationTime x.length (bound x.length),
      (control entry program).OutputsAt x (f x) ticks := by
    obtain ⟨steps, hSteps, cfg, hExec, hPC, hOutput⟩ := hRun x
    obtain ⟨ticks, hTicks, hTape⟩ := outputsAt_of_run hExec hPC
    exact ⟨ticks, hTicks.trans (simulationTime_mono_steps x.length hSteps), hOutput ▸ hTape⟩
  refine ⟨control entry program, ?_, ?_⟩
  · refine (Machine.polyTime_iff_polynomiallyBounded _).mpr
      ⟨_, simulationTime_polynomiallyBounded hBound, fun x ↦ ?_⟩
    obtain ⟨ticks, hTicks, hHalt⟩ := hOutput x
    exact ⟨ticks, hTicks, true, hHalt.1⟩
  · intro x
    obtain ⟨ticks, _, hResult⟩ := hOutput x
    exact ⟨ticks, hResult⟩

end PvsNP.RegisterMachine
