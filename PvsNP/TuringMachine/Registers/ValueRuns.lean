module

public import PvsNP.TuringMachine.Registers.BasicFragments
public import PvsNP.TuringMachine.Registers.Power

/-! # Exact register-value runs -/

@[expose] public section

namespace PvsNP.RegisterMachine.Fragment

variable {R : Type} [DecidableEq R]

/-- A normal exact run on register values, preserving any preexisting output
and leaving the cursor unmarked. -/
def RunsValues (fragment : Fragment R) (x : BinaryWord) (cost : Nat)
    (before after : R → Nat) : Prop :=
  ∀ output, fragment.run x cost (fragment.enter (⟨none, before, none, output⟩ : Config R Unit)) =
    some ⟨some none, after, none, output⟩

/-- Compose exact register-value runs with no additional instruction at the boundary. -/
theorem RunsValues.seq {first second : Fragment R} {x : BinaryWord} {m n : Nat}
    {before mid after : R → Nat} (hFirst : first.RunsValues x m before mid)
    (hSecond : second.RunsValues x n mid after) :
    (first.seq second).RunsValues x (m + n) before after := by
  intro output
  exact Fragment.run_seq (hFirst output) rfl (hSecond output) rfl

theorem runsValues_skip (x : BinaryWord) (values : R → Nat) :
    (skip : Fragment R).RunsValues x 0 values values := by
  intro output
  rfl

private theorem addRegisterValue_eq (lane : R) (amount : Nat) (before : R → Nat) :
    addRegisterValue lane amount before = setValue lane (before lane + amount) before := by
  funext r
  by_cases h : r = lane <;> simp [addRegisterValue, setValue, h]

theorem runsValues_inputLength (lane : R) (x : BinaryWord) (before : R → Nat) :
    (inputLength lane).RunsValues x (2 * x.length + 1) before
      (setValue lane (before lane + x.length) before) := by
  intro output
  let cfg : Config R Unit := ⟨none, before, none, output⟩
  simpa only [cfg, addRegisterValue_eq] using run_inputLength lane x cfg rfl

theorem runsValues_incrementBy (lane : R) (amount : Nat) (x : BinaryWord) (before : R → Nat) :
    (incrementBy lane amount).RunsValues x amount before
      (setValue lane (before lane + amount) before) := by
  intro output
  let cfg : Config R Unit := ⟨none, before, none, output⟩
  simpa only [cfg, addRegisterValue_eq] using run_incrementBy lane amount x cfg

theorem runsValues_add (source target scratch : R) (x : BinaryWord) (before : R → Nat)
    (hST : source ≠ target) (hSW : source ≠ scratch) (hTW : target ≠ scratch)
    (hScratch : before scratch = 0) :
    (add source target scratch).RunsValues x (5 * before source + 2) before
      (setValue target (before target + before source) before) := by
  intro output
  let cfg : Config R Unit := ⟨none, before, none, output⟩
  have hRun := run_add source target scratch x cfg hST hSW hTW hScratch
  change (add source target scratch).run x (5 * before source + 2)
    ((add source target scratch).enter cfg) =
      some ⟨some none, addRegisterValue target (before source) before, none, output⟩ at hRun
  simpa only [cfg, addRegisterValue_eq] using hRun

theorem runsValues_multiply (multiplier multiplicand accumulator scratch : R)
    (x : BinaryWord) (before : R → Nat)
    (hMP : multiplier ≠ multiplicand) (hMA : multiplier ≠ accumulator)
    (hMS : multiplier ≠ scratch) (hPA : multiplicand ≠ accumulator)
    (hPS : multiplicand ≠ scratch) (hAS : accumulator ≠ scratch) (hScratch : before scratch = 0) :
    (multiply multiplier multiplicand accumulator scratch).RunsValues x
      (before multiplier * (5 * before multiplicand + 3) + 1) before
      (setValue accumulator (before accumulator + before multiplier * before multiplicand)
        (setValue multiplier 0 before)) := by
  intro output
  let cfg : Config R Unit := ⟨none, before, none, output⟩
  have hValues : multiplyValues multiplier multiplicand accumulator before =
      setValue accumulator (before accumulator + before multiplier * before multiplicand)
        (setValue multiplier 0 before) := by
    funext r
    by_cases hM : r = multiplier
    · simp [multiplyValues, setValue, hM, hMA]
    · by_cases hA : r = accumulator
      · subst r
        simp [multiplyValues, setValue, hMA.symm]
      · simp [multiplyValues, setValue, hM, hA]
  simpa only [cfg, hValues] using run_multiply multiplier multiplicand accumulator scratch x cfg
    hMP hMA hMS hPA hPS hAS hScratch

theorem runsValues_power (base result accumulator scratch : R) (exponent : Nat)
    (x : BinaryWord) (before : R → Nat)
    (hRB : result ≠ base) (hRA : result ≠ accumulator) (hRS : result ≠ scratch)
    (hBA : base ≠ accumulator) (hBS : base ≠ scratch) (hAS : accumulator ≠ scratch)
    (hResult : before result = 0) (hAcc : before accumulator = 0) (hScratch : before scratch = 0) :
    (power base result accumulator scratch exponent).RunsValues x
      (1 + powerTailTime (before base) 1 exponent) before
      (setValue result (before base ^ exponent) before) := by
  intro output
  let cfg : Config R Unit := ⟨none, before, none, output⟩
  exact RegisterMachine.run_power x hRB hRA hRS hBA hBS hAS
    (cfg := (power base result accumulator scratch exponent).enter cfg) rfl hResult hAcc hScratch

end PvsNP.RegisterMachine.Fragment
