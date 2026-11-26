module

public import PvsNP.TuringMachine.Registers.OutputRuns

/-! # Preserving branch on a register's positivity -/

@[expose] public section

namespace PvsNP.RegisterMachine.Fragment

variable {R K : Type}

abbrev IfRegisterPositiveLabel (positive zero : Fragment R) :=
  Bool ⊕ (positive.Label ⊕ zero.Label)

abbrev ifRegisterPositiveThenLabel (positive zero : Fragment R) :
    Option positive.Label → Option (IfRegisterPositiveLabel positive zero) :=
  Option.map (fun label ↦ .inr (.inl label))

abbrev ifRegisterPositiveElseLabel (positive zero : Fragment R) :
    Option zero.Label → Option (IfRegisterPositiveLabel positive zero) :=
  Option.map (fun label ↦ .inr (.inr label))

/-- Test for zero and restore a decremented register before entering the positive branch. -/
abbrev ifRegisterPositive (lane : R) (positive zero : Fragment R) : Fragment R where
  Label := IfRegisterPositiveLabel positive zero
  entry := some (.inl false)
  code
    | .inl false => .dec lane (ifRegisterPositiveElseLabel positive zero zero.entry)
        (some (.inl true))
    | .inl true => .inc lane (ifRegisterPositiveThenLabel positive zero positive.entry)
    | .inr (.inl label) => (positive.code label).map (ifRegisterPositiveThenLabel positive zero)
    | .inr (.inr label) => (zero.code label).map (ifRegisterPositiveElseLabel positive zero)

/-- Only the positive path needs to restore the tested register. -/
def ifRegisterPositiveTime (value : Nat) : Nat := if 0 < value then 2 else 1

theorem ifRegisterPositiveTime_le (value : Nat) : ifRegisterPositiveTime value ≤ 2 := by
  unfold ifRegisterPositiveTime
  split <;> decide

variable [DecidableEq R]

private theorem increment_decrement_of_pos (lane : R) (values : R → Nat)
    (hPos : 0 < values lane) : incrementValues lane (decrementValues lane values) = values := by
  funext r
  by_cases h : r = lane
  · subst r
    simp [incrementValues, decrementValues, Nat.sub_add_cancel hPos]
  · simp [incrementValues, decrementValues, h]

private theorem run_ifRegisterPositive_test (lane : R) (positive zero : Fragment R)
    (x : BinaryWord) (cfg : Config R K) :
    let test := ifRegisterPositive lane positive zero
    test.run x (ifRegisterPositiveTime (cfg.values lane)) (test.enter cfg) =
      some ⟨some (if 0 < cfg.values lane then
        ifRegisterPositiveThenLabel positive zero positive.entry
        else ifRegisterPositiveElseLabel positive zero zero.entry),
        cfg.values, cfg.cursor, cfg.output⟩ := by
  let test := ifRegisterPositive lane positive zero
  let start := test.enter cfg
  change RegisterMachine.run test.close x (ifRegisterPositiveTime (cfg.values lane)) start =
    some ⟨some (if 0 < cfg.values lane then
      ifRegisterPositiveThenLabel positive zero positive.entry
      else ifRegisterPositiveElseLabel positive zero zero.entry),
      cfg.values, cfg.cursor, cfg.output⟩
  by_cases hPos : 0 < cfg.values lane
  · let mid : test.Cfg :=
      ⟨some (some (.inl true)), decrementValues lane cfg.values, cfg.cursor, cfg.output⟩
    have hTake : step test.close x start = some mid :=
      step_dec_pos (label := some (.inl false))
        (zero := ifRegisterPositiveElseLabel positive zero zero.entry)
        rfl rfl hPos
    have hRestore := step_inc (program := test.close) (x := x) (cfg := mid)
      (label := some (.inl true)) (reg := lane)
      (next := ifRegisterPositiveThenLabel positive zero positive.entry) rfl rfl
    rw [ifRegisterPositiveTime, ite_eq_left hPos, ite_eq_left hPos,
      show (2 : Nat) = (0 + 1) + 1 by rfl, RegisterMachine.run_succ, hTake, Option.bind_some,
      RegisterMachine.run_succ, hRestore, Option.bind_some, RegisterMachine.run_zero]
    simp only [mid, increment_decrement_of_pos lane cfg.values hPos]
  · have hZero : cfg.values lane = 0 := Nat.eq_zero_of_not_pos hPos
    have hTake := step_dec_zero (program := test.close) (x := x) (cfg := start)
      (label := some (.inl false)) (next := some (.inl true)) rfl rfl hZero
    rw [ifRegisterPositiveTime, ite_eq_right hPos, ite_eq_right hPos,
      show (1 : Nat) = 0 + 1 by rfl, RegisterMachine.run_succ, hTake, Option.bind_some,
      RegisterMachine.run_zero]
    rfl

/-- Execute the selected branch after the exact test cost, with its own valuation and output. -/
theorem runsOutput_ifRegisterPositive (lane : R) (positive zero : Fragment R)
    (x : BinaryWord) (before : R → Nat) {ticks : Nat} {after : R → Nat}
    {suffix output : BinaryWord}
    (hRun : (if 0 < before lane then positive else zero).RunsOutput
      x ticks before after suffix output) :
    (ifRegisterPositive lane positive zero).RunsOutput
      x (ifRegisterPositiveTime (before lane) + ticks) before after suffix output := by
  let cfg : Config R Unit := ⟨none, before, none, suffix⟩
  let test := ifRegisterPositive lane positive zero
  have hTest := run_ifRegisterPositive_test lane positive zero x cfg
  change RegisterMachine.run test.close x (ifRegisterPositiveTime (before lane)) (test.enter cfg) =
    some ⟨some (if 0 < before lane then ifRegisterPositiveThenLabel positive zero positive.entry
      else ifRegisterPositiveElseLabel positive zero zero.entry), before, none, suffix⟩ at hTest
  change RegisterMachine.run test.close x _ (test.enter cfg) = _
  rw [RegisterMachine.run_add, hTest, Option.bind_some]
  by_cases hPos : 0 < before lane
  · simp only [ite_eq_left hPos] at hRun ⊢
    exact run_link (ifRegisterPositiveThenLabel positive zero) (target := test.close)
      (fun _ ↦ rfl) hRun rfl
  · simp only [ite_eq_right hPos] at hRun ⊢
    exact run_link (ifRegisterPositiveElseLabel positive zero) (target := test.close)
      (fun _ ↦ rfl) hRun rfl

/-- A branch known to preserve its output suffix has the same exact test charge. -/
theorem runsValues_ifRegisterPositive (lane : R) (positive zero : Fragment R)
    (x : BinaryWord) (before : R → Nat) {ticks : Nat} {after : R → Nat}
    (hRun : (if 0 < before lane then positive else zero).RunsValues x ticks before after) :
    (ifRegisterPositive lane positive zero).RunsValues
      x (ifRegisterPositiveTime (before lane) + ticks) before after :=
  fun suffix ↦ runsOutput_ifRegisterPositive lane positive zero x before (hRun suffix)

end PvsNP.RegisterMachine.Fragment
