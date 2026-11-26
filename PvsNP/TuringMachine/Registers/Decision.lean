module

public import PvsNP.TuringMachine.Registers.SimulationBound
public import PvsNP.Complexity.Reductions

import Mathlib.Data.Fintype.Option

/-! # Deciding a binary language with a counted register program -/

public section

namespace PvsNP.RegisterMachine

private def readAnswer : Machine Bool where
  State := Unit
  Symbol := Option Bool
  stateFinite := inferInstance
  symbolFinite := inferInstance
  initial := ()
  blank := none
  input := ⟨some, Option.some_injective _⟩
  input_ne_blank := Option.some_ne_none
  transition := fun _ symbol ↦ (.inr (symbol == some true), symbol, .right)

private theorem readAnswer_halt (word : BinaryWord) :
    (readAnswer.run 1 (readAnswer.start word)).state = .inr (word.head? == some true) := by
  cases word <;> rfl

private theorem readAnswer_polyTime : readAnswer.PolyTime := by
  refine ⟨1, fun word ↦ ⟨1, ?_, _, readAnswer_halt word⟩⟩
  simp only [Nat.pow_one]
  omega

private theorem readAnswer_decides :
    readAnswer.Decides {word : BinaryWord | word.head? = some true} := by
  intro word
  constructor
  · intro h
    exact ⟨1, (readAnswer_halt word).trans (congrArg Sum.inr (beq_iff_eq.mpr h))⟩
  · rintro ⟨t, h⟩
    exact beq_iff_eq.mp (readAnswer.halt_result_unique _ (readAnswer_halt word) h)

/-- A polynomial counted register run yielding `[true]` exactly on members gives a Cook decider. -/
theorem mem_P_of_boolean_run {R L : Type} [Finite R] [Finite L] [DecidableEq R]
    (entry : L) (program : L → Instruction R L) {accepts : BinaryWord → Bool}
    {bound : Nat → Nat} (hBound : PolynomiallyBounded bound)
    (hRun : ∀ x, ∃ steps ≤ bound x.length, ∃ cfg,
      run program x steps (Config.initial entry) = some cfg ∧ cfg.pc = none ∧
        cfg.output = [accepts x]) : {x : BinaryWord | accepts x = true} ∈ P := by
  let answerLanguage : BinaryLanguage := {word | word.head? = some true}
  have hDecide : answerLanguage ∈ P := ⟨readAnswer, readAnswer_polyTime, readAnswer_decides⟩
  have hMap : PolynomialTimeMap (fun x ↦ [accepts x]) :=
    polynomialTimeMap_of_run entry program hBound hRun
  refine PolynomiallyReducesTo.mem_P ⟨_, hMap, fun x ↦ ?_⟩ hDecide
  change accepts x = true ↔ some (accepts x) = some true
  exact ⟨congrArg some, Option.some.inj⟩

end PvsNP.RegisterMachine
