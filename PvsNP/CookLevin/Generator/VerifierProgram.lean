module

public import PvsNP.CookLevin.Generator.Blocks
public import PvsNP.CookLevin.Generator.InitialSection
public import PvsNP.CookLevin.Generator.RegisterReduction
public import PvsNP.CookLevin.Generator.Steps

import Mathlib.Tactic.DeriveFintype

/-! # The complete indexed verifier tableau generator -/

@[expose] public section

namespace PvsNP.CookLevin

open RegisterMachine RegisterMachine.Fragment

/-- Share the persistent parameters between the sections of the register generator. -/
structure VerifierProgramLayout (R : Type) where
  parameters : ParameterLane ↪ R
  acceptingIndex : R
  steps : StepSectionLane ↪ R
  rows : RowLane ↪ R
  initial : InitialSectionLane ↪ R
  acceptingFresh : ∀ lane, acceptingIndex ≠ parameters lane
  stepStride : steps (.parameter .stride) = parameters .stride
  stepWidth : steps (.parameter .width) = parameters .width
  stepFresh : ∀ lane, lane ≠ .parameter .stride → lane ≠ .parameter .width →
    ∀ p, steps lane ≠ parameters p
  rowStride : rows .stride = parameters .stride
  rowWidth : rows .width = parameters .width
  rowFresh : ∀ lane, lane ≠ .stride → lane ≠ .width → ∀ p, rows lane ≠ parameters p
  initialLength : initial .length = parameters .length
  initialOffset : initial .offset = parameters .horizon
  initialCapacity : initial .capacity = parameters .capacity
  initialWidth : initial .width = parameters .width
  initialFresh : ∀ lane, lane ∉ [.length, .offset, .capacity, .width] →
    ∀ p, initial lane ≠ parameters p

variable {R : Type} {states symbols certificates : Nat}

/-- Emit the accepting suffix, transitions, rows, and initial clauses in order. -/
def verifierProgram (layout : VerifierProgramLayout R)
    (table : FiniteTable states symbols certificates) (k d : Nat) : Fragment R :=
  let prefixProgram := table.generatorPrefix layout.parameters layout.acceptingIndex k d
  let transitions := stepsFragment layout.steps (layout.parameters .horizon) table
  let rows := rowsFragment layout.rows (layout.parameters .horizon) states symbols
  ((prefixProgram.seq transitions).seq rows).seq (initialSectionFragment layout.initial table)

/-- A uniform instruction budget, including the final abstract halt. -/
def verifierProgramTimeBound [DecidableEq R] (layout : VerifierProgramLayout R)
    (table : FiniteTable states symbols certificates) (n k d : Nat) : Nat :=
  let t := horizon n k d
  let width := 2 * t + 1
  let stride := Tableau.atomStride states width symbols
  let v := parameterValues layout.parameters n k d states symbols
  table.generatorPrefixTime n k d + stepsTimeBound states symbols width stride t +
    rowsTimeBound layout.rows (layout.parameters .horizon) v states symbols +
    initialSectionTimeBound table n t (n ^ k) width + 1

/-- Each section contributes a polynomial term to the complete budget. -/
theorem verifierProgramTimeBound_polynomiallyBounded [DecidableEq R]
    (layout : VerifierProgramLayout R) (table : FiniteTable states symbols certificates)
    (k d : Nat) : PolynomiallyBounded (fun n ↦ verifierProgramTimeBound layout table n k d) := by
  let constant := PolynomiallyBounded.const
  have hTime := horizon_polynomiallyBounded k d
  have hWidth := ((constant 2).mul hTime).add (constant 1)
  have hStride := ((constant states).add hWidth).add (hWidth.mul (constant symbols))
  let values (n : Nat) := parameterValues layout.parameters n k d states symbols
  have hRowTime : PolynomiallyBounded (fun n ↦ values n (layout.parameters .horizon)) := by
    simpa only [values, parameterValues_at] using hTime
  have hRowWidth : PolynomiallyBounded (fun n ↦ values n (layout.rows .width)) := by
    simpa only [values, layout.rowWidth, parameterValues_at] using hWidth
  have hRowStride : PolynomiallyBounded (fun n ↦ values n (layout.rows .stride)) := by
    simpa only [values, layout.rowStride, parameterValues_at, Tableau.atomStride] using hStride
  have hRows := rowsTimeBound_polynomiallyBounded layout.rows (layout.parameters .horizon)
    states symbols hRowTime hRowStride hRowWidth
  have hSteps := stepsTimeBound_polynomiallyBounded states symbols hWidth hStride hTime
  have hInitial := initialSectionTimeBound_polynomiallyBounded table PolynomiallyBounded.id
    hTime (PolynomiallyBounded.id.pow k) hWidth
  exact ((((table.generatorPrefixTime_polynomiallyBounded k d).add hSteps).add hRows).add
    hInitial).add (constant 1)

private theorem verifierStepHorizonFresh (layout : VerifierProgramLayout R) :
    ∀ lane, layout.parameters .horizon ≠ layout.steps lane := by
  intro lane
  by_cases hs : lane = .parameter .stride
  · rw [hs, layout.stepStride]
    exact layout.parameters.injective.ne (by decide)
  by_cases hw : lane = .parameter .width
  · rw [hw, layout.stepWidth]
    exact layout.parameters.injective.ne (by decide)
  exact (layout.stepFresh lane hs hw .horizon).symm

private theorem verifierRowHorizonFresh (layout : VerifierProgramLayout R) :
    ∀ lane, layout.parameters .horizon ≠ layout.rows lane := by
  intro lane
  by_cases hs : lane = .stride
  · rw [hs, layout.rowStride]
    exact layout.parameters.injective.ne (by decide)
  by_cases hw : lane = .width
  · rw [hw, layout.rowWidth]
    exact layout.parameters.injective.ne (by decide)
  exact (layout.rowFresh lane hs hw .horizon).symm

/-- From zero registers, the linked fragment prepends the exact indexed binary verifier map. -/
theorem runsOutput_verifierProgram [DecidableEq R] (layout : VerifierProgramLayout R)
    (table : FiniteTable states symbols certificates) (x suffix : BinaryWord) (k d : Nat) :
    ∃ cost, cost + 1 ≤ verifierProgramTimeBound layout table x.length k d ∧
      (verifierProgram layout table k d).RunsOutput x cost (fun _ ↦ 0)
        (initialSectionValues layout.initial states
          (parameterValues layout.parameters x.length k d states symbols))
        suffix (table.binaryVerifierMap x k d ++ suffix) := by
  let t := horizon x.length k d
  let width := 2 * t + 1
  let stride := Tableau.atomStride states width symbols
  let v := parameterValues layout.parameters x.length k d states symbols
  let accepted := table.acceptanceCode x.length k d ++ suffix
  let transitions := table.transitionOutput width t accepted
  let rows := tableauRowsOutput states symbols width stride t transitions
  have hPrefix : (table.generatorPrefix layout.parameters layout.acceptingIndex k d).RunsOutput x
      (table.generatorPrefixTime x.length k d) (fun _ ↦ 0) v suffix accepted :=
    table.run_generatorPrefix layout.parameters layout.acceptingIndex layout.acceptingFresh
      x k d suffix
  have hp := parameterValues_at layout.parameters x.length k d states symbols
  have hHorizon : v (layout.parameters .horizon) = t := hp .horizon
  have hStepWidth : v (layout.steps (.parameter .width)) = width := by
    rw [layout.stepWidth]
    exact hp .width
  have hStepStride : v (layout.steps (.parameter .stride)) = stride := by
    rw [layout.stepStride]
    exact hp .stride
  have hStepStride' : v (layout.steps (.parameter .stride)) =
      Tableau.atomStride states (v (layout.steps (.parameter .width))) symbols := by
    rw [hStepWidth]
    exact hStepStride
  have hZero (r : R) (hf : ∀ lane, r ≠ layout.parameters lane) : v r = 0 :=
    parameterValues_outside layout.parameters x.length k d states symbols r hf
  have hStepTime : v (layout.steps (.parameter .time)) = 0 :=
    hZero _ (layout.stepFresh _ (by decide) (by decide))
  have hStepsReady : StepSectionReady layout.steps v :=
    fun lane _ hs hw ↦ hZero _ (layout.stepFresh lane hs hw)
  obtain ⟨stepCost, hStepCost, hSteps⟩ := run_stepsFragment layout.steps
    (layout.parameters .horizon) table x accepted v (verifierStepHorizonFresh layout)
    hStepTime hStepStride' hStepsReady
  rw [hStepWidth, hStepStride, hHorizon] at hStepCost
  rw [hStepWidth, hHorizon] at hSteps
  have rowZero (lane : RowLane) (hs : lane ≠ .stride) (hw : lane ≠ .width) :
      v (layout.rows lane) = 0 := hZero _ (layout.rowFresh lane hs hw)
  have hRowsReady : RowReady layout.rows v :=
    ⟨⟨rowZero (.field .base) (by decide) (by decide),
      rowZero (.field .count) (by decide) (by decide),
      rowZero .multiplier (by decide) (by decide),
      rowZero .preparationScratch (by decide) (by decide)⟩,
      ⟨rowZero (.field .index) (by decide) (by decide),
        rowZero (.field .additionScratch) (by decide) (by decide),
        rowZero (.field .leftCopy) (by decide) (by decide),
        rowZero (.field .rightCopy) (by decide) (by decide),
        rowZero (.field .comparisonScratch) (by decide) (by decide)⟩,
      rowZero (.field .left) (by decide) (by decide),
      rowZero (.field .right) (by decide) (by decide)⟩
  have hRowTime : v (layout.rows .time) = 0 := rowZero .time (by decide) (by decide)
  have hPosition : v (layout.rows .position) = 0 := rowZero .position (by decide) (by decide)
  have hRowWidth : v (layout.rows .width) = width := by rw [layout.rowWidth]; exact hp .width
  have hRowStride : v (layout.rows .stride) = stride := by rw [layout.rowStride]; exact hp .stride
  obtain ⟨rowCost, hRowCost, hRows⟩ := run_rowsFragment layout.rows
    (layout.parameters .horizon) states symbols x transitions v (verifierRowHorizonFresh layout)
    hRowTime hRowsReady hPosition
  rw [hRowWidth, hRowStride, hHorizon] at hRows
  have hInitLength : v (layout.initial .length) = x.length := by
    rw [layout.initialLength]
    exact hp .length
  have hInitOffset : v (layout.initial .offset) = t := by rw [layout.initialOffset]; exact hHorizon
  have hInitCapacity : v (layout.initial .capacity) = x.length ^ k := by
    rw [layout.initialCapacity]
    exact hp .capacity
  have hInitWidth : v (layout.initial .width) = width := by
    rw [layout.initialWidth]
    exact hp .width
  have hInitialReady : InitialSectionReady layout.initial v :=
    fun lane h ↦ hZero _ (layout.initialFresh lane h)
  obtain ⟨initCost, hInitCost, hInitial⟩ := run_initialSectionWindow layout.initial table
    x rows (x.length ^ k) t v hInitLength hInitOffset hInitCapacity hInitWidth hInitialReady
  have hInitBudget : initCost ≤ initialSectionTimeBound table x.length t (x.length ^ k) width :=
    hInitCost
  have hWord : initialSectionOutput table x rows (Machine.windowCenter t) (x.length ^ k) =
      table.binaryVerifierMap x k d ++ suffix :=
    (table.binaryVerifierMap_eq_sections x k d suffix).symm
  rw [hWord] at hInitial
  refine ⟨table.generatorPrefixTime x.length k d + stepCost + rowCost + initCost, ?_, ?_⟩
  · change _ ≤ table.generatorPrefixTime x.length k d +
      stepsTimeBound states symbols width stride t +
      rowsTimeBound layout.rows (layout.parameters .horizon) v states symbols +
      initialSectionTimeBound table x.length t (x.length ^ k) width + 1
    omega
  · exact ((hPrefix.seq hSteps).seq hRows).seq hInitial

/-- Close the fragment with an abstract halt after the last bit has been emitted. -/
theorem run_verifierProgram [DecidableEq R] (layout : VerifierProgramLayout R)
    (table : FiniteTable states symbols certificates) (x : BinaryWord) (k d : Nat) :
    let f := verifierProgram layout table k d
    ∃ cost ≤ verifierProgramTimeBound layout table x.length k d, ∃ cfg,
      RegisterMachine.run f.close x cost (Config.initial f.entry) = some cfg ∧
      cfg.pc = none ∧ cfg.output = table.binaryVerifierMap x k d := by
  let f := verifierProgram layout table k d
  let done : f.Cfg := ⟨some none,
    initialSectionValues layout.initial states
      (parameterValues layout.parameters x.length k d states symbols),
    none, table.binaryVerifierMap x k d⟩
  obtain ⟨cost, hCost, hRun⟩ := runsOutput_verifierProgram layout table x [] k d
  have hLive : f.run x cost (Config.initial f.entry) = some done := by
    simpa only [RunsOutput, enter, Config.initial, List.append_nil, done, f] using hRun
  exact ⟨cost + 1, hCost, { done with pc := none }, run_close hLive rfl rfl, rfl, rfl⟩

local instance : Fintype ParameterLane := derive_fintype% _
local instance : Fintype StepPreparationLane := derive_fintype% _
local instance : Fintype StepCopyLane := derive_fintype% _
local instance : Fintype StepUpdateLane := derive_fintype% _
local instance : Fintype StepSectionLane := derive_fintype% _
local instance : Fintype ExactlyOneLane := derive_fintype% _
local instance : Fintype RowLane := derive_fintype% _
local instance : Fintype InitialSectionLane := derive_fintype% _

/-- A finite tagged allocation, with common size parameters shared by every section. -/
inductive VerifierRegister where
  | parameter (lane : ParameterLane)
  | acceptingIndex
  | step (lane : StepSectionLane)
  | row (lane : RowLane)
  | initial (lane : InitialSectionLane)
  deriving DecidableEq, Fintype

/-- Share width and stride with the transition section. -/
def verifierStepRegister : StepSectionLane → VerifierRegister
  | .parameter .stride => .parameter .stride
  | .parameter .width => .parameter .width
  | lane => .step lane

/-- Share width and stride with the exactly-one row section. -/
def verifierRowRegister : RowLane → VerifierRegister
  | .stride => .parameter .stride
  | .width => .parameter .width
  | lane => .row lane

/-- The initial head offset equals the horizon, the center of the window. -/
def verifierInitialRegister : InitialSectionLane → VerifierRegister
  | .length => .parameter .length
  | .offset => .parameter .horizon
  | .capacity => .parameter .capacity
  | .width => .parameter .width
  | lane => .initial lane

private theorem verifierStepRegister_injective : Function.Injective verifierStepRegister := by
  let decode : VerifierRegister → Option StepSectionLane
    | .parameter .stride => some (.parameter .stride)
    | .parameter .width => some (.parameter .width)
    | .step lane => some lane
    | _ => none
  have recover (lane : StepSectionLane) : decode (verifierStepRegister lane) = some lane := by
    cases lane with
    | parameter lane => cases lane <;> rfl
    | copy => rfl
    | update => rfl
  intro a b h
  have hDecoded := congrArg decode h
  rwa [recover, recover, Option.some.injEq] at hDecoded

private theorem verifierRowRegister_injective : Function.Injective verifierRowRegister := by
  let decode : VerifierRegister → Option RowLane
    | .parameter .stride => some .stride
    | .parameter .width => some .width
    | .row lane => some lane
    | _ => none
  have recover (lane : RowLane) : decode (verifierRowRegister lane) = some lane := by
    cases lane <;> rfl
  intro a b h
  have hDecoded := congrArg decode h
  rwa [recover, recover, Option.some.injEq] at hDecoded

private theorem verifierInitialRegister_injective : Function.Injective verifierInitialRegister := by
  let decode : VerifierRegister → Option InitialSectionLane
    | .parameter .length => some .length
    | .parameter .horizon => some .offset
    | .parameter .capacity => some .capacity
    | .parameter .width => some .width
    | .initial lane => some lane
    | _ => none
  have recover (lane : InitialSectionLane) : decode (verifierInitialRegister lane) = some lane := by
    cases lane <;> rfl
  intro a b h
  have hDecoded := congrArg decode h
  rwa [recover, recover, Option.some.injEq] at hDecoded

/-- The concrete layout used by the indexed tableau transducer. -/
def verifierRegisterLayout : VerifierProgramLayout VerifierRegister where
  parameters := ⟨VerifierRegister.parameter, fun _ _ h ↦ VerifierRegister.parameter.inj h⟩
  acceptingIndex := .acceptingIndex
  steps := ⟨verifierStepRegister, by exact verifierStepRegister_injective⟩
  rows := ⟨verifierRowRegister, by exact verifierRowRegister_injective⟩
  initial := ⟨verifierInitialRegister, by exact verifierInitialRegister_injective⟩
  acceptingFresh := by intro lane h; cases h
  stepStride := rfl
  stepWidth := rfl
  stepFresh := by
    intro lane hs hw p
    change verifierStepRegister lane ≠ .parameter p
    cases lane with
    | parameter lane => cases lane <;> simp_all [verifierStepRegister]
    | copy => simp [verifierStepRegister]
    | update => simp [verifierStepRegister]
  rowStride := rfl
  rowWidth := rfl
  rowFresh := by
    intro lane hs hw p
    change verifierRowRegister lane ≠ .parameter p
    cases lane <;> simp_all [verifierRowRegister]
  initialLength := rfl
  initialOffset := rfl
  initialCapacity := rfl
  initialWidth := rfl
  initialFresh := by
    intro lane h p
    change verifierInitialRegister lane ≠ .parameter p
    cases lane <;> simp_all [verifierInitialRegister]

/-- The exact binary tableau reduction is polynomial-time in Cook's machine model. -/
theorem binaryTableauxPolyTime_verified : BinaryTableauxPolyTime := by
  apply binaryTableauxPolyTime_of_registers
  intro states symbols certificates table k d
  let f := verifierProgram verifierRegisterLayout table k d
  refine ⟨VerifierRegister, Option f.Label, inferInstance, inferInstance, inferInstance,
    f.entry, f.close, (fun n ↦ verifierProgramTimeBound verifierRegisterLayout table n k d),
    verifierProgramTimeBound_polynomiallyBounded verifierRegisterLayout table k d, ?_⟩
  intro x
  exact run_verifierProgram verifierRegisterLayout table x k d

end PvsNP.CookLevin
