module

public import PvsNP.SAT.QueryIterationRules
public import PvsNP.TuringMachine.TrackCall.Loader.Program

/-! # The finite controller for a SAT search iteration -/

public section

namespace PvsNP.SATSearch

open TrackCall TrackCall.QueryEdit Turing

inductive QueryCommitPhase where
  | seekSign
  | returnHome
  | turnHome

/-- The phases reached by the append, loader, and sign-commit operations. -/
inductive QueryIterationPhase where
  | seekTail
  | literal
  | sign
  | writeIndex
  | closeClause
  | closeFormula
  | returnHome
  | turnHome
  | seekLeft
  | turnAtLeft
  | loadForward
  | seekOrigin
  | invoke
  | commit (answer : Bool) (phase : QueryCommitPhase)
  | next

private def commitCode : QueryCommitPhase → Fin 3
  | .seekSign => 0
  | .returnHome => 1
  | .turnHome => 2

private theorem commitCode_injective : Function.Injective commitCode := by
  intro a b h
  cases a <;> cases b <;> simp_all [commitCode]

private def phaseCode : QueryIterationPhase → Fin 15 × Bool × Fin 3
  | .seekTail => (0, false, 0)
  | .literal => (1, false, 0)
  | .sign => (2, false, 0)
  | .writeIndex => (3, false, 0)
  | .closeClause => (4, false, 0)
  | .closeFormula => (5, false, 0)
  | .returnHome => (6, false, 0)
  | .turnHome => (7, false, 0)
  | .seekLeft => (8, false, 0)
  | .turnAtLeft => (9, false, 0)
  | .loadForward => (10, false, 0)
  | .seekOrigin => (11, false, 0)
  | .invoke => (12, false, 0)
  | .commit answer phase => (13, answer, commitCode phase)
  | .next => (14, false, 0)

instance : Finite QueryIterationPhase := Finite.of_injective phaseCode (by
  intro a b h
  cases a <;> cases b <;> simp_all [phaseCode, commitCode_injective.eq_iff])

@[expose] def queryIterationLabels : StepLabels QueryIterationPhase where
  append := ⟨.seekTail, .literal, .sign, .writeIndex, .closeClause, .closeFormula,
    .returnHome, .turnHome, .seekLeft⟩
  loader := ⟨.seekLeft, .turnAtLeft, .loadForward, .seekOrigin, .invoke,
    .commit false .seekSign, .commit true .seekSign⟩
  commit answer := ⟨.commit answer .seekSign, .commit answer .returnHome,
    .commit answer .turnHome, .next⟩
  next := .next

private def loaderLabel : Loader.Phase → QueryIterationPhase
  | .seekLeft => .seekLeft
  | .turnAtLeft => .turnAtLeft
  | .writeForward => .loadForward
  | .seekOrigin => .seekOrigin
  | .invoke => .invoke
  | .reject => .commit false .seekSign
  | .accept => .commit true .seekSign

variable {D : Machine Bool} {ρ : Type}

private def loaderStep (layout : Loader.Layout D (Cell ρ)) (phase : Loader.Phase)
    (cell : Symbol D (Cell ρ)) : Command QueryIterationPhase × Symbol D (Cell ρ) × Dir :=
  let (cmd, written, dir) := (Loader.program layout).transition phase cell
  let mapped := match cmd with
    | .jump next => .jump (loaderLabel next)
    | .call onFalse onTrue => .call (loaderLabel onFalse) (loaderLabel onTrue)
    | .halt answer => .halt answer
  (mapped, written, dir)

/-- Move between the three operations, committing the opposite of the trial decision. -/
def queryIterationTransition (stop : ρ → Bool) (layout : Loader.Layout D (Cell ρ)) :
    QueryIterationPhase → Symbol D (Cell ρ) →
      Command QueryIterationPhase × Symbol D (Cell ρ) × Dir
  | .seekTail, cell =>
    if tail cell.2.1 then (.jump .literal, editSymbol cell clauseStart, .right)
    else (.jump .seekTail, cell, .right)
  | .literal, cell => (.jump .sign, editSymbol cell literalStart, .right)
  | .sign, cell => (.jump .writeIndex, editSymbol cell trialSign, .right)
  | .writeIndex, cell =>
    if stop cell.2.1.1 then (.jump .closeClause, editSymbol cell indexEnd, .right)
    else (.jump .writeIndex, editSymbol cell indexOne, .right)
  | .closeClause, cell => (.jump .closeFormula, editSymbol cell clauseEnd, .right)
  | .closeFormula, cell => (.jump .returnHome, editSymbol cell formulaEnd, .right)
  | .returnHome, cell =>
    if cell.2.2 then (.jump .turnHome, cell, .right)
    else (.jump .returnHome, cell, .left)
  | .turnHome, cell => (.jump .seekLeft, cell, .left)
  | .seekLeft, cell => loaderStep layout .seekLeft cell
  | .turnAtLeft, cell => loaderStep layout .turnAtLeft cell
  | .loadForward, cell => loaderStep layout .writeForward cell
  | .seekOrigin, cell => loaderStep layout .seekOrigin cell
  | .invoke, cell => loaderStep layout .invoke cell
  | .commit answer .seekSign, cell =>
    if pending cell.2.1 then
      (.jump (.commit answer .returnHome), editSymbol cell (ordinary (!answer)), .left)
    else (.jump (.commit answer .seekSign), cell, .right)
  | .commit answer .returnHome, cell =>
    if cell.2.2 then (.jump (.commit answer .turnHome), cell, .right)
    else (.jump (.commit answer .returnHome), cell, .left)
  | .commit _ .turnHome, cell => (.jump .next, cell, .left)
  | .next, cell => (.halt true, cell, .right)

/-- A finite linked controller implementing one iteration. -/
@[expose, reducible] def queryIterationProgram (D : Machine Bool) (stop : ρ → Bool)
    (layout : Loader.Layout D (Cell ρ)) : Controller D (Cell ρ) where
  State := QueryIterationPhase
  stateFinite := inferInstance
  initial := .seekTail
  transition := queryIterationTransition stop layout

theorem queryIterationProgram_rules (D : Machine Bool) (stop : ρ → Bool)
    (layout : Loader.Layout D (Cell ρ)) :
    StepRules (queryIterationProgram D stop layout) queryIterationLabels stop layout := by
  refine ⟨?_, ?_, ?_, rfl, ?_, fun _ ↦ rfl⟩
  · constructor <;> intro cell <;> rfl
  · constructor <;> intro cell
    · by_cases h : layout.leftEdge cell.2.1 = true <;>
        simp [queryIterationProgram, queryIterationLabels, queryIterationTransition,
          loaderStep, loaderLabel, h]
    · rfl
    · by_cases h : layout.rightEdge cell.2.1 = true <;>
        simp [queryIterationProgram, queryIterationLabels, queryIterationTransition,
          loaderStep, loaderLabel, h]
    · by_cases h : cell.2.2 = true <;>
        simp [queryIterationProgram, queryIterationLabels, queryIterationTransition,
          loaderStep, loaderLabel, h]
    · rfl
  · intro answer
    constructor <;> intro cell <;> rfl
  · intro answer
    cases answer <;> rfl

/-- The continuation after a commit is the next iteration's first scan. -/
@[expose] def loopIterationLabels : StepLabels QueryIterationPhase :=
  { queryIterationLabels with
    commit := fun answer ↦ { queryIterationLabels.commit answer with afterCommit := .seekTail }
    next := .seekTail }

/-- A controller that returns to the initial scan after each commit. -/
@[expose, reducible] def loopIterationProgram (D : Machine Bool) (stop : ρ → Bool)
    (layout : Loader.Layout D (Cell ρ)) : Controller D (Cell ρ) :=
  { queryIterationProgram D stop layout with
    transition := fun phase cell ↦ match phase with
      | .commit _ .turnHome => (.jump .seekTail, cell, .left)
      | _ => queryIterationTransition stop layout phase cell }

theorem loopIterationProgram_rules (D : Machine Bool) (stop : ρ → Bool)
    (layout : Loader.Layout D (Cell ρ)) :
    StepRules (loopIterationProgram D stop layout) loopIterationLabels stop layout := by
  have base := queryIterationProgram_rules D stop layout
  refine ⟨?_, ?_, ?_, base.loadLabel, base.commitLabel, fun _ ↦ rfl⟩
  · exact ⟨base.appendRules.seekTail, base.appendRules.literal, base.appendRules.sign,
      base.appendRules.writeIndex, base.appendRules.closeClause, base.appendRules.closeFormula,
      base.appendRules.returnHome, base.appendRules.turnHome⟩
  · exact ⟨base.loaderRules.seekLeft, base.loaderRules.turnAtLeft, base.loaderRules.writeForward,
      base.loaderRules.seekOrigin, base.loaderRules.invoke⟩
  · intro answer
    exact ⟨(base.commitRules answer).seekSign, (base.commitRules answer).returnHome, fun _ ↦ rfl⟩

theorem loopIterationLabels_next_eq_seekTail :
    loopIterationLabels.next = loopIterationLabels.append.seekTail := rfl

end PvsNP.SATSearch
