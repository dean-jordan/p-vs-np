module

public import PvsNP.TuringMachine.TrackCall.QueryEdit.Append
public import PvsNP.TuringMachine.TrackCall.QueryEdit.Commit
public import PvsNP.TuringMachine.TrackCall.QueryEdit.LoaderBridge

/-! # Append, decide, and commit a unit clause on one Cook tape -/

@[expose] public section

namespace PvsNP.SATSearch

open TrackCall TrackCall.QueryEdit Turing

/-- The controller enters the loader after appending the trial clause. Each
decider return label selects a sign edit and then reaches the next stage. -/
structure StepLabels (Q : Type) where
  append : QueryEdit.Labels Q
  loader : Loader.Labels Q
  commit : Bool → CommitLabels Q
  next : Q

variable {D : Machine Bool} {ρ : Type} [Finite ρ] [Inhabited ρ]

structure StepRules (C : Controller D (Cell ρ)) (labels : StepLabels C.State)
    (stop : ρ → Bool) (layout : Loader.Layout D (Cell ρ)) : Prop where
  appendRules : QueryEdit.Rules C labels.append stop
  loaderRules : Loader.Rules C labels.loader layout
  commitRules : ∀ answer, CommitRules C (labels.commit answer) (!answer)
  loadLabel : labels.append.afterAppend = labels.loader.seekLeft
  commitLabel : ∀ answer,
    C.resume labels.loader.reject labels.loader.accept answer = (labels.commit answer).seekSign
  nextLabel : ∀ answer, (labels.commit answer).afterCommit = labels.next

/-- Bound the append, loaded call, and sign commit at terminator index `j`. -/
def queryStepBound (j i L R clock : Nat) : Nat :=
  (2 * (j + i + 6) + 2) + (2 * (L + R) + 2 * clock + 6) + (2 * (j + 2) + 2)

end PvsNP.SATSearch
