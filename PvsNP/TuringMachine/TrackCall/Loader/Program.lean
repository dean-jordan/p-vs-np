module

public import PvsNP.TuringMachine.TrackCall.Loader.Core

/-! # A concrete finite controller for the scratch loader -/

@[expose] public section

namespace PvsNP.TrackCall.Loader

inductive Phase where
  | seekLeft
  | turnAtLeft
  | writeForward
  | seekOrigin
  | invoke
  | reject
  | accept

theorem phaseFinite : Finite Phase := by
  refine Finite.intro (n := 7)
    { toFun := fun phase ↦ match phase with
        | .seekLeft => 0
        | .turnAtLeft => 1
        | .writeForward => 2
        | .seekOrigin => 3
        | .invoke => 4
        | .reject => 5
        | .accept => 6
      invFun := fun i ↦ match i.val with
        | 0 => .seekLeft
        | 1 => .turnAtLeft
        | 2 => .writeForward
        | 3 => .seekOrigin
        | 4 => .invoke
        | 5 => .reject
        | _ => .accept
      left_inv := by intro phase; cases phase <;> rfl
      right_inv := ?_ }
  rintro ⟨i, hi⟩
  have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

def programLabels : Labels Phase :=
  ⟨.seekLeft, .turnAtLeft, .writeForward, .seekOrigin, .invoke, .reject, .accept⟩

variable {α : Type} {D : Machine α} {ρ : Type}

/-- Fill scratch from the protected source and branch on the decision. -/
@[reducible] def program (layout : Layout D ρ) : Controller D ρ where
  State := Phase
  stateFinite := phaseFinite
  initial := .seekLeft
  transition phase cell :=
    match phase with
    | .seekLeft =>
      if layout.leftEdge cell.2.1 then (.jump .turnAtLeft, cell, .right)
      else (.jump .seekLeft, cell, .left)
    | .turnAtLeft => (.jump .writeForward, cell, .left)
    | .writeForward =>
      let written := (layout.load cell.2.1, cell.2)
      if layout.rightEdge cell.2.1 then (.jump .seekOrigin, written, .left)
      else (.jump .writeForward, written, .right)
    | .seekOrigin =>
      if cell.2.2 then (.jump .invoke, cell, .right)
      else (.jump .seekOrigin, cell, .left)
    | .invoke => (.call .reject .accept, cell, .left)
    | .reject => (.halt false, cell, .right)
    | .accept => (.halt true, cell, .right)

theorem program_rules (layout : Layout D ρ) : Rules (program layout) programLabels layout := by
  constructor <;> intro cell <;> rfl

end PvsNP.TrackCall.Loader
