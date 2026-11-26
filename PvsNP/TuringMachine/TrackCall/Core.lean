module

public import PvsNP.TuringMachine.Core

import Mathlib.Basic.Finite.Prod
import Mathlib.Basic.Finite.Sum

/-! # A returning Cook subroutine on a scratch track -/

@[expose] public section

namespace PvsNP.TrackCall

open Turing

/-- The symbol read by the subroutine, a protected symbol, and an origin marker. -/
abbrev Symbol {α : Type} (D : Machine α) (ρ : Type) := D.Symbol × ρ × Bool

/-- The outer right summand is the final step from just right of the origin. -/
abbrev State (Q : Type) := ((Q ⊕ Bool) × Bool) ⊕ Bool

def executing {Q : Type} (q : Q) (side : Bool) : State Q := .inl (.inl q, side)

def rewinding {Q : Type} (answer side : Bool) : State Q := .inl (.inr answer, side)

def finishing {Q : Type} (answer : Bool) : State Q := .inr answer

/-- A child halt hands its result to the rewind phase. -/
def phaseState {Q : Type} (state : Q ⊕ Bool) (side : Bool) : State Q :=
  match state with
  | .inl q => executing q side
  | .inr answer => rewinding answer side

/-- The change in absolute head position due to one physical move. -/
def delta : Dir → Int
  | .left => -1
  | .right => 1

/-- Off the origin, true records the right side and false records the left.
At the origin the marker determines the next side. -/
def SideAt (side : Bool) (pos : Int) : Prop :=
  (0 < pos → side = true) ∧ (pos < 0 → side = false)

theorem sideAt_zero (side : Bool) : SideAt side 0 := by
  simp [SideAt]

/-- Only a move from the marked cell can change the recorded side. -/
def advanceSide (origin side : Bool) (dir : Dir) : Bool :=
  if origin then
    match dir with
    | .left => false
    | .right => true
  else side

theorem sideAt_advanceSide {side : Bool} {pos : Int} (h : SideAt side pos) (dir : Dir) :
    SideAt (advanceSide (decide (pos = 0)) side dir) (pos + delta dir) := by
  by_cases hZero : pos = 0
  · subst pos
    cases dir <;> simp [SideAt, advanceSide, delta]
  · have hKeep : advanceSide (decide (pos = 0)) side dir = side := by
      simp [advanceSide, hZero]
    rw [hKeep]
    constructor
    · intro hPos
      apply h.1
      cases dir <;> simp only [delta] at hPos <;> omega
    · intro hNeg
      apply h.2
      cases dir <;> simp only [delta] at hNeg <;> omega

theorem natAbs_add_delta_le (pos : Int) (dir : Dir) :
    (pos + delta dir).natAbs ≤ pos.natAbs + 1 := by
  have h := Int.natAbs_add_le pos (delta dir)
  cases dir <;> exact h

/-- Run the child on the scratch field. Once it halts, move toward the
origin, then make a right-left pair of moves to halt on the marked cell. -/
def transition {α : Type} (D : Machine α) {ρ : Type}
    (state : State D.State) (cell : Symbol D ρ) : (State D.State ⊕ Bool) × Symbol D ρ × Dir :=
  match state with
  | .inl (.inl q, side) =>
    let (next, sym, dir) := D.transition q cell.1
    (.inl (phaseState next (advanceSide cell.2.2 side dir)), (sym, cell.2), dir)
  | .inl (.inr answer, side) =>
    if cell.2.2 then (.inl (finishing answer), cell, .right)
    else (.inl (rewinding answer side), cell, if side then .left else .right)
  | .inr answer => (.inr answer, cell, .left)

/-- A single-tape Cook machine over the product alphabet. Returning calls
enter it with their query and origin marker already installed. -/
@[reducible] def machine {α : Type} (D : Machine α) (ρ : Type)
    [Finite ρ] [Inhabited ρ] : Machine α := by
  let _ : Finite D.State := D.stateFinite
  let _ : Finite D.Symbol := D.symbolFinite
  exact {
    State := State D.State
    Symbol := Symbol D ρ
    stateFinite := by
      change Finite (((D.State ⊕ Bool) × Bool) ⊕ Bool)
      infer_instance
    symbolFinite := by
      change Finite (D.Symbol × ρ × Bool)
      infer_instance
    initial := executing D.initial true
    blank := (D.blank, default, false)
    input := ⟨fun a ↦ (D.input a, default, false),
      fun _ _ h ↦ D.input.injective (congrArg Prod.fst h)⟩
    input_ne_blank := fun a h ↦ D.input_ne_blank a (congrArg Prod.fst h)
    transition := transition D }

section
variable {α : Type} (D : Machine α) (ρ : Type) [Finite ρ] [Inhabited ρ]

theorem tick_executing (q : D.State) (side : Bool) (tape : (machine D ρ).Tape)
    {next : D.State ⊕ Bool} {written : D.Symbol} {dir : Dir} :
    let _ := (machine D ρ).tapeInhabited
    D.transition q tape.head.1 = (next, written, dir) →
    (machine D ρ).tick ⟨.inl (executing q side), tape⟩ =
      ⟨.inl (phaseState next (advanceSide tape.head.2.2 side dir)),
        (tape.write (written, tape.head.2)).move dir⟩ := by
  dsimp only
  intro h
  simp only [Machine.tick, machine, executing, transition, h]

end

end PvsNP.TrackCall
