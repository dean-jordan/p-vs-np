module

public import PvsNP.TuringMachine.TrackCall.Core

import Mathlib.Basic.Finite.Prod
import Mathlib.Basic.Finite.Sum

/-! # Link a finite Cook controller to a returning decider -/

@[expose] public section

namespace PvsNP.TrackCall

open Turing

/-- A controller transition may enter the decider, with return labels for both answers. -/
inductive Command (Q : Type) where
  | jump (next : Q)
  | call (reject accept : Q)
  | halt (answer : Bool)

/-- A finite controller that uses the same tape alphabet as a returning call. -/
structure Controller {α : Type} (D : Machine α) (ρ : Type) where
  State : Type
  stateFinite : Finite State
  initial : State
  transition : State → Symbol D ρ → Command State × Symbol D ρ × Dir

namespace Controller

variable {α : Type} {D : Machine α} {ρ : Type} [Finite ρ] [Inhabited ρ]
variable (C : Controller D ρ)

/-- Save the two return labels in the finite control while the call runs. -/
abbrev LinkedState := C.State ⊕ (TrackCall.State D.State × C.State × C.State)

def resume (reject accept : C.State) (answer : Bool) : C.State :=
  if answer then accept else reject

def enter (cmd : Command C.State) : C.LinkedState ⊕ Bool :=
  match cmd with
  | .jump next => .inl (.inl next)
  | .call reject accept => .inl (.inr (executing D.initial true, reject, accept))
  | .halt answer => .inr answer

def fromCall (reject accept : C.State) (state : TrackCall.State D.State ⊕ Bool) :
    C.LinkedState ⊕ Bool :=
  match state with
  | .inl running => .inl (.inr (running, reject, accept))
  | .inr answer => .inl (.inl (C.resume reject accept answer))

/-- A Cook machine containing both controller and call states. The call's last
transition enters the chosen return label at the marked origin. -/
@[reducible] def compile : Machine α := by
  let _ : Finite C.State := C.stateFinite
  let _ : Finite (TrackCall.State D.State) := (machine D ρ).stateFinite
  exact {
    State := C.LinkedState
    Symbol := (machine D ρ).Symbol
    stateFinite := by
      change Finite (C.State ⊕ (TrackCall.State D.State × C.State × C.State))
      infer_instance
    symbolFinite := (machine D ρ).symbolFinite
    initial := .inl C.initial
    blank := (machine D ρ).blank
    input := (machine D ρ).input
    input_ne_blank := (machine D ρ).input_ne_blank
    transition := fun q cell ↦
      match q with
      | .inl controller =>
        let (next, cell', dir) := C.transition controller cell
        (C.enter next, cell', dir)
      | .inr (callee, reject, accept) =>
        let (next, cell', dir) := TrackCall.transition D callee cell
        (C.fromCall reject accept next, cell', dir) }

/-- The same physical tape is shared by the controller and decider. -/
def embedCall (reject accept : C.State) (cfg : (machine D ρ).Config) : C.compile.Config :=
  ⟨C.fromCall reject accept cfg.state, cfg.tape⟩

theorem tick_controller (q : C.State) (tape : C.compile.Tape)
    {cmd : Command C.State} {cell : Symbol D ρ} {dir : Dir} :
    let _ := C.compile.tapeInhabited
    C.transition q tape.head = (cmd, cell, dir) →
    C.compile.tick ⟨.inl (.inl q), tape⟩ = ⟨C.enter cmd, (tape.write cell).move dir⟩ := by
  dsimp only
  intro h
  simp only [Machine.tick, compile, h]

theorem tick_embedCall (reject accept : C.State) (cfg : (machine D ρ).Config)
    (hRunning : ∃ q, cfg.state = .inl q) :
    C.compile.tick (C.embedCall reject accept cfg) =
      C.embedCall reject accept ((machine D ρ).tick cfg) := by
  obtain ⟨state, tape⟩ := cfg
  obtain ⟨q, hq⟩ := hRunning
  change state = .inl q at hq
  subst state
  rcases h : TrackCall.transition D q (@Tape.head _ (machine D ρ).tapeInhabited tape) with
    ⟨next, cell, dir⟩
  simp only [Machine.tick, embedCall, fromCall, compile, machine, h]

theorem run_embedCall (reject accept : C.State) (cfg : (machine D ρ).Config) (t : Nat)
    (hRunning : ∀ j < t, ∃ q, ((machine D ρ).run j cfg).state = .inl q) :
    C.compile.run t (C.embedCall reject accept cfg) =
      C.embedCall reject accept ((machine D ρ).run t cfg) := by
  induction t generalizing cfg with
  | zero => rfl
  | succ t ih =>
    rw [Machine.run_succ, C.tick_embedCall reject accept cfg (hRunning 0 (Nat.zero_lt_succ t)),
      Machine.run_succ]
    exact ih _ (fun j hj ↦ hRunning (j + 1) (Nat.succ_lt_succ hj))

end Controller

end PvsNP.TrackCall
