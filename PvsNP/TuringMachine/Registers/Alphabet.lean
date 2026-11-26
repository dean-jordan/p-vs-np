module

public import PvsNP.Complexity.PairEncoding
public import PvsNP.TuringMachine.Sweeps

import Mathlib.Basic.Finite.Prod
import Mathlib.Basic.Finite.Sum

/-! # A single tape for unary registers and binary output

A tape cell in the register area stores one bit per register. The prefix
of true bits on a register's track represents its value. The input and
output areas lie to the left of the register area and have distinct
boundary symbols.
-/

@[expose] public section

namespace PvsNP.RegisterMachine

open Turing

/-- The register labels are fixed when a program is compiled. -/
inductive Symbol (R : Type) where
  | blank
  | bit (value : Bool)
  | start
  | home
  | track (cell : R → Bool)
  | inputMark (value : Bool)

variable {R : Type}

private def code : Symbol R → Fin 6 × (Bool ⊕ (R → Bool))
  | .blank => (0, .inl false)
  | .bit b => (1, .inl b)
  | .start => (2, .inl false)
  | .home => (3, .inl false)
  | .track cell => (4, .inr cell)
  | .inputMark b => (5, .inl b)

theorem symbolFinite [Finite R] : Finite (Symbol R) := by
  apply Finite.of_injective code
  intro a b h
  cases a <;> cases b <;> simp_all [code]

def input : Bool ↪ Symbol R := ⟨Symbol.bit, fun _ _ h ↦ Symbol.bit.inj h⟩

theorem input_ne_blank (b : Bool) : input (R := R) b ≠ .blank := by
  intro h
  cases h

/-- Build a Cook machine with the common tape alphabet and an explicit transition table. -/
abbrev host {Q : Type} [Finite R] [Finite Q] (entry : Q)
    (delta : Q → Symbol R → (Q ⊕ Bool) × Symbol R × Dir) : Machine Bool where
  State := Q
  Symbol := Symbol R
  stateFinite := inferInstance
  symbolFinite := RegisterMachine.symbolFinite
  initial := entry
  blank := .blank
  input := RegisterMachine.input
  input_ne_blank := RegisterMachine.input_ne_blank
  transition := delta

/-- Tape symbols for a binary word. -/
abbrev bits (word : BinaryWord) : List (Symbol R) := word.map Symbol.bit

/-- Tape symbols for the finite register area. -/
abbrev trackTape (cells : List (R → Bool)) : List (Symbol R) := cells.map Symbol.track

/-- Set one register's bit in a packed cell. -/
def setTrack [DecidableEq R] (cell : R → Bool) (lane : R) (value : Bool) : R → Bool :=
  fun r ↦ if r = lane then value else cell r

@[simp] theorem setTrack_same [DecidableEq R] (cell : R → Bool) (lane : R) (value : Bool) :
    setTrack cell lane value lane = value := by simp [setTrack]

theorem setTrack_other [DecidableEq R] (cell : R → Bool) (lane r : R) (value : Bool)
    (h : r ≠ lane) : setTrack cell lane value r = cell r := by simp [setTrack, h]

end PvsNP.RegisterMachine
