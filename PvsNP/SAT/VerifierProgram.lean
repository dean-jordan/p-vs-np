module

public import PvsNP.SAT.CursorProgram
public import PvsNP.SAT.InputSetup

import Mathlib.Basic.Finite.Prod

/-! # Single-tape program for the CNF verifier

The active head processes formula bits from left to right. On a certificate
operation it marks the current formula cell, walks to the certificate marker,
performs the operation, and returns to the formula marker.
-/

@[expose] public section

namespace PvsNP.SATMachine

open Turing

/-- Control states for local parsing and certificate shuttles. -/
inductive Phase where
  | parse (control : SATCursor.Control)
  | reset (next : SATCursor.Control) (restoreBit : Bool)
  | seek (control : SATCursor.Control) (advance : Bool)
  | place (next : SATCursor.Control) (restoreBit : Bool)
  | restore (next : SATCursor.Control) (restoreBit : Bool)

private def phaseCode : Phase → Fin 5 × SATCursor.Control × Bool
  | .parse q => (0, q, false)
  | .reset q b => (1, q, b)
  | .seek q b => (2, q, b)
  | .place q b => (3, q, b)
  | .restore q b => (4, q, b)

instance : Finite Phase := Finite.of_injective phaseCode (by
  intro a b h
  cases a <;> cases b <;> simp_all [phaseCode])

/-- The transition table after input validation. Every transition writes and moves. -/
def verifierTransition : Phase → Symbol → (Phase ⊕ Bool) × Symbol × Dir
  | .parse q, .bit bit =>
    let (next, action) := SATCursor.transition q bit none
    match action with
    | .stay => ⟨.inl (.parse next), .bit bit, .right⟩
    | .reset => ⟨.inl (.reset next bit), .formulaMark, .right⟩
    | .advance | .release => ⟨.inl (.seek q bit), .formulaMark, .right⟩
  | .parse q, .delimiter => ⟨.inr q.result, .delimiter, .right⟩
  | .reset q b, .bit a => ⟨.inl (.reset q b), .bit a, .right⟩
  | .reset q b, .delimiter => ⟨.inl (.place q b), .delimiter, .right⟩
  | .seek q b, .bit a => ⟨.inl (.seek q b), .bit a, .right⟩
  | .seek q b, .delimiter => ⟨.inl (.seek q b), .delimiter, .right⟩
  | .seek q true, .certificateMark none =>
    ⟨.inl (.restore (SATCursor.transition q true none).1 true), .certificateMark none, .left⟩
  | .seek q true, .certificateMark (some a) =>
    ⟨.inl (.place (SATCursor.transition q true (some a)).1 true), .bit a, .right⟩
  | .seek q false, .certificateMark value =>
    ⟨.inl (.restore (SATCursor.transition q false value).1 false), certificateCell value, .left⟩
  | .place q b, .bit a => ⟨.inl (.restore q b), .certificateMark (some a), .left⟩
  | .place q b, .blank => ⟨.inl (.restore q b), .certificateMark none, .left⟩
  | .restore q b, .bit a => ⟨.inl (.restore q b), .bit a, .left⟩
  | .restore q b, .delimiter => ⟨.inl (.restore q b), .delimiter, .left⟩
  | .restore q b, .formulaMark => ⟨.inl (.parse q), .bit b, .right⟩
  | _, a => ⟨.inr false, a, .right⟩

/-- Insert the parser phases after the input setup phases. -/
def verifierProgram (q : Phase) (a : Symbol) : ((SetupState ⊕ Phase) ⊕ Bool) × Symbol × Dir :=
  let (next, written, dir) := verifierTransition q a
  ⟨next.map Sum.inr id, written, dir⟩

/-- The Cook single-tape verifier with a delimiter-validation phase. -/
abbrev verifierMachine : Machine VerifierSymbol :=
  withInputSetup (.parse SATCursor.initial.control) verifierProgram

/-- A parser-phase configuration with the given finite tape zipper. -/
abbrev phaseConfig (q : Phase) (left right : List Symbol) : verifierMachine.Config :=
  ⟨.inl (.inr q), verifierMachine.tapeFromLists left right⟩

/-- A parser-phase configuration positioned one cell to the left of the given cut. -/
abbrev leftOfCut (q : Phase) (left right : List Symbol) : verifierMachine.Config :=
  ⟨.inl (.inr q), @Tape.move _ verifierMachine.tapeInhabited .left
    (verifierMachine.tapeFromLists left right)⟩

end PvsNP.SATMachine
