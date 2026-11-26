module

public import PvsNP.Complexity.PairEncoding
public import PvsNP.TuringMachine.Sweeps

import Mathlib.Basic.Finite.Sum

/-! # Tape alphabet for the single-tape CNF verifier

The formula marker stands in for one consumed bit, which is kept in finite
control during a shuttle. The certificate marker stores the bit it replaces,
or marks the first blank after the certificate.
-/

@[expose] public section

namespace PvsNP.SATMachine

/-- Input symbols and the three kinds of working markers. -/
inductive Symbol where
  | blank
  | leftEnd
  | delimiter
  | bit (value : Bool)
  | formulaMark
  | certificateMark (value : Option Bool)
  deriving DecidableEq

private def symbolCode : Symbol → Fin 9
  | .blank => 0
  | .leftEnd => 1
  | .delimiter => 2
  | .bit false => 3
  | .bit true => 4
  | .formulaMark => 5
  | .certificateMark none => 6
  | .certificateMark (some false) => 7
  | .certificateMark (some true) => 8

private def symbolOfCode (value : Fin 9) : Symbol :=
  match value.val with
  | 0 => .blank
  | 1 => .leftEnd
  | 2 => .delimiter
  | 3 => .bit false
  | 4 => .bit true
  | 5 => .formulaMark
  | 6 => .certificateMark none
  | 7 => .certificateMark (some false)
  | _ => .certificateMark (some true)

theorem symbolFinite : Finite Symbol := by
  apply Finite.of_injective symbolCode
  apply Function.LeftInverse.injective (g := symbolOfCode)
  intro s
  cases s with
  | bit b => cases b <;> rfl
  | certificateMark value =>
    cases value with
    | none => rfl
    | some b => cases b <;> rfl
  | blank | leftEnd | delimiter | formulaMark => rfl

/-- A raw verifier word uses bits and a delimiter, leaving blank available for the tape. -/
def input : VerifierSymbol ↪ Symbol := ⟨fun value ↦ value.elim .delimiter .bit, by
  intro a b h
  cases a <;> cases b <;> simp_all⟩

@[simp] theorem input_none : input none = .delimiter := rfl

@[simp] theorem input_some (b : Bool) : input (some b) = .bit b := rfl

theorem input_ne_blank (a : VerifierSymbol) : input a ≠ .blank := by
  cases a <;> simp

/-- Unmarked tape symbols for a binary word. -/
abbrev bits (w : BinaryWord) : List Symbol := w.map Symbol.bit

theorem input_encodePair (x y : BinaryWord) :
    (encodePair x y).map input = bits x ++ .delimiter :: bits y := by
  simp only [encodePair_eq, List.map_append, List.map_map, List.map_cons, input_none,
    Function.comp_def, input_some]

/-- The cell after removing the certificate marker. -/
def certificateCell (value : Option Bool) : Symbol := value.elim .blank .bit

/-- Mark the first cell of a suffix, including the end blank for an empty suffix. -/
def markFirst : BinaryWord → List Symbol
  | [] => [.certificateMark none]
  | b :: tail => .certificateMark (some b) :: bits tail

end PvsNP.SATMachine
