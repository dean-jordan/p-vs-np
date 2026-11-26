module

public import PvsNP.TuringMachine.TrackCall.Loader.Core
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Data.Fintype.Option

/-! # In-place editing of a protected query track -/

@[expose] public section

namespace PvsNP.TrackCall.QueryEdit

open Turing

/-- Protected cells retain an auxiliary payload, a query bit or blank,
and marks for the formula terminator and the pending sign. -/
abbrev Cell (ρ : Type) := ρ × Option Bool × (Bool × Bool)

def bit {ρ : Type} (cell : Cell ρ) : Option Bool := cell.2.1

def tail {ρ : Type} (cell : Cell ρ) : Bool := cell.2.2.1

def pending {ρ : Type} (cell : Cell ρ) : Bool := cell.2.2.2

structure Edit where
  bit : Bool
  tail : Bool
  pending : Bool

def ordinary (b : Bool) : Edit := ⟨b, false, false⟩
def clauseStart : Edit := ordinary true
def literalStart : Edit := ordinary true
def trialSign : Edit := ⟨false, false, true⟩
def indexOne : Edit := ordinary true
def indexEnd : Edit := ordinary false
def clauseEnd : Edit := ordinary false
def formulaEnd : Edit := ⟨false, true, false⟩

def writeCell {ρ : Type} (cell : Cell ρ) (edit : Edit) : Cell ρ :=
  (cell.1, some edit.bit, (edit.tail, edit.pending))

def editSymbol {α : Type} {D : Machine α} {ρ : Type}
    (cell : Symbol D (Cell ρ)) (edit : Edit) : Symbol D (Cell ρ) :=
  (cell.1, writeCell cell.2.1 edit, cell.2.2)

/-- Update one absolute cell of the protected track. -/
def updateCell {ρ : Type} (pos : Int) (edit : Edit) (data : Int → Cell ρ) : Int → Cell ρ :=
  fun i ↦ if i = pos then writeCell (data i) edit else data i

def writeEdits {ρ : Type} (pos : Int) : List Edit → (Int → Cell ρ) → (Int → Cell ρ)
  | [], data => data
  | edit :: rest, data => writeEdits (pos + 1) rest (updateCell pos edit data)

theorem writeEdits_append {ρ : Type} (pos : Int) (a b : List Edit) (data : Int → Cell ρ) :
    writeEdits pos (a ++ b) data =
      writeEdits (pos + (a.length : Int)) b (writeEdits pos a data) := by
  induction a generalizing pos data with
  | nil => simp [writeEdits]
  | cons e a ih =>
    simp only [List.cons_append, writeEdits, ih, List.length_cons]
    rw [show pos + 1 + (a.length : Int) = pos + (a.length + 1 : Nat) by omega]

theorem writeEdits_payload {ρ : Type} (j : Int) (edits : List Edit)
    (data : Int → Cell ρ) (i : Int) : (writeEdits j edits data i).1 = (data i).1 := by
  induction edits generalizing j data with
  | nil => rfl
  | cons e edits ih =>
    rw [writeEdits, ih]
    by_cases hi : i = j <;> simp [updateCell, hi, writeCell]

/-- Replace the old terminator with a unit clause and a new terminator. -/
def appendEdits (i : Nat) : List Edit :=
  [clauseStart, literalStart, trialSign] ++ List.replicate i indexOne ++
    [indexEnd, clauseEnd, formulaEnd]

structure Labels (Q : Type) where
  seekTail : Q
  literal : Q
  sign : Q
  writeIndex : Q
  closeClause : Q
  closeFormula : Q
  returnHome : Q
  turnHome : Q
  afterAppend : Q

variable {α : Type} {D : Machine α} {ρ : Type}

/-- An immutable auxiliary mark ends the unary index of the new clause. -/
structure Rules (C : Controller D (Cell ρ)) (labels : Labels C.State) (stop : ρ → Bool) :
    Prop where
  seekTail : ∀ cell, C.transition labels.seekTail cell =
    (if tail cell.2.1 then (.jump labels.literal, editSymbol cell clauseStart, .right)
     else (.jump labels.seekTail, cell, .right))
  literal : ∀ cell, C.transition labels.literal cell =
    (.jump labels.sign, editSymbol cell literalStart, .right)
  sign : ∀ cell, C.transition labels.sign cell =
    (.jump labels.writeIndex, editSymbol cell trialSign, .right)
  writeIndex : ∀ cell, C.transition labels.writeIndex cell =
    (if stop cell.2.1.1 then (.jump labels.closeClause, editSymbol cell indexEnd, .right)
     else (.jump labels.writeIndex, editSymbol cell indexOne, .right))
  closeClause : ∀ cell, C.transition labels.closeClause cell =
    (.jump labels.closeFormula, editSymbol cell clauseEnd, .right)
  closeFormula : ∀ cell, C.transition labels.closeFormula cell =
    (.jump labels.returnHome, editSymbol cell formulaEnd, .right)
  returnHome : ∀ cell, C.transition labels.returnHome cell =
    (if cell.2.2 then (.jump labels.turnHome, cell, .right)
     else (.jump labels.returnHome, cell, .left))
  turnHome : ∀ cell, C.transition labels.turnHome cell =
    (.jump labels.afterAppend, cell, .left)

variable (D ρ) [Finite ρ] [Inhabited ρ]

/-- Describe both tracks in absolute coordinates, including the unique origin mark. -/
def TracksAt (tape : (machine D (Cell ρ)).Tape) (pos : Int)
    (work : Int → D.Symbol) (data : Int → Cell ρ) : Prop :=
  ∀ i : Int, @Tape.nth _ (machine D (Cell ρ)).tapeInhabited tape (i - pos) =
    (work i, data i, decide (i = 0))

theorem tracksAt_head {tape : (machine D (Cell ρ)).Tape} {pos : Int}
    {work : Int → D.Symbol} {data : Int → Cell ρ} (h : TracksAt D ρ tape pos work data) :
    @Tape.head _ (machine D (Cell ρ)).tapeInhabited tape =
      (work pos, data pos, decide (pos = 0)) := by
  simpa only [Int.sub_self, Tape.nth_zero] using h pos

theorem tracksAt_move {tape : (machine D (Cell ρ)).Tape} {pos : Int}
    {work : Int → D.Symbol} {data : Int → Cell ρ} (h : TracksAt D ρ tape pos work data)
    (dir : Dir) :
    TracksAt D ρ (@Tape.move _ (machine D (Cell ρ)).tapeInhabited dir tape)
      (pos + delta dir) work data := by
  intro i
  rw [@move_nth_delta _ (machine D (Cell ρ)).tapeInhabited tape dir,
    show i - (pos + delta dir) + delta dir = i - pos by omega, h i]

theorem tracksAt_edit_move {tape : (machine D (Cell ρ)).Tape} {pos : Int}
    {work : Int → D.Symbol} {data : Int → Cell ρ} (h : TracksAt D ρ tape pos work data)
    (e : Edit) (dir : Dir) :
    TracksAt D ρ (@Tape.move _ (machine D (Cell ρ)).tapeInhabited dir
      (@Tape.write _ (machine D (Cell ρ)).tapeInhabited
        (editSymbol (@Tape.head _ (machine D (Cell ρ)).tapeInhabited tape) e) tape))
      (pos + delta dir) work (updateCell pos e data) := by
  apply tracksAt_move D ρ _ dir
  intro i
  by_cases hi : i = pos
  · subst i
    simp only [Int.sub_self, @Tape.write_nth _ (machine D (Cell ρ)).tapeInhabited,
      ite_true, tracksAt_head D ρ h, updateCell, editSymbol]
  · have hOffset : i - pos ≠ 0 := by omega
    rw [@Tape.write_nth _ (machine D (Cell ρ)).tapeInhabited, ite_eq_right hOffset, h i]
    simp only [updateCell, ite_eq_right hi]

end PvsNP.TrackCall.QueryEdit
