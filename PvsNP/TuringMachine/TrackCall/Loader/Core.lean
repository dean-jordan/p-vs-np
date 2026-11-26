module

public import PvsNP.TuringMachine.TrackCall.Controller
public import PvsNP.TuringMachine.TrackCall.Tracks

/-! # A finite controller for loading the scratch track -/

@[expose] public section

namespace PvsNP.TrackCall.Loader

open Turing

/-- The protected field supplies boundary marks and the value to write at each cell. -/
structure Layout {α : Type} (D : Machine α) (ρ : Type) where
  leftEdge : ρ → Bool
  rightEdge : ρ → Bool
  load : ρ → D.Symbol

/-- The loader phases and the two continuations of the decider. -/
structure Labels (Q : Type) where
  seekLeft : Q
  turnAtLeft : Q
  writeForward : Q
  seekOrigin : Q
  invoke : Q
  reject : Q
  accept : Q

variable {α : Type} {D : Machine α} {ρ : Type}

/-- The loader scans left, writes right, and returns to the marked origin to call.
The reversals respect Cook's requirement to move on every transition. -/
structure Rules (C : Controller D ρ) (labels : Labels C.State) (layout : Layout D ρ) : Prop where
  seekLeft : ∀ cell, C.transition labels.seekLeft cell =
    (if layout.leftEdge cell.2.1 then (.jump labels.turnAtLeft, cell, .right)
     else (.jump labels.seekLeft, cell, .left))
  turnAtLeft : ∀ cell, C.transition labels.turnAtLeft cell =
    (.jump labels.writeForward, cell, .left)
  writeForward : ∀ cell, C.transition labels.writeForward cell =
    (if layout.rightEdge cell.2.1 then
      (.jump labels.seekOrigin, (layout.load cell.2.1, cell.2), .left)
     else (.jump labels.writeForward, (layout.load cell.2.1, cell.2), .right))
  seekOrigin : ∀ cell, C.transition labels.seekOrigin cell =
    (if cell.2.2 then (.jump labels.invoke, cell, .right)
     else (.jump labels.seekOrigin, cell, .left))
  invoke : ∀ cell, C.transition labels.invoke cell =
    (.call labels.reject labels.accept, cell, .left)

variable (D ρ) [Finite ρ] [Inhabited ρ]

/-- The scratch cells selected by `P` agree with a target tape in absolute coordinates. -/
def ScratchAt (tape : (machine D ρ).Tape) (target : D.Tape) (pos : Int)
    (P : Int → Prop) : Prop :=
  ∀ i, P i →
    (@Tape.nth _ (machine D ρ).tapeInhabited tape (i - pos)).1 =
      @Tape.nth _ D.tapeInhabited target i

theorem scratchAt_mono {tape : (machine D ρ).Tape} {target : D.Tape}
    {pos : Int} {P Q : Int → Prop} (h : ScratchAt D ρ tape target pos P)
    (hPQ : ∀ i, Q i → P i) : ScratchAt D ρ tape target pos Q :=
  fun i hi ↦ h i (hPQ i hi)

theorem scratchAt_move {tape : (machine D ρ).Tape} {target : D.Tape}
    {pos : Int} {P : Int → Prop} (h : ScratchAt D ρ tape target pos P) (dir : Dir) :
    ScratchAt D ρ (@Tape.move _ (machine D ρ).tapeInhabited dir tape)
      target (pos + delta dir) P := by
  intro i hi
  rw [@TrackCall.move_nth_delta _ (machine D ρ).tapeInhabited tape dir,
    show i - (pos + delta dir) + delta dir = i - pos by omega]
  exact h i hi

theorem scratchAt_write_move {tape : (machine D ρ).Tape} {target : D.Tape}
    {pos : Int} {P : Int → Prop} (h : ScratchAt D ρ tape target pos P)
    (b : D.Symbol) (hValue : b = @Tape.nth _ D.tapeInhabited target pos) (dir : Dir) :
    ScratchAt D ρ
      (@Tape.move _ (machine D ρ).tapeInhabited dir
        (@Tape.write _ (machine D ρ).tapeInhabited
          (b, (@Tape.head _ (machine D ρ).tapeInhabited tape).2) tape))
      target (pos + delta dir) (fun i ↦ P i ∨ i = pos) := by
  apply scratchAt_move D ρ _ dir
  intro i hi
  by_cases hHere : i = pos
  · subst i
    simpa only [Int.sub_self, @Tape.write_nth _ (machine D ρ).tapeInhabited, ite_true] using
      hValue
  · have hOffset : i - pos ≠ 0 := by omega
    rw [@Tape.write_nth _ (machine D ρ).tapeInhabited, ite_eq_right hOffset]
    exact h i (hi.resolve_right hHere)

end PvsNP.TrackCall.Loader
