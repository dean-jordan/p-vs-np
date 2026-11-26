module

public import PvsNP.TuringMachine.TrackCall.Loader.Core

/-! # Writing a query onto scratch

The controller visits every cell from the left edge through the right
edge. Cells already visited and cells beyond the right edge agree with
the target tape throughout the pass.
-/

public section

namespace PvsNP.TrackCall.Loader

open Turing

variable {α : Type} {D : Machine α} {ρ : Type} [Finite ρ] [Inhabited ρ]
variable (C : Controller D ρ) (labels : Labels C.State) (layout : Layout D ρ)
variable (rules : Rules C labels layout)
include rules

private theorem tick_writeForward (R : Nat) {tape : C.compile.Tape} {saved : Tape ρ}
    {pos : Int} (hFrame : FrameAt D ρ tape saved pos)
    (hRight : layout.rightEdge (saved.nth pos) = decide (pos = (R : Int))) :
    let _ := C.compile.tapeInhabited
    let cell := (layout.load (saved.nth pos), tape.head.2)
    C.compile.tick ⟨.inl (.inl labels.writeForward), tape⟩ =
      if pos = (R : Int) then
        ⟨.inl (.inl labels.seekOrigin), (tape.write cell).move .left⟩
      else
        ⟨.inl (.inl labels.writeForward), (tape.write cell).move .right⟩ := by
  dsimp only
  let _ := C.compile.tapeInhabited
  have hSaved : tape.head.2.1 = saved.nth pos :=
    congrArg Prod.fst (frameAt_head D ρ hFrame)
  by_cases hEnd : pos = (R : Int)
  · rw [ite_eq_left hEnd]
    apply C.tick_controller (cmd := .jump labels.seekOrigin)
    rw [rules.writeForward, hSaved, hRight]
    simp [hEnd]
  · rw [ite_eq_right hEnd]
    apply C.tick_controller (cmd := .jump labels.writeForward)
    rw [rules.writeForward, hSaved, hRight]
    simp [hEnd]

private theorem run_writeForward_from (R k : Nat) {pos : Int}
    {tape : C.compile.Tape} {saved : Tape ρ} {target : D.Tape}
    (hRemain : pos + (k : Int) = (R : Int))
    (hFrame : FrameAt D ρ tape saved pos)
    (hScratch : ScratchAt D ρ tape target pos (fun i ↦ i < pos ∨ (R : Int) < i))
    (hRight : ∀ i : Int, layout.rightEdge (saved.nth i) = decide (i = (R : Int)))
    (hLoad : ∀ i : Int, pos ≤ i → i ≤ (R : Int) →
      layout.load (saved.nth i) = @Tape.nth _ D.tapeInhabited target i) :
    let result := C.compile.run (k + 1) ⟨.inl (.inl labels.writeForward), tape⟩
    result.state = .inl (.inl labels.seekOrigin) ∧
      FrameAt D ρ result.tape saved ((R : Int) - 1) ∧
      ScratchAt D ρ result.tape target ((R : Int) - 1) (fun _ ↦ True) := by
  let _ := C.compile.tapeInhabited
  dsimp only
  induction k generalizing pos tape with
  | zero =>
    have hEnd : pos = (R : Int) := by omega
    let b := layout.load (saved.nth pos)
    have hSymbol : b = @Tape.nth _ D.tapeInhabited target pos :=
      hLoad pos (Int.le_refl _) hEnd.le
    have hTick := tick_writeForward C labels layout rules R hFrame (hRight pos)
    simp only [ite_eq_left hEnd] at hTick
    rw [Machine.run_succ, hTick, Machine.run_zero]
    subst pos
    have hFrame' := frameAt_write_move D ρ hFrame b .left
    have hScratch' := scratchAt_write_move D ρ hScratch b hSymbol .left
    refine ⟨rfl, ?_, ?_⟩
    · simpa only [delta, Int.sub_eq_add_neg] using hFrame'
    · apply scratchAt_mono D ρ
      · simpa only [delta, Int.sub_eq_add_neg] using hScratch'
      · intro i _
        omega
  | succ k ih =>
    have hBefore : pos < (R : Int) := by omega
    let b := layout.load (saved.nth pos)
    have hSymbol : b = @Tape.nth _ D.tapeInhabited target pos :=
      hLoad pos (Int.le_refl _) hBefore.le
    have hTick := tick_writeForward C labels layout rules R hFrame (hRight pos)
    simp only [ite_eq_right hBefore.ne] at hTick
    rw [Machine.run_succ, hTick]
    have hFrame' := frameAt_write_move D ρ hFrame b .right
    have hScratch' := scratchAt_write_move D ρ hScratch b hSymbol .right
    apply ih (pos := pos + 1)
    · omega
    · exact hFrame'
    · apply scratchAt_mono D ρ hScratch'
      intro i hi
      omega
    · intro i hi hEnd
      exact hLoad i (by omega) hEnd

/-- Write the interval from `-L` through `R`, with one tick at each cell. -/
theorem run_writeForward (L R : Nat) {tape : C.compile.Tape} {saved : Tape ρ} {target : D.Tape}
    (hFrame : FrameAt D ρ tape saved (-(L : Int)))
    (hScratch : ScratchAt D ρ tape target (-(L : Int))
      (fun i ↦ i < -(L : Int) ∨ (R : Int) < i))
    (hRight : ∀ i : Int, layout.rightEdge (saved.nth i) = decide (i = (R : Int)))
    (hLoad : ∀ i : Int, -(L : Int) ≤ i → i ≤ (R : Int) →
      layout.load (saved.nth i) = @Tape.nth _ D.tapeInhabited target i) :
    let result := C.compile.run (L + R + 1) ⟨.inl (.inl labels.writeForward), tape⟩
    result.state = .inl (.inl labels.seekOrigin) ∧
      FrameAt D ρ result.tape saved ((R : Int) - 1) ∧
      ScratchAt D ρ result.tape target ((R : Int) - 1) (fun _ ↦ True) :=
  run_writeForward_from C labels layout rules R (L + R) (by omega) hFrame hScratch hRight hLoad

end PvsNP.TrackCall.Loader
