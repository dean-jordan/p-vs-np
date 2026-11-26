module

public import PvsNP.TuringMachine.TrackCall.Loader.Core

/-! # Count the loader's movement before writing and calling -/

public section

namespace PvsNP.TrackCall.Loader

open Turing

variable {α : Type} {D : Machine α} {ρ : Type} [Finite ρ] [Inhabited ρ]
variable {C : Controller D ρ}

private theorem tick_move (q : C.State) (tape : C.compile.Tape)
    {cmd : Command C.State} {dir : Dir}
    (h : C.transition q (@Tape.head _ C.compile.tapeInhabited tape) =
      (cmd, @Tape.head _ C.compile.tapeInhabited tape, dir)) :
    C.compile.tick ⟨.inl (.inl q), tape⟩ =
      ⟨C.enter cmd, @Tape.move _ C.compile.tapeInhabited dir tape⟩ := by
  rw [C.tick_controller q tape h, @Tape.write_self _ C.compile.tapeInhabited]

private theorem run_left_steps (q : C.State) (steps : Nat)
    {tape : C.compile.Tape} {saved : Tape ρ} {target : D.Tape} {pos : Int} {P : Int → Prop}
    (hFrame : FrameAt D ρ tape saved pos) (hScratch : ScratchAt D ρ tape target pos P)
    (hMove : ∀ p : Int, pos - (steps : Int) < p → p ≤ pos →
      ∀ here : C.compile.Tape, FrameAt D ρ here saved p →
        C.transition q (@Tape.head _ C.compile.tapeInhabited here) =
          (.jump q, @Tape.head _ C.compile.tapeInhabited here, .left)) :
    ∃ reached : C.compile.Tape,
      C.compile.run steps ⟨.inl (.inl q), tape⟩ = ⟨.inl (.inl q), reached⟩ ∧
      FrameAt D ρ reached saved (pos - (steps : Int)) ∧
      ScratchAt D ρ reached target (pos - (steps : Int)) P := by
  induction steps generalizing tape pos with
  | zero =>
    change ∃ reached : C.compile.Tape, _ ∧ FrameAt D ρ reached saved (pos - 0) ∧
      ScratchAt D ρ reached target (pos - 0) P
    exact ⟨tape, rfl, by simpa only [Int.sub_zero] using hFrame,
      by simpa only [Int.sub_zero] using hScratch⟩
  | succ steps ih =>
    let next := @Tape.move _ C.compile.tapeInhabited .left tape
    have hNextFrame : FrameAt D ρ next saved (pos - 1) := by
      simpa only [next, delta, Int.sub_eq_add_neg] using frameAt_move D ρ hFrame .left
    have hNextScratch : ScratchAt D ρ next target (pos - 1) P := by
      simpa only [next, delta, Int.sub_eq_add_neg] using scratchAt_move D ρ hScratch .left
    obtain ⟨reached, hRun, hReachedFrame, hReachedScratch⟩ :=
      ih hNextFrame hNextScratch fun p hp hUpper here hHere ↦
        hMove p (by omega) (by omega) here hHere
    have hPos : pos - 1 - (steps : Int) = pos - (↑(steps + 1) : Int) := by omega
    refine ⟨reached, ?_, by simpa only [hPos] using hReachedFrame,
      by simpa only [hPos] using hReachedScratch⟩
    rw [Machine.run_succ, tick_move q tape (hMove pos (by omega) (le_refl pos) tape hFrame)]
    exact hRun

private theorem run_right_left (q turn : C.State) (cmd : Command C.State)
    (tape : C.compile.Tape)
    (hRight : C.transition q (@Tape.head _ C.compile.tapeInhabited tape) =
      (.jump turn, @Tape.head _ C.compile.tapeInhabited tape, .right)) :
    let right := @Tape.move _ C.compile.tapeInhabited .right tape
    C.transition turn (@Tape.head _ C.compile.tapeInhabited right) =
      (cmd, @Tape.head _ C.compile.tapeInhabited right, .left) →
    C.compile.run 2 ⟨.inl (.inl q), tape⟩ = ⟨C.enter cmd, tape⟩ := by
  let right := @Tape.move _ C.compile.tapeInhabited .right tape
  dsimp only
  intro hLeft
  rw [Machine.run_succ, tick_move q tape hRight]
  change C.compile.run 1 ⟨.inl (.inl turn), right⟩ = _
  rw [Machine.run_succ, tick_move turn right hLeft, Machine.run_zero]
  rw [show @Tape.move _ C.compile.tapeInhabited .left right = tape from
    @Tape.move_right_left _ C.compile.tapeInhabited tape]

variable {labels : Labels C.State} {layout : Layout D ρ}

/-- The loader reaches its left edge and faces the writing phase there after `L + 2` ticks. -/
theorem run_seekLeft (rules : Rules C labels layout) (L : Nat)
    {tape : C.compile.Tape} {saved : Tape ρ} {target : D.Tape} {P : Int → Prop}
    (hFrame : FrameAt D ρ tape saved 0) (hScratch : ScratchAt D ρ tape target 0 P)
    (hMarker : ∀ i : Int, layout.leftEdge (saved.nth i) = true ↔ i = -(L : Int)) :
    let final := C.compile.run (L + 2) ⟨.inl (.inl labels.seekLeft), tape⟩
    final.state = .inl (.inl labels.writeForward) ∧
      FrameAt D ρ final.tape saved (-(L : Int)) ∧
      ScratchAt D ρ final.tape target (-(L : Int)) P := by
  obtain ⟨reached, hRun, hReachedFrame, hReachedScratch⟩ :=
    run_left_steps labels.seekLeft L hFrame hScratch (by
      intro pos hLower _ here hHere
      have hCell := congrArg Prod.fst (frameAt_head D ρ hHere)
      have hOff : layout.leftEdge (@Tape.head _ C.compile.tapeInhabited here).2.1 = false := by
        rw [hCell]
        cases hEdge : layout.leftEdge (saved.nth pos) with
        | false => rfl
        | true =>
          have hPos := (hMarker pos).mp hEdge
          omega
      simp only [rules.seekLeft, hOff, Bool.false_eq_true, ite_false])
  have hBoundary : FrameAt D ρ reached saved (-(L : Int)) := by
    simpa only [Int.zero_sub] using hReachedFrame
  have hCell := congrArg Prod.fst (frameAt_head D ρ hBoundary)
  have hOn : layout.leftEdge (@Tape.head _ C.compile.tapeInhabited reached).2.1 = true := by
    rw [hCell]
    exact (hMarker _).mpr rfl
  have hTurn := run_right_left labels.seekLeft labels.turnAtLeft (.jump labels.writeForward)
    reached (by simp only [rules.seekLeft, hOn, ite_true]) (rules.turnAtLeft _)
  dsimp only
  rw [Machine.run_add, hRun, hTurn]
  exact ⟨rfl, hBoundary, by simpa only [Int.zero_sub] using hReachedScratch⟩

/-- From position `R - 1`, the loader calls the child at the origin after `R + 1` ticks. -/
theorem run_seekOrigin (rules : Rules C labels layout) (R : Nat) (hPositive : 0 < R)
    {tape : C.compile.Tape} {saved : Tape ρ} {target : D.Tape} {P : Int → Prop}
    (hFrame : FrameAt D ρ tape saved ((R : Int) - 1))
    (hScratch : ScratchAt D ρ tape target ((R : Int) - 1) P) :
    let final := C.compile.run (R + 1) ⟨.inl (.inl labels.seekOrigin), tape⟩
    final.state = C.enter (.call labels.reject labels.accept) ∧
      FrameAt D ρ final.tape saved 0 ∧ ScratchAt D ρ final.tape target 0 P := by
  have hOriginPos : (R : Int) - 1 - (↑(R - 1) : Int) = 0 := by omega
  obtain ⟨reached, hRun, hReachedFrame, hReachedScratch⟩ :=
    run_left_steps labels.seekOrigin (R - 1) hFrame hScratch (by
      intro pos hLower _ here hHere
      have hPos : pos ≠ 0 := by omega
      have hMarker := congrArg Prod.snd (frameAt_head D ρ hHere)
      have hOff : (@Tape.head _ C.compile.tapeInhabited here).2.2 = false := by
        simpa only [hPos, decide_false] using hMarker
      simp only [rules.seekOrigin, hOff, Bool.false_eq_true, ite_false])
  have hAtOrigin : FrameAt D ρ reached saved 0 := by
    simpa only [hOriginPos] using hReachedFrame
  have hOn : (@Tape.head _ C.compile.tapeInhabited reached).2.2 = true :=
    congrArg Prod.snd (frameAt_head D ρ hAtOrigin)
  have hTurn := run_right_left labels.seekOrigin labels.invoke (.call labels.reject labels.accept)
    reached (by simp only [rules.seekOrigin, hOn, ite_true]) (rules.invoke _)
  dsimp only
  rw [show R + 1 = R - 1 + 2 by omega, Machine.run_add, hRun, hTurn]
  exact ⟨rfl, hAtOrigin, by simpa only [hOriginPos] using hReachedScratch⟩

end PvsNP.TrackCall.Loader
