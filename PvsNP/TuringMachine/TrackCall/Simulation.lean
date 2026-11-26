module

public import PvsNP.TuringMachine.TrackCall.Tracks

/-! # Simulate a child machine on a scratch track -/

public section

namespace PvsNP.TrackCall

open Turing (Tape)

variable {α : Type} (D : Machine α) (ρ : Type) [Finite ρ] [Inhabited ρ]

private theorem write_move_nth_ne (tape : (machine D ρ).Tape) (cell : Symbol D ρ)
    (dir : Turing.Dir) {i pos : Int} (h : i ≠ pos) :
    let _ := (machine D ρ).tapeInhabited
    ((tape.write cell).move dir).nth (i - (pos + delta dir)) = tape.nth (i - pos) := by
  dsimp only
  have hNonzero : i - pos ≠ 0 := by omega
  have hWrite := (@Tape.write_nth _ (machine D ρ).tapeInhabited cell tape (i - pos)).trans
    (ite_eq_right hNonzero)
  cases dir
  · rw [@Tape.move_left_nth _ (machine D ρ).tapeInhabited]
    have hIndex : i - (pos + delta .left) - 1 = i - pos := by
      simp only [delta]
      omega
    rw [hIndex, hWrite]
  · rw [@Tape.move_right_nth _ (machine D ρ).tapeInhabited]
    have hIndex : i - (pos + delta .right) + 1 = i - pos := by
      simp only [delta]
      omega
    rw [hIndex, hWrite]

private theorem simulate_tick (child : D.Config) (tape : (machine D ρ).Tape)
    (saved : Turing.Tape ρ) (pos : Int) (side : Bool) {q : D.State}
    (hState : child.state = .inl q) (hScratch : scratch D ρ tape = child.tape)
    (hFrame : FrameAt D ρ tape saved pos) (hSide : SideAt side pos) :
    ∃ (pos' : Int) (side' : Bool) (tape' : (machine D ρ).Tape),
      (machine D ρ).tick ⟨.inl (phaseState child.state side), tape⟩ =
        ⟨.inl (phaseState (D.tick child).state side'), tape'⟩ ∧
      scratch D ρ tape' = (D.tick child).tape ∧ FrameAt D ρ tape' saved pos' ∧
      SideAt side' pos' ∧ pos'.natAbs ≤ pos.natAbs + 1 ∧
      ∀ i : Int, i ≠ pos →
        @Tape.nth _ (machine D ρ).tapeInhabited tape' (i - pos') =
          @Tape.nth _ (machine D ρ).tapeInhabited tape (i - pos) := by
  let cell := @Tape.head _ (machine D ρ).tapeInhabited tape
  rcases hStep : D.transition q (@Tape.head _ D.tapeInhabited child.tape) with
    ⟨next, written, dir⟩
  have hRead : cell.1 = @Tape.head _ D.tapeInhabited child.tape :=
    (scratch_head D ρ tape).symm.trans (congrArg (@Tape.head _ D.tapeInhabited) hScratch)
  have hStep' : D.transition q cell.1 = (next, written, dir) := by
    rwa [hRead]
  let writeMove (childTape : D.Tape) := @Tape.move _ D.tapeInhabited dir
    (@Tape.write _ D.tapeInhabited written childTape)
  have hChild : D.tick child = ⟨next, writeMove child.tape⟩ := by
    simp only [Machine.tick, hState, hStep, writeMove]
  let pos' := pos + delta dir
  let side' := advanceSide cell.2.2 side dir
  let tape' := @Tape.move _ (machine D ρ).tapeInhabited dir
    (@Tape.write _ (machine D ρ).tapeInhabited (written, cell.2) tape)
  refine ⟨pos', side', tape', ?_, ?_, frameAt_write_move D ρ hFrame written dir, ?_,
    natAbs_add_delta_le pos dir, ?_⟩
  · rw [hState, hChild]
    exact tick_executing D ρ q side tape hStep'
  · rw [hChild]
    exact (scratch_write_move D ρ tape written dir).trans (congrArg writeMove hScratch)
  · have hOrigin : cell.2.2 = decide (pos = 0) :=
      congrArg Prod.snd (frameAt_head D ρ hFrame)
    simpa only [side', pos', hOrigin] using sideAt_advanceSide hSide dir
  · exact fun i hi ↦ write_move_nth_ne D ρ tape (written, cell.2) dir (i := i) (pos := pos) hi

/-- The simulation preserves scratch cells beyond the head's possible write positions. -/
theorem simulate_run_preserving_outside (t : Nat) (child : D.Config) (tape : (machine D ρ).Tape)
    (saved : Turing.Tape ρ) (pos : Int) (side : Bool)
    (hScratch : scratch D ρ tape = child.tape) (hFrame : FrameAt D ρ tape saved pos)
    (hSide : SideAt side pos) (hBefore : ∀ j < t, ∃ q, (D.run j child).state = .inl q) :
    let final := (machine D ρ).run t ⟨.inl (phaseState child.state side), tape⟩
    ∃ pos' side', final.state = .inl (phaseState (D.run t child).state side') ∧
      scratch D ρ final.tape = (D.run t child).tape ∧ FrameAt D ρ final.tape saved pos' ∧
      SideAt side' pos' ∧ pos'.natAbs ≤ pos.natAbs + t ∧
      ∀ i : Int, pos.natAbs + t ≤ i.natAbs →
        (@Tape.nth _ (machine D ρ).tapeInhabited final.tape (i - pos')).1 =
          (@Tape.nth _ (machine D ρ).tapeInhabited tape (i - pos)).1 := by
  induction t generalizing child tape pos side with
  | zero => exact ⟨pos, side, rfl, hScratch, hFrame, hSide, Nat.le_refl _, fun _ _ ↦ rfl⟩
  | succ t ih =>
    obtain ⟨q, hState⟩ := hBefore 0 (Nat.zero_lt_succ t)
    simp only [Machine.run_zero] at hState
    obtain ⟨nextPos, nextSide, nextTape, hTick, hNextScratch, hNextFrame, hNextSide,
      hStepBound, hStepOutside⟩ :=
        simulate_tick D ρ child tape saved pos side hState hScratch hFrame hSide
    have hNextBefore : ∀ j < t, ∃ q, (D.run j (D.tick child)).state = .inl q := by
      intro j hj
      exact hBefore (j + 1) (Nat.succ_lt_succ hj)
    obtain ⟨pos', side', hState', hScratch', hFrame', hSide', hRunBound, hRunOutside⟩ :=
      ih (D.tick child) nextTape nextPos nextSide hNextScratch hNextFrame hNextSide hNextBefore
    simp only [Machine.run_succ, hTick]
    refine ⟨pos', side', hState', hScratch', hFrame', hSide', by omega, ?_⟩
    intro i hi
    have hAway : i ≠ pos := by
      rintro rfl
      omega
    exact (hRunOutside i (by omega)).trans (congrArg Prod.fst (hStepOutside i hAway))

/-- Before the child halts, each wrapper tick simulates one child tick. The scratch track
agrees with the child tape, while the protected track and origin marker stay in place. -/
theorem simulate_run (t : Nat) (child : D.Config) (tape : (machine D ρ).Tape)
    (saved : Turing.Tape ρ) (pos : Int) (side : Bool)
    (hScratch : scratch D ρ tape = child.tape) (hFrame : FrameAt D ρ tape saved pos)
    (hSide : SideAt side pos) (hBefore : ∀ j < t, ∃ q, (D.run j child).state = .inl q) :
    let final := (machine D ρ).run t ⟨.inl (phaseState child.state side), tape⟩
    ∃ pos' side', final.state = .inl (phaseState (D.run t child).state side') ∧
      scratch D ρ final.tape = (D.run t child).tape ∧ FrameAt D ρ final.tape saved pos' ∧
      SideAt side' pos' ∧ pos'.natAbs ≤ pos.natAbs + t := by
  obtain ⟨pos', side', hState, hScratch', hFrame', hSide', hBound, _⟩ :=
    simulate_run_preserving_outside D ρ t child tape saved pos side hScratch hFrame hSide hBefore
  exact ⟨pos', side', hState, hScratch', hFrame', hSide', hBound⟩

end PvsNP.TrackCall
