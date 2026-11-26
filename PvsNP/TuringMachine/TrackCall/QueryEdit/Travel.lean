module

public import PvsNP.TuringMachine.TrackCall.QueryEdit.Core

/-! # Head movement between query-editing operations -/

public section

namespace PvsNP.TrackCall.QueryEdit

open Turing

variable {α : Type} {D : Machine α} {ρ : Type} [Finite ρ] [Inhabited ρ]
variable {C : Controller D (Cell ρ)}

private theorem tick_move (q : C.State) (tape : C.compile.Tape)
    {cmd : Command C.State} {dir : Dir}
    (h : C.transition q (@Tape.head _ C.compile.tapeInhabited tape) =
      (cmd, @Tape.head _ C.compile.tapeInhabited tape, dir)) :
    C.compile.tick ⟨.inl (.inl q), tape⟩ =
      ⟨C.enter cmd, @Tape.move _ C.compile.tapeInhabited dir tape⟩ := by
  rw [C.tick_controller q tape h, @Tape.write_self _ C.compile.tapeInhabited]

private def scanPosition (pos : Int) (dir : Dir) (steps : Nat) : Int :=
  match dir with
  | .left => pos - steps
  | .right => pos + steps

private theorem scanPosition_zero (pos : Int) (dir : Dir) : scanPosition pos dir 0 = pos := by
  cases dir
  · exact Int.sub_zero pos
  · exact Int.add_zero pos

private theorem scanPosition_succ (pos : Int) (dir : Dir) (steps : Nat) :
    scanPosition pos dir (steps + 1) = scanPosition (pos + delta dir) dir steps := by
  cases dir <;> simp only [scanPosition, delta] <;> omega

private theorem run_scan (q : C.State) (steps : Nat) (dir : Dir)
    (test : Symbol D (Cell ρ) → Bool)
    {tape : C.compile.Tape} {pos : Int} {work : Int → D.Symbol} {data : Int → Cell ρ}
    (hTracks : TracksAt D ρ tape pos work data)
    (hLoop : ∀ cell, test cell = false → C.transition q cell = (.jump q, cell, dir))
    (hUnmarked : ∀ step < steps,
      let i := scanPosition pos dir step
      test (work i, data i, decide (i = 0)) = false) :
    let final := C.compile.run steps ⟨.inl (.inl q), tape⟩
    final.state = .inl (.inl q) ∧
      TracksAt D ρ final.tape (scanPosition pos dir steps) work data := by
  induction steps generalizing tape pos with
  | zero =>
    exact ⟨rfl, by simpa only [scanPosition_zero, Machine.run_zero] using hTracks⟩
  | succ steps ih =>
    let next := @Tape.move _ C.compile.tapeInhabited dir tape
    have hNext : TracksAt D ρ next (pos + delta dir) work data := tracksAt_move D ρ hTracks dir
    have hHere : test (@Tape.head _ C.compile.tapeInhabited tape) = false := by
      change test (@Tape.head _ (machine D (Cell ρ)).tapeInhabited tape) = false
      rw [tracksAt_head D ρ hTracks]
      simpa only [scanPosition_zero] using hUnmarked 0 (Nat.zero_lt_succ steps)
    have hRest := ih hNext (fun step hStep ↦ by
      dsimp only
      rw [← scanPosition_succ]
      exact hUnmarked (step + 1) (Nat.succ_lt_succ hStep))
    dsimp only
    rw [Machine.run_succ, tick_move q tape (hLoop _ hHere), scanPosition_succ]
    exact hRest

/-- Scan right for exactly `steps` ticks, preserving all cells and the scanner state. -/
theorem run_scanRight (q : C.State) (steps : Nat) (test : Symbol D (Cell ρ) → Bool)
    {tape : C.compile.Tape} {pos : Int} {work : Int → D.Symbol} {data : Int → Cell ρ}
    (hTracks : TracksAt D ρ tape pos work data)
    (hLoop : ∀ cell, test cell = false → C.transition q cell = (.jump q, cell, .right))
    (hUnmarked : ∀ i : Int, pos ≤ i → i < pos + (steps : Int) →
      test (work i, data i, decide (i = 0)) = false) :
    let final := C.compile.run steps ⟨.inl (.inl q), tape⟩
    final.state = .inl (.inl q) ∧ TracksAt D ρ final.tape (pos + (steps : Int)) work data :=
  run_scan q steps .right test hTracks hLoop fun step hStep ↦
    hUnmarked (pos + step) (by omega) (by omega)

/-- Scan left for exactly `steps` ticks, preserving all cells and the scanner state. -/
theorem run_scanLeft (q : C.State) (steps : Nat) (test : Symbol D (Cell ρ) → Bool)
    {tape : C.compile.Tape} {pos : Int} {work : Int → D.Symbol} {data : Int → Cell ρ}
    (hTracks : TracksAt D ρ tape pos work data)
    (hLoop : ∀ cell, test cell = false → C.transition q cell = (.jump q, cell, .left))
    (hUnmarked : ∀ i : Int, pos - (steps : Int) < i → i ≤ pos →
      test (work i, data i, decide (i = 0)) = false) :
    let final := C.compile.run steps ⟨.inl (.inl q), tape⟩
    final.state = .inl (.inl q) ∧ TracksAt D ρ final.tape (pos - (steps : Int)) work data :=
  run_scan q steps .left test hTracks hLoop fun step hStep ↦
    hUnmarked (pos - step) (by omega) (by omega)

/-- Move left to the marked origin, then use two moves to enter `target` at position zero. -/
theorem run_returnOrigin (q turn target : C.State) (R : Nat)
    {tape : C.compile.Tape} {work : Int → D.Symbol} {data : Int → Cell ρ}
    (hTracks : TracksAt D ρ tape (R : Int) work data)
    (hLoop : ∀ cell, cell.2.2 = false → C.transition q cell = (.jump q, cell, .left))
    (hTurn : ∀ cell, cell.2.2 = true → C.transition q cell = (.jump turn, cell, .right))
    (hBack : ∀ cell, C.transition turn cell = (.jump target, cell, .left)) :
    let final := C.compile.run (R + 2) ⟨.inl (.inl q), tape⟩
    final.state = .inl (.inl target) ∧ TracksAt D ρ final.tape 0 work data := by
  let reached := C.compile.run R ⟨.inl (.inl q), tape⟩
  have hScan := run_scanLeft q R (fun cell ↦ cell.2.2) hTracks hLoop (by
    intro i hLower _
    have hNonzero : i ≠ 0 := by omega
    simp only [hNonzero, decide_false])
  have hReached : TracksAt D ρ reached.tape 0 work data := by
    simpa only [Int.sub_self] using hScan.2
  have hMarker : (@Tape.head _ C.compile.tapeInhabited reached.tape).2.2 = true := by
    exact congrArg (fun cell : Symbol D (Cell ρ) ↦ cell.2.2) (tracksAt_head D ρ hReached)
  have hRet (c : C.compile.Config) (h : c.state = .inl (.inl q))
      (hOn : (@Tape.head _ C.compile.tapeInhabited c.tape).2.2 = true) :
      C.compile.run 2 c = ⟨.inl (.inl target), c.tape⟩ := by
    obtain ⟨state, tape⟩ := c
    change state = .inl (.inl q) at h
    subst state
    let right := @Tape.move _ C.compile.tapeInhabited .right tape
    rw [Machine.run_succ, tick_move q tape (hTurn _ hOn)]
    change C.compile.run 1 ⟨.inl (.inl turn), right⟩ = _
    rw [Machine.run_succ, tick_move turn right (hBack _), Machine.run_zero]
    rw [show @Tape.move _ C.compile.tapeInhabited .left right = tape from
      @Tape.move_right_left _ C.compile.tapeInhabited tape]
    rfl
  dsimp only
  rw [Machine.run_add]
  change (C.compile.run 2 reached).state = _ ∧
    TracksAt D ρ (C.compile.run 2 reached).tape 0 work data
  rw [hRet reached hScan.1 hMarker]
  exact ⟨rfl, hReached⟩

end PvsNP.TrackCall.QueryEdit
