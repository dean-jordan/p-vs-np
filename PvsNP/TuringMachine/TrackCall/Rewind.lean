module

public import PvsNP.TuringMachine.TrackCall.Tracks

/-! # Returning to the marked origin after a track call -/

namespace PvsNP.TrackCall

open Turing

variable {α : Type} (D : Machine α) (ρ : Type) [Finite ρ] [Inhabited ρ]

private theorem rewind_tick_at_origin (b side : Bool) {tape : (machine D ρ).Tape}
    {saved : Tape ρ} (hFrame : FrameAt D ρ tape saved 0) :
    (machine D ρ).tick ⟨.inl (rewinding b side), tape⟩ =
      ⟨.inl (finishing b), @Tape.move _ (machine D ρ).tapeInhabited .right tape⟩ := by
  have hMark := congrArg Prod.snd (frameAt_head D ρ hFrame)
  change _ = true at hMark
  simp [Machine.tick, machine, rewinding, transition, hMark, Tape.write_self]

private theorem rewind_tick_off_origin (b side : Bool) {tape : (machine D ρ).Tape}
    {saved : Tape ρ} {pos : Int} (hFrame : FrameAt D ρ tape saved pos) (hAway : pos ≠ 0) :
    (machine D ρ).tick ⟨.inl (rewinding b side), tape⟩ =
      ⟨.inl (rewinding b side),
        @Tape.move _ (machine D ρ).tapeInhabited (if side then .left else .right) tape⟩ := by
  have hMark := congrArg Prod.snd (frameAt_head D ρ hFrame)
  change _ = decide (pos = 0) at hMark
  simp only [hAway, decide_false] at hMark
  simp [Machine.tick, machine, rewinding, transition, hMark, Tape.write_self]

private theorem finishing_tick (b : Bool) (tape : (machine D ρ).Tape) :
    (machine D ρ).tick ⟨.inl (finishing b), tape⟩ =
      ⟨.inr b, @Tape.move _ (machine D ρ).tapeInhabited .left tape⟩ := by
  simp [Machine.tick, machine, finishing, transition, Tape.write_self]

private theorem rewind_at_origin (b side : Bool) {tape : (machine D ρ).Tape}
    {saved : Tape ρ} (hFrame : FrameAt D ρ tape saved 0) :
    (machine D ρ).run 2 ⟨.inl (rewinding b side), tape⟩ = ⟨.inr b, tape⟩ := by
  rw [Machine.run_succ, rewind_tick_at_origin D ρ b side hFrame, Machine.run_succ,
    finishing_tick, Machine.run_zero, @Tape.move_right_left _ (machine D ρ).tapeInhabited]

private theorem rewind_progress {side : Bool} {pos : Int} (hSide : SideAt side pos)
    (hAway : pos ≠ 0) :
    let next := pos + delta (if side then .left else .right)
    SideAt side next ∧ next.natAbs + 1 = pos.natAbs := by
  cases side with
  | false =>
    have hNeg : pos < 0 := by
      by_cases hPos : 0 < pos
      · exact (Bool.false_ne_true (hSide.1 hPos)).elim
      · omega
    change SideAt false (pos + 1) ∧ (pos + 1).natAbs + 1 = pos.natAbs
    exact ⟨⟨fun h ↦ by omega, fun _ ↦ rfl⟩, by omega⟩
  | true =>
    have hPos : 0 < pos := by
      by_cases hNeg : pos < 0
      · exact (Bool.false_ne_true (hSide.2 hNeg).symm).elim
      · omega
    change SideAt true (pos + (-1)) ∧ (pos + (-1)).natAbs + 1 = pos.natAbs
    exact ⟨⟨fun _ ↦ rfl, fun h ↦ by omega⟩, by omega⟩

private theorem rewind_move_nth (tape : (machine D ρ).Tape) (dir : Dir) (pos i : Int) :
    letI := (machine D ρ).tapeInhabited
    (tape.move dir).nth (i - (pos + delta dir)) = tape.nth (i - pos) := by
  dsimp only
  cases dir
  · rw [@Tape.move_left_nth _ (machine D ρ).tapeInhabited]
    congr 1
    simp only [delta]
    omega
  · rw [@Tape.move_right_nth _ (machine D ρ).tapeInhabited]
    congr 1
    simp only [delta]
    omega

private theorem rewind_run_preserved (b side : Bool) {tape : (machine D ρ).Tape}
    {saved : Tape ρ} {pos : Int}
    (hFrame : FrameAt D ρ tape saved pos) (hSide : SideAt side pos) :
    letI := (machine D ρ).tapeInhabited
    let result := (machine D ρ).run (pos.natAbs + 2) ⟨.inl (rewinding b side), tape⟩
    result.state = .inr b ∧ FrameAt D ρ result.tape saved 0 ∧
      ∀ i : Int, result.tape.nth i = tape.nth (i - pos) := by
  dsimp only
  let _ := (machine D ρ).tapeInhabited
  generalize hDistance : pos.natAbs = k
  induction k generalizing tape pos with
  | zero =>
    have hOrigin : pos = 0 := by omega
    subst pos
    rw [rewind_at_origin D ρ b side hFrame]
    exact ⟨rfl, hFrame, fun i ↦ by rw [Int.sub_zero]⟩
  | succ k ih =>
    have hAway : pos ≠ 0 := by omega
    let dir : Dir := if side then .left else .right
    let next : Int := pos + delta dir
    have hProgress : SideAt side next ∧ next.natAbs + 1 = pos.natAbs :=
      rewind_progress hSide hAway
    have hStepDistance : next.natAbs = k := by omega
    have hStepFrame : FrameAt D ρ (tape.move dir) saved next := frameAt_move D ρ hFrame dir
    obtain ⟨hHalt, hFinalFrame, hTape⟩ := ih hStepFrame hProgress.1 hStepDistance
    rw [show k + 1 + 2 = (k + 2) + 1 by omega, Machine.run_succ,
      rewind_tick_off_origin D ρ b side hFrame hAway]
    exact ⟨hHalt, hFinalFrame, fun i ↦ (hTape i).trans (rewind_move_nth D ρ tape dir pos i)⟩

/-- After `pos.natAbs + 2` ticks, the rewind ends at the origin with the saved result. -/
public theorem rewind_run (b side : Bool) {tape : (machine D ρ).Tape} {saved : Tape ρ}
    {pos : Int} (hFrame : FrameAt D ρ tape saved pos) (hSide : SideAt side pos) :
    let result := (machine D ρ).run (pos.natAbs + 2) ⟨.inl (rewinding b side), tape⟩
    result.state = .inr b ∧ FrameAt D ρ result.tape saved 0 :=
  let h := rewind_run_preserved D ρ b side hFrame hSide
  ⟨h.1, h.2.1⟩

/-- Each absolute cell has the same physical symbol before and after a rewind. -/
public theorem rewind_run_nth (b side : Bool) {tape : (machine D ρ).Tape} {saved : Tape ρ}
    {pos : Int} (hFrame : FrameAt D ρ tape saved pos) (hSide : SideAt side pos) (i : Int) :
    letI := (machine D ρ).tapeInhabited
    ((machine D ρ).run (pos.natAbs + 2) ⟨.inl (rewinding b side), tape⟩).tape.nth i =
      tape.nth (i - pos) :=
  (rewind_run_preserved D ρ b side hFrame hSide).2.2 i

end PvsNP.TrackCall
