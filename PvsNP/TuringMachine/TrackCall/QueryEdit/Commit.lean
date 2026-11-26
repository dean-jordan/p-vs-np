module

public import PvsNP.TuringMachine.TrackCall.QueryEdit.Travel

/-! # Set the pending sign and return to the origin -/

public section

namespace PvsNP.TrackCall.QueryEdit

open Turing

structure CommitLabels (Q : Type) where
  seekSign : Q
  returnHome : Q
  turnHome : Q
  afterCommit : Q

variable {α : Type} {D : Machine α} {ρ : Type}

/-- Scan to the pending sign, replace its value, and return to the marked origin. -/
structure CommitRules (C : Controller D (Cell ρ)) (labels : CommitLabels C.State)
    (answer : Bool) : Prop where
  seekSign : ∀ cell, C.transition labels.seekSign cell =
    (if pending cell.2.1 then
      (.jump labels.returnHome, editSymbol cell (ordinary answer), .left)
     else (.jump labels.seekSign, cell, .right))
  returnHome : ∀ cell, C.transition labels.returnHome cell =
    (if cell.2.2 then (.jump labels.turnHome, cell, .right)
     else (.jump labels.returnHome, cell, .left))
  turnHome : ∀ cell, C.transition labels.turnHome cell =
    (.jump labels.afterCommit, cell, .left)

variable [Finite ρ] [Inhabited ρ]
variable {C : Controller D (Cell ρ)} {labels : CommitLabels C.State} {answer : Bool}

private theorem tick_commit (rules : CommitRules C labels answer) (cfg : C.compile.Config)
    {pos : Int} {work : Int → D.Symbol} {data : Int → Cell ρ}
    (hState : cfg.state = .inl (.inl labels.seekSign))
    (hTracks : TracksAt D ρ cfg.tape pos work data) (hPending : pending (data pos) = true) :
    let _ := C.compile.tapeInhabited
    C.compile.tick cfg =
      ⟨.inl (.inl labels.returnHome),
        (cfg.tape.write (editSymbol cfg.tape.head (ordinary answer))).move .left⟩ := by
  dsimp only
  let _ := C.compile.tapeInhabited
  obtain ⟨state, tape⟩ := cfg
  change state = .inl (.inl labels.seekSign) at hState
  subst state
  have hHere : pending tape.head.2.1 = true := by
    rw [tracksAt_head D ρ hTracks]
    exact hPending
  apply C.tick_controller (cmd := .jump labels.returnHome)
  simp only [rules.seekSign, hHere, ite_true]

/-- A pending sign at position `s > 0` is committed in `2 * s + 2` ticks. -/
theorem run_commit (rules : CommitRules C labels answer) (s : Nat) (hs : 0 < s)
    {tape : C.compile.Tape} {work : Int → D.Symbol} {data : Int → Cell ρ}
    (hTracks : TracksAt D ρ tape 0 work data)
    (hBefore : ∀ i : Int, 0 ≤ i → i < (s : Int) → pending (data i) = false)
    (hAt : pending (data (s : Int)) = true) :
    let final := C.compile.run (2 * s + 2) ⟨.inl (.inl labels.seekSign), tape⟩
    final.state = .inl (.inl labels.afterCommit) ∧
      TracksAt D ρ final.tape 0 work (updateCell (s : Int) (ordinary answer) data) := by
  let _ := C.compile.tapeInhabited
  let atSign := C.compile.run s ⟨.inl (.inl labels.seekSign), tape⟩
  have hScan := run_scanRight labels.seekSign s (fun cell ↦ pending cell.2.1) hTracks
    (fun cell hFalse ↦ by simp only [rules.seekSign, hFalse, Bool.false_eq_true, ite_false])
    (fun i hi hEnd ↦ hBefore i hi (by omega))
  have hSign : TracksAt D ρ atSign.tape (s : Int) work data := by
    simpa only [Int.zero_add] using hScan.2
  have hTick := tick_commit rules atSign hScan.1 hSign hAt
  let written := (atSign.tape.write (editSymbol atSign.tape.head (ordinary answer))).move .left
  have hPos : (s : Int) + delta .left = (↑(s - 1) : Int) := by
    simp only [delta]
    omega
  have hWritten : TracksAt D ρ written (↑(s - 1) : Int) work
      (updateCell (s : Int) (ordinary answer) data) := by
    simpa only [hPos] using tracksAt_edit_move D ρ hSign (ordinary answer) .left
  have hReturn := run_returnOrigin labels.returnHome labels.turnHome labels.afterCommit (s - 1)
    hWritten
    (fun cell hFalse ↦ by simp only [rules.returnHome, hFalse, Bool.false_eq_true, ite_false])
    (fun cell hTrue ↦ by simp only [rules.returnHome, hTrue, ite_true])
    rules.turnHome
  dsimp only
  rw [show 2 * s + 2 = s + ((s - 1 + 2) + 1) by omega, Machine.run_add, Machine.run_succ]
  change (C.compile.run (s - 1 + 2) (C.compile.tick atSign)).state = _ ∧ _
  rw [hTick]
  exact hReturn

end PvsNP.TrackCall.QueryEdit
