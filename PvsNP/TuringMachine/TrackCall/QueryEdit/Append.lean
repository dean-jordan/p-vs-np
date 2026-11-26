module

public import PvsNP.TuringMachine.TrackCall.QueryEdit.AppendBody
public import PvsNP.TuringMachine.TrackCall.QueryEdit.Travel

/-! # Append a trial clause and restore the head to the origin -/

public section

namespace PvsNP.TrackCall.QueryEdit

open Turing

variable {α : Type} {D : Machine α} {ρ : Type} [Finite ρ] [Inhabited ρ]
variable {C : Controller D (Cell ρ)} {labels : Labels C.State} {stop : ρ → Bool}

/-- Find the old terminator, write the clause, and return to the origin.
Both the scratch track and the auxiliary payloads retain their values. -/
theorem run_append (rules : Rules C labels stop) (j i : Nat)
    {tape : C.compile.Tape} {work : Int → D.Symbol} {data : Int → Cell ρ}
    (hTracks : TracksAt D ρ tape 0 work data)
    (hBefore : ∀ a : Int, 0 ≤ a → a < (j : Int) → tail (data a) = false)
    (hTail : tail (data (j : Int)) = true)
    (hStop : ∀ a : Nat, a ≤ i → stop (data ((j : Int) + 3 + (a : Int))).1 = decide (a = i)) :
    let final := C.compile.run (2 * (j + i + 6) + 2) ⟨.inl (.inl labels.seekTail), tape⟩
    final.state = .inl (.inl labels.afterAppend) ∧
      TracksAt D ρ final.tape 0 work (writeEdits (j : Int) (appendEdits i) data) := by
  let start : C.compile.Config := ⟨.inl (.inl labels.seekTail), tape⟩
  let reached := C.compile.run j start
  have hScan := run_scanRight labels.seekTail j (fun cell ↦ tail cell.2.1) hTracks
    (fun cell h ↦ by simp only [rules.seekTail, h, Bool.false_eq_true, ite_false])
    (fun a hlo hhi ↦ hBefore a hlo (by omega))
  have hReached : reached = ⟨.inl (.inl labels.seekTail), reached.tape⟩ := by
    have hState : reached.state = .inl (.inl labels.seekTail) := hScan.1
    rw [← hState]
  have hAtTail : TracksAt D ρ reached.tape (j : Int) work data := by
    simpa only [Int.zero_add] using hScan.2
  let wrote := C.compile.run (i + 6) ⟨.inl (.inl labels.seekTail), reached.tape⟩
  have hWrite := run_appendBody rules i hAtTail hTail hStop
  have hWrote : wrote = ⟨.inl (.inl labels.returnHome), wrote.tape⟩ := by
    have hState : wrote.state = .inl (.inl labels.returnHome) := hWrite.1
    rw [← hState]
  have hReturnStart : TracksAt D ρ wrote.tape ((j + i + 6 : Nat) : Int)
      work (writeEdits (j : Int) (appendEdits i) data) := by
    rw [show ((j + i + 6 : Nat) : Int) = (j : Int) + (i : Int) + 6 by omega]
    exact hWrite.2
  have hReturn := run_returnOrigin labels.returnHome labels.turnHome labels.afterAppend
    (j + i + 6) hReturnStart
    (fun cell h ↦ by simp only [rules.returnHome, h, Bool.false_eq_true, ite_false])
    (fun cell h ↦ by simp only [rules.returnHome, h, ite_true])
    rules.turnHome
  dsimp only
  rw [show 2 * (j + i + 6) + 2 = (j + (i + 6)) + (j + i + 6 + 2) by omega,
    C.compile.run_add (j + (i + 6)) (j + i + 6 + 2), C.compile.run_add j (i + 6)]
  change
    let final := C.compile.run (j + i + 6 + 2) (C.compile.run (i + 6) reached)
    final.state = .inl (.inl labels.afterAppend) ∧
      TracksAt D ρ final.tape 0 work (writeEdits (j : Int) (appendEdits i) data)
  rw [hReached]
  change
    let final := C.compile.run (j + i + 6 + 2) wrote
    final.state = .inl (.inl labels.afterAppend) ∧
      TracksAt D ρ final.tape 0 work (writeEdits (j : Int) (appendEdits i) data)
  rw [hWrote]
  exact hReturn

end PvsNP.TrackCall.QueryEdit
