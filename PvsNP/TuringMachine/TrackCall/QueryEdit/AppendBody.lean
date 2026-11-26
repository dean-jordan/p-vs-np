module

public import PvsNP.TuringMachine.TrackCall.QueryEdit.Core

/-! # Write a unit clause and advance its formula terminator -/

namespace PvsNP.TrackCall.QueryEdit

open Turing

variable {α : Type} {D : Machine α} {ρ : Type} [Finite ρ] [Inhabited ρ]
variable {C : Controller D (Cell ρ)} {labels : Labels C.State} {stop : ρ → Bool}

private theorem tick_editRight (source target : C.State) (e : Edit)
    {tape : C.compile.Tape} {pos : Int} {work : Int → D.Symbol} {data : Int → Cell ρ}
    (hTracks : TracksAt D ρ tape pos work data)
    (hRule : ∀ cell, cell.2.1 = data pos →
      C.transition source cell = (.jump target, editSymbol cell e, .right)) :
    ∃ nextTape : C.compile.Tape,
      C.compile.tick ⟨.inl (.inl source), tape⟩ = ⟨.inl (.inl target), nextTape⟩ ∧
      TracksAt D ρ nextTape (pos + 1) work (updateCell pos e data) := by
  let _ := C.compile.tapeInhabited
  let cell := tape.head
  let nextTape := (tape.write (editSymbol cell e)).move .right
  have hCell : cell.2.1 = data pos :=
    congrArg (fun c : Symbol D (Cell ρ) ↦ c.2.1) (tracksAt_head D ρ hTracks)
  exact ⟨nextTape, C.tick_controller source tape (hRule cell hCell),
    tracksAt_edit_move D ρ hTracks e .right⟩

private theorem run_closing (rules : Rules C labels stop)
    {tape : C.compile.Tape} {pos : Int} {work : Int → D.Symbol} {data : Int → Cell ρ}
    (hTracks : TracksAt D ρ tape pos work data) :
    let final := C.compile.run 2 ⟨.inl (.inl labels.closeClause), tape⟩
    final.state = .inl (.inl labels.returnHome) ∧
      TracksAt D ρ final.tape (pos + 2) work (writeEdits pos [clauseEnd, formulaEnd] data) := by
  obtain ⟨nextTape, hStep, hNext⟩ :=
    tick_editRight labels.closeClause labels.closeFormula clauseEnd hTracks
      (fun cell _ ↦ rules.closeClause cell)
  obtain ⟨_, hLast, hFinal⟩ :=
    tick_editRight labels.closeFormula labels.returnHome formulaEnd hNext
      (fun cell _ ↦ rules.closeFormula cell)
  dsimp only
  rw [Machine.run_succ, hStep, Machine.run_succ, hLast, Machine.run_zero,
    show pos + 2 = pos + 1 + 1 by omega]
  exact ⟨rfl, hFinal⟩

private theorem run_writeIndex (rules : Rules C labels stop) (i : Nat)
    {tape : C.compile.Tape} {pos : Int} {work : Int → D.Symbol} {data : Int → Cell ρ}
    (hTracks : TracksAt D ρ tape pos work data)
    (hStop : ∀ a : Nat, a ≤ i → stop (data (pos + (a : Int))).1 = decide (a = i)) :
    let final := C.compile.run (i + 3) ⟨.inl (.inl labels.writeIndex), tape⟩
    final.state = .inl (.inl labels.returnHome) ∧
      TracksAt D ρ final.tape (pos + (i : Int) + 3) work
        (writeEdits pos (List.replicate i indexOne ++ [indexEnd, clauseEnd, formulaEnd]) data) := by
  induction i generalizing tape pos data with
  | zero =>
    have hHere : stop (data pos).1 = true := by
      simpa using hStop 0 (Nat.le_refl 0)
    obtain ⟨_, hStep, hNext⟩ :=
      tick_editRight labels.writeIndex labels.closeClause indexEnd hTracks (by
        intro cell hCell
        simp only [rules.writeIndex, hCell, hHere, ite_true])
    dsimp only
    rw [Machine.run_succ, hStep]
    have hPosition : pos + 3 = pos + 1 + 2 := by omega
    simpa only [Int.natCast_zero, Int.add_zero, hPosition, List.replicate_zero,
      List.nil_append, writeEdits] using run_closing rules hNext
  | succ i ih =>
    have hHere : stop (data pos).1 = false := by
      simpa using hStop 0 (Nat.zero_le _)
    obtain ⟨_, hStep, hNext⟩ :=
      tick_editRight labels.writeIndex labels.writeIndex indexOne hTracks (by
        intro cell hCell
        simp only [rules.writeIndex, hCell, hHere, Bool.false_eq_true, ite_false])
    have hNextStop (a : Nat) (ha : a ≤ i) :
        stop (updateCell pos indexOne data (pos + 1 + (a : Int))).1 = decide (a = i) := by
      change stop (writeEdits pos [indexOne] data (pos + 1 + (a : Int))).1 = _
      rw [writeEdits_payload, show pos + 1 + (a : Int) = pos + ((a + 1 : Nat) : Int) by omega,
        hStop (a + 1) (Nat.succ_le_succ ha)]
      simp
    dsimp only
    rw [show i + 1 + 3 = (i + 3) + 1 by omega, Machine.run_succ, hStep,
      show pos + ((i + 1 : Nat) : Int) + 3 = pos + 1 + (i : Int) + 3 by omega,
      List.replicate_succ, List.cons_append, writeEdits]
    exact ih hNext hNextStop

/-- Starting at the old terminator, write the complete unit clause and its new
formula terminator before entering the return phase. -/
public theorem run_appendBody (rules : Rules C labels stop) (i : Nat)
    {tape : C.compile.Tape} {j : Int} {work : Int → D.Symbol} {data : Int → Cell ρ}
    (hTracks : TracksAt D ρ tape j work data) (hTail : tail (data j) = true)
    (hStop : ∀ a : Nat, a ≤ i → stop (data (j + 3 + (a : Int))).1 = decide (a = i)) :
    let final := C.compile.run (i + 6) ⟨.inl (.inl labels.seekTail), tape⟩
    final.state = .inl (.inl labels.returnHome) ∧
      TracksAt D ρ final.tape (j + (i : Int) + 6) work (writeEdits j (appendEdits i) data) := by
  obtain ⟨_, hClause, hAfterClause⟩ :=
    tick_editRight labels.seekTail labels.literal clauseStart hTracks (by
      intro cell hCell
      simp only [rules.seekTail, hCell, hTail, ite_true])
  obtain ⟨_, hLiteral, hAfterLiteral⟩ :=
    tick_editRight labels.literal labels.sign literalStart hAfterClause
      (fun cell _ ↦ rules.literal cell)
  obtain ⟨_, hSign, hAfterSign⟩ :=
    tick_editRight labels.sign labels.writeIndex trialSign hAfterLiteral
      (fun cell _ ↦ rules.sign cell)
  have hIndexStop (a : Nat) (ha : a ≤ i) :
      stop (writeEdits j [clauseStart, literalStart, trialSign] data
        (j + 1 + 1 + 1 + (a : Int))).1 = decide (a = i) := by
    rw [writeEdits_payload, show j + 1 + 1 + 1 + (a : Int) = j + 3 + (a : Int) by omega]
    exact hStop a ha
  dsimp only
  rw [show i + 6 = (i + 3) + 1 + 1 + 1 by omega,
    Machine.run_succ, hClause, Machine.run_succ, hLiteral, Machine.run_succ, hSign,
    show j + (i : Int) + 6 = j + 1 + 1 + 1 + (i : Int) + 3 by omega]
  simpa only [appendEdits, List.cons_append, List.nil_append, writeEdits] using
    run_writeIndex rules i hAfterSign hIndexStop

end PvsNP.TrackCall.QueryEdit
