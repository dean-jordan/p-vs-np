module

public import PvsNP.TuringMachine.TrackCall.QueryEdit.Core

/-! # Absolute locations of the edits in a query append -/

public section

namespace PvsNP.TrackCall.QueryEdit

theorem writeEdits_outside {ρ : Type} (start : Int) (edits : List Edit)
    (data : Int → Cell ρ) (i : Int) (h : i < start ∨ start + (edits.length : Int) ≤ i) :
    writeEdits start edits data i = data i := by
  induction edits generalizing start data with
  | nil => rfl
  | cons e edits ih =>
    have hRange : i < start + 1 ∨ start + 1 + (edits.length : Int) ≤ i := by
      simp only [List.length_cons, Int.natCast_succ] at h
      omega
    have hNot : i ≠ start := by
      simp only [List.length_cons, Int.natCast_succ] at h
      omega
    rw [writeEdits, ih (start + 1) (updateCell start e data) hRange]
    simp only [updateCell, ite_eq_right hNot]

theorem writeEdits_at {ρ : Type} (start : Int) (edits : List Edit)
    (data : Int → Cell ρ) (k : Nat) (hk : k < edits.length) :
    writeEdits start edits data (start + (k : Int)) =
      writeCell (data (start + (k : Int))) edits[k] := by
  induction edits generalizing start data k with
  | nil => simp at hk
  | cons e edits ih =>
    cases k with
    | zero =>
      simp only [writeEdits, Int.natCast_zero, Int.add_zero, List.getElem_cons_zero]
      rw [writeEdits_outside (start + 1) edits (updateCell start e data) start (Or.inl (by omega))]
      simp only [updateCell, ite_true]
    | succ k =>
      have hk' : k < edits.length := Nat.lt_of_succ_lt_succ hk
      simp only [writeEdits, List.getElem_cons_succ, Int.natCast_succ]
      rw [show start + ((k : Int) + 1) = start + 1 + (k : Int) by omega,
        ih (start + 1) (updateCell start e data) k hk']
      simp only [updateCell, ite_eq_right (show start + 1 + (k : Int) ≠ start by omega)]

theorem length_appendEdits (i : Nat) : (appendEdits i).length = i + 6 := by
  simp [appendEdits]

end PvsNP.TrackCall.QueryEdit
