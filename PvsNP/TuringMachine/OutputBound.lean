module

public import PvsNP.TuringMachine.Core

/-! # Output length in the Cook machine model

One transition writes at the old head and moves the origin by one position.
This bounds how far a nonblank symbol can appear to the right of the head.
-/

@[expose] public section

namespace PvsNP.Machine

open Turing

variable {α : Type} (M : Machine α)

/-- Nonnegative positions in an initial tape read the input list padded with blanks. -/
theorem mk₁_nth_nat {Γ : Type} [Inhabited Γ] (symbols : List Γ) (i : Nat) :
    (Tape.mk₁ symbols).nth i = symbols.getI i := by
  rw [Tape.mk₁, Tape.mk₂, Tape.mk'_nth_nat, ListBlank.nth_mk]

private theorem tick_far_right_blank (c : M.Config) (bound : Int) (hn : 0 ≤ bound)
    (h : ∀ i : Int, bound ≤ i → @Tape.nth _ M.tapeInhabited c.tape i = M.blank)
    (i : Int) (hi : bound + 2 ≤ i) : @Tape.nth _ M.tapeInhabited (M.tick c).tape i = M.blank := by
  let _ := M.tapeInhabited
  rcases c with ⟨state, tape⟩
  cases state with
  | inr result => exact h i (by omega)
  | inl q =>
    rcases hStep : M.transition q (@Tape.head _ M.tapeInhabited tape) with ⟨q', symbol, dir⟩
    cases dir with
    | left =>
      simp only [tick, hStep, Tape.move_left_nth, Tape.write_nth,
        ite_eq_right (show i - 1 ≠ 0 by omega)]
      exact h (i - 1) (by omega)
    | right =>
      simp only [tick, hStep, Tape.move_right_nth, Tape.write_nth,
        ite_eq_right (show i + 1 ≠ 0 by omega)]
      exact h (i + 1) (by omega)

/-- At time `t`, every position at or beyond `|x| + 2t` to the right of the head is blank. -/
theorem run_far_right_blank (x : List α) (t : Nat) (i : Int)
    (hi : (x.length : Int) + 2 * (t : Int) ≤ i) :
    @Tape.nth _ M.tapeInhabited (M.run t (M.start x)).tape i = M.blank := by
  let _ := M.tapeInhabited
  induction t generalizing i with
  | zero =>
    cases i with
    | negSucc i => omega
    | ofNat i =>
      change (x.length : Int) + 2 * (0 : Int) ≤ (i : Int) at hi
      change (Tape.mk₁ (x.map M.input)).nth (i : Int) = M.blank
      rw [mk₁_nth_nat]
      exact List.getI_eq_default _ (by rw [List.length_map]; omega)
  | succ t ih =>
    rw [run_add]
    exact M.tick_far_right_blank _ ((x.length : Int) + 2 * (t : Int)) (by omega)
      (fun i h ↦ ih i h) i (by omega)

/-- A canonical output word has length at most the input length plus twice the number of ticks. -/
theorem output_length_le (x y : List α) (t : Nat)
    (h : (M.run t (M.start x)).tape = @Tape.mk₁ _ M.tapeInhabited (y.map M.input)) :
    y.length ≤ x.length + 2 * t := by
  let _ := M.tapeInhabited
  let i := x.length + 2 * t
  by_cases hi : y.length ≤ i
  · exact hi
  · have hIn : i < y.length := Nat.lt_of_not_ge hi
    have hMap : i < (y.map M.input).length := by simpa only [List.length_map] using hIn
    have hBlank := M.run_far_right_blank x t (i : Int) (by dsimp [i]; omega)
    rw [h, mk₁_nth_nat, List.getI_eq_getElem _ hMap, List.getElem_map] at hBlank
    exact (M.input_ne_blank y[i] hBlank).elim

end PvsNP.Machine
