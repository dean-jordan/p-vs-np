module

public import PvsNP.Complexity.Classes

import PvsNP.TuringMachine.OutputBound

/-! # Binary maps computed by Cook machines

A successful output is a binary word on an otherwise blank tape, with the
head in the same position relative to the word as for an ordinary input.
Beyond the first halt, the absorbing run keeps that output fixed.
-/

@[expose] public section

namespace PvsNP

namespace Machine

open Turing

/-- A binary word on the tape in canonical input position. -/
def wordTape (M : Machine Bool) (w : BinaryWord) : M.Tape :=
  @Tape.mk₁ M.Symbol M.tapeInhabited (w.map M.input)

theorem start_tape_eq_wordTape (M : Machine Bool) (x : BinaryWord) :
    (M.start x).tape = M.wordTape x := rfl

/-- Canonical output uses the input symbols followed by blanks. -/
theorem wordTape_nth_nat (M : Machine Bool) (word : BinaryWord) (i : Nat) :
    @Tape.nth _ M.tapeInhabited (M.wordTape word) (i : Int) =
      (word[i]?.map M.input).getD M.blank := by
  let _ := M.tapeInhabited
  rw [wordTape, mk₁_nth_nat, List.getI_eq_getElem?_getD, List.getElem?_map]
  rfl

/-- A successful halt with exactly the indicated binary output. -/
def OutputsAt (M : Machine Bool) (x y : BinaryWord) (t : Nat) : Prop :=
  (M.run t (M.start x)).state = .inr true ∧
  (M.run t (M.start x)).tape = M.wordTape y

/-- The machine produces the map's output on every binary input. -/
def Computes (M : Machine Bool) (f : BinaryWord → BinaryWord) : Prop :=
  ∀ x, ∃ t, M.OutputsAt x (f x) t

theorem outputsAt_firstHalt (M : Machine Bool) {x y : BinaryWord} {bound : Nat}
    (hBound : M.HaltsWithin x bound) {u : Nat} (hOutput : M.OutputsAt x y u) :
    ∃ t ≤ bound, M.OutputsAt x y t ∧
      ∀ j < t, ∃ q, (M.run j (M.start x)).state = .inl q := by
  obtain ⟨t, ht, b, hb, hRun⟩ := (M.haltsWithin_iff_firstHalt x bound).mp hBound
  refine ⟨t, ht, ?_, hRun⟩
  have eqRun : M.run t (M.start x) = M.run u (M.start x) := by
    rcases Nat.le_total t u with h | h
    · exact (M.run_eq_of_halted_le _ h hb).symm
    · exact M.run_eq_of_halted_le _ h hOutput.1
  unfold OutputsAt at hOutput ⊢
  rwa [eqRun]

/-- A bounded halt for the input preserves the successful output at the bound. -/
theorem outputsAt_at_bound (M : Machine Bool) {x y : BinaryWord} {bound u : Nat}
    (hBound : M.HaltsWithin x bound) (hOutput : M.OutputsAt x y u) : M.OutputsAt x y bound := by
  obtain ⟨t, ht, hFirst, _⟩ := M.outputsAt_firstHalt hBound hOutput
  unfold OutputsAt at hFirst ⊢
  rwa [M.run_eq_of_halted_le _ ht hFirst.1]

end Machine

/-- Polynomial-time computation of a binary map on Cook's single tape. -/
def PolynomialTimeMap (f : BinaryWord → BinaryWord) : Prop :=
  ∃ M : Machine Bool, M.PolyTime ∧ M.Computes f

/-- Polynomial-time many-one reducibility of binary languages. -/
def PolynomiallyReducesTo (L K : BinaryLanguage) : Prop :=
  ∃ f : BinaryWord → BinaryWord, PolynomialTimeMap f ∧ ∀ x, x ∈ L ↔ f x ∈ K

end PvsNP
