module

public import PvsNP.TuringMachine.Crossing.Absolute
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! # Charging transcript lengths to physical transitions -/

public section

namespace PvsNP.Machine

open scoped BigOperators

variable {α : Type} (M : Machine α)

private theorem crossing_cut_eq (c : M.AbsoluteConfig) (cut : Int)
    (h : ¬ (c.position < cut ↔ (M.absoluteTick c).position < cut)) :
    cut = max c.position (M.absoluteTick c).position := by
  have hStep := M.absoluteTick_position_le c
  by_cases hLeft : c.position < cut
  · have hRight : ¬ (M.absoluteTick c).position < cut := fun hr ↦ h ⟨fun _ ↦ hr, fun _ ↦ hLeft⟩
    rw [max_eq_right (by omega)]
    omega
  · have hRight : (M.absoluteTick c).position < cut := by
      by_contra hn
      exact h ⟨fun hc ↦ (hLeft hc).elim, fun hc ↦ (hn hc).elim⟩
    rw [max_eq_left (by omega)]
    omega

private theorem sum_crossing_charge_le_one {J : Type} [Fintype J] (cut : J → Int)
    (hCut : Function.Injective cut) (c : M.AbsoluteConfig) :
    (∑ j, if (c.position < cut j ↔ (M.absoluteTick c).position < cut j) then 0 else 1) ≤ 1 := by
  classical
  by_cases hExists : ∃ j, ¬ (c.position < cut j ↔ (M.absoluteTick c).position < cut j)
  · obtain ⟨j, hCross⟩ := hExists
    have hEach (k : J) :
        (if (c.position < cut k ↔ (M.absoluteTick c).position < cut k) then 0 else 1) =
          if k = j then 1 else 0 := by
      by_cases h : k = j
      · subst k; simp [hCross]
      · have hSame : c.position < cut k ↔ (M.absoluteTick c).position < cut k := by
          by_contra hDiff
          exact h (hCut ((crossing_cut_eq M c _ hDiff).trans (crossing_cut_eq M c _ hCross).symm))
        simp [hSame, h]
    simp only [hEach, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Nat.le_refl]
  · have hSame (j : J) : c.position < cut j ↔ (M.absoluteTick c).position < cut j := by
      by_contra hDiff
      exact hExists ⟨j, hDiff⟩
    simp [hSame]

/-- A tick can cross at most one of a collection of distinct cuts. -/
theorem sum_crossingTranscript_length_le {J : Type} [Fintype J] (cut : J → Int)
    (hCut : Function.Injective cut) (ticks : Nat) (c : M.AbsoluteConfig) :
    (∑ j, (M.crossingTranscript (cut j) ticks c).length) ≤ ticks := by
  induction ticks generalizing c with
  | zero => simp [crossingTranscript]
  | succ n ih =>
    have hEach (j : J) :
        (M.crossingTranscript (cut j) (n + 1) c).length =
          (M.crossingTranscript (cut j) n (M.absoluteTick c)).length +
            (if (c.position < cut j ↔ (M.absoluteTick c).position < cut j) then 0 else 1) := by
      simp only [crossingTranscript]
      split <;> simp
    simp only [hEach, Finset.sum_add_distrib]
    exact Nat.add_le_add (ih _) (sum_crossing_charge_le_one M cut hCut c)

end PvsNP.Machine
