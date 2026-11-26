module

public import PvsNP.SAT.CrossingPaletteTime

import Mathlib.Data.Nat.Find

/-! # A worst-case palette bound at every sufficiently large length -/

namespace PvsNP.SATCrossing.Palette

private theorem width_succ_le (r : Nat) : width (r + 1) ≤ 8 * width r := by
  simp only [width, Nat.pow_succ 2 r]
  have hSquare : (r + 1 + 1) ^ 2 ≤ (2 * (r + 1)) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  calc
    _ ≤ 48 * (2 * (r + 1)) ^ 2 * (2 ^ r * 2) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 48 hSquare)
    _ = (2 ^ 2 * 2) * (48 * (r + 1) ^ 2 * 2 ^ r) := by
      rw [Nat.mul_pow 2 (r + 1)]
      ac_rfl
    _ = _ := rfl

/-- At every sufficiently large length there is a rejecting word whose
halting clocks satisfy the near-quadratic bound at that exact length. -/
public theorem exists_rejecting_word_with_log_crossing_time_at_every_length (M : Machine Bool)
    (hDecides : M.Decides CNFSAT) (N : Nat) (hN : 10 * width 1 + 1 ≤ N) :
    ∃ w : BinaryWord, w.length = N ∧ w ∉ CNFSAT ∧
      ∀ t, M.HaltsWithin w t →
        N ^ 2 ≤ 743424 * (N.log2 + 1) * (Nat.card M.State + 3) * (t + N) := by
  let familyLength (r : Nat) := 10 * width r + 1
  have hExists : ∃ k : Nat, N < familyLength (k + 1) := by
    refine ⟨N, ?_⟩
    have hPower : N + 1 < 2 ^ (N + 1) := Nat.lt_two_pow_self
    have hWidth := pow_le_width (N + 1)
    dsimp only [familyLength]
    omega
  let r := Nat.find hExists
  have hAbove : N < familyLength (r + 1) := Nat.find_spec hExists
  have hr : 1 ≤ r := by
    by_contra hZero
    have hEq : r = 0 := by omega
    rw [hEq] at hAbove
    exact (Nat.not_lt_of_ge hN) hAbove
  let n := familyLength r
  have hBelow : n ≤ N := by
    apply Nat.le_of_not_gt
    intro hSmall
    have hEarlier : N < familyLength ((r - 1) + 1) := by
      rw [Nat.sub_add_cancel hr]
      exact hSmall
    have hMin : r ≤ r - 1 := Nat.find_min' hExists hEarlier
    omega
  have hNear : N ≤ 8 * n := by
    have hGrowth := width_succ_le r
    dsimp only [n, familyLength] at hAbove ⊢
    omega
  have hn : n ≠ 0 := by dsimp only [n, familyLength]; omega
  have hNPos : N ≠ 0 := by omega
  have hLog : n.log2 ≤ N.log2 :=
    (Nat.le_log2 hNPos).mpr ((Nat.log2_self_le hn).trans hBelow)
  obtain ⟨w, hLength, hReject, hClock⟩ :=
    exists_rejecting_word_at_exact_length M hDecides r N hr hBelow
  refine ⟨w, hLength, hReject, fun t ht ↦ ?_⟩
  have hTime : n ^ 2 ≤ 11616 * (n.log2 + 1) * (Nat.card M.State + 3) * (t + n) :=
    hClock t ht
  calc
    N ^ 2 ≤ (8 * n) ^ 2 := Nat.pow_le_pow_left hNear 2
    _ = 64 * n ^ 2 := by rw [Nat.mul_pow]
    _ ≤ 64 * (11616 * (n.log2 + 1) * (Nat.card M.State + 3) * (t + n)) :=
      Nat.mul_le_mul_left 64 hTime
    _ = (64 * 11616) * (n.log2 + 1) * (Nat.card M.State + 3) * (t + n) := by ac_rfl
    _ ≤ 743424 * (N.log2 + 1) * (Nat.card M.State + 3) * (t + N) :=
      Nat.mul_le_mul
        (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 743424 (Nat.add_le_add_right hLog 1)))
        (Nat.add_le_add_left hBelow t)

end PvsNP.SATCrossing.Palette
