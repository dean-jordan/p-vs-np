module

public import PvsNP.SAT.CrossingPaletteBlocks
public import PvsNP.SAT.CrossingPaletteScale
public import PvsNP.SAT.CrossingTimeLowerBound

import Mathlib.Data.Finset.Max

/-! # A one-logarithm crossing lower bound for binary CNF-SAT -/

public section

namespace PvsNP.SATCrossing.Palette

theorem card_table (r : Nat) : Fintype.card (Table r) = 2 ^ (r * 2 ^ r) := by
  simp [Table, Address, Nat.pow_mul]

private theorem middle_clock_lower_bound (M : Machine Bool) (hDecides : M.Decides CNFSAT)
    (r t : Nat) (hr : 1 ≤ r) (middle : BinaryWord)
    (hEnough : 8 * width r ≤ middle.length)
    (hSat : ∀ a b : Table r, leftBlock r a ++ middle ++ rightBlock r b ∈ CNFSAT ↔ a ≠ b)
    (hClock : ∀ a : Table r, M.HaltsWithin (leftBlock r a ++ middle ++ rightBlock r a) t) :
    8 * width r * ((r * 2 ^ r - 1) / (Nat.card M.State + 3)) ≤ 2 * t := by
  classical
  let q := Nat.card M.State + 3
  let bits := r * 2 ^ r
  let budget := (bits - 1) / q
  have hCount : 2 * q ^ budget ≤ Fintype.card (Table r) := by
    rw [card_table]
    exact twice_pow_div_le_pow_two bits q (Nat.mul_pos hr (Nat.two_pow_pos r))
  have hCross := separated_word_crossing_clock_lower_bound M hDecides (leftBlock r) (rightBlock r)
    middle (width r) t budget (length_leftBlock r) (width_pos r)
    (fun a ha ↦ (hSat a a).mp ha rfl) (fun a b hNe ↦ (hSat a b).mpr hNe) hCount hClock
  exact (Nat.mul_le_mul_right budget hEnough).trans hCross

/-- A clock common to all equal-table inputs pays for the larger family. -/
theorem diagonal_clock_lower_bound (M : Machine Bool) (hDecides : M.Decides CNFSAT)
    (r t : Nat) (hr : 1 ≤ r)
    (hClock : ∀ a : Table r, M.HaltsWithin (word r (width r) a a) t) :
    8 * width r * ((r * 2 ^ r - 1) / (Nat.card M.State + 3)) ≤ 2 * t :=
  middle_clock_lower_bound M hDecides r t hr (paddingBlock (width r))
    (by rw [length_paddingBlock]) (word_mem_CNFSAT_iff r (width r)) hClock

/-- Along the explicit palette lengths, a common rejecting-family clock
has a squared-length lower bound with one logarithmic loss. -/
theorem cnfsat_square_length_le_log_crossing_time (M : Machine Bool)
    (hDecides : M.Decides CNFSAT) (r t : Nat) (hr : 1 ≤ r)
    (hClock : ∀ a : Table r, M.HaltsWithin (word r (width r) a a) t) :
    let n := 10 * width r + 1
    n ^ 2 ≤ 11616 * (n.log2 + 1) * (Nat.card M.State + 3) * (t + n) := by
  exact square_length_le_log_crossing_time r (width r) (Nat.card M.State + 3) t hr
    (pow_le_width r) (Nat.le_refl _) (by omega)
    (diagonal_clock_lower_bound M hDecides r t hr hClock)

private theorem exists_rejecting_of_common_bound (M : Machine Bool) (r base n factor : Nat)
    (family : Table r → BinaryWord) (hLength : ∀ a, (family a).length = n)
    (hReject : ∀ a, family a ∉ CNFSAT)
    (hCommon : ∀ t, (∀ a, M.HaltsWithin (family a) t) → base ^ 2 ≤ factor * (t + base)) :
    ∃ w : BinaryWord, w.length = n ∧ w ∉ CNFSAT ∧
      ∀ t, M.HaltsWithin w t → base ^ 2 ≤ factor * (t + base) := by
  classical
  by_contra hNone
  have hShort (a : Table r) :
      ∃ t, M.HaltsWithin (family a) t ∧ factor * (t + base) < base ^ 2 := by
    by_contra hSlow
    apply hNone
    exact ⟨family a, hLength a, hReject a,
      fun t ht ↦ Nat.le_of_not_gt (fun hBad ↦ hSlow ⟨t, ht, hBad⟩)⟩
  choose clock hHalt hSmall using hShort
  obtain ⟨aMax, _, hLargest⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Table r)) clock Finset.univ_nonempty
  have hClock (a : Table r) : M.HaltsWithin (family a) (clock aMax) := by
    obtain ⟨t, ht, answer, hStop⟩ := hHalt a
    exact ⟨t, ht.trans (hLargest a (Finset.mem_univ a)), answer, hStop⟩
  have hLower := hCommon (clock aMax) hClock
  exact (Nat.not_lt_of_ge hLower) (hSmall aMax)

/-- At each palette length, some rejecting word needs the stated time
budget at every clock by which the machine halts. -/
theorem exists_rejecting_word_with_log_crossing_time (M : Machine Bool)
    (hDecides : M.Decides CNFSAT) (r : Nat) (hr : 1 ≤ r) :
    let n := 10 * width r + 1
    ∃ w : BinaryWord, w.length = n ∧ w ∉ CNFSAT ∧
      ∀ t, M.HaltsWithin w t →
        n ^ 2 ≤ 11616 * (n.log2 + 1) * (Nat.card M.State + 3) * (t + n) := by
  let n := 10 * width r + 1
  apply exists_rejecting_of_common_bound M r n n _ (fun a ↦ word r (width r) a a)
  · intro a
    rw [length_word]
    dsimp only [n]
    omega
  · exact fun a ha ↦ (word_mem_CNFSAT_iff r (width r) a a).mp ha rfl
  · exact fun t hClock ↦ cnfsat_square_length_le_log_crossing_time M hDecides r t hr hClock

/-- Use a fresh middle unit to realize any prescribed length at least the
base palette length, with at least as many counted cuts. -/
theorem exists_rejecting_word_at_exact_length (M : Machine Bool) (hDecides : M.Decides CNFSAT)
    (r N : Nat) (hr : 1 ≤ r) (hN : 10 * width r + 1 ≤ N) :
    ∃ w : BinaryWord, w.length = N ∧ w ∉ CNFSAT ∧
      ∀ t, M.HaltsWithin w t →
        (10 * width r + 1) ^ 2 ≤ 11616 * ((10 * width r + 1).log2 + 1) *
          (Nat.card M.State + 3) * (t + (10 * width r + 1)) := by
  apply exists_rejecting_of_common_bound M r (10 * width r + 1) N _
    (fun a ↦ wordAtLength r N a a)
  · exact fun a ↦ length_wordAtLength r N hN a a
  · exact fun a ha ↦ (wordAtLength_mem_CNFSAT_iff r N hN a a).mp ha rfl
  · intro t hClock
    exact square_length_le_log_crossing_time r (width r) (Nat.card M.State + 3) t hr
      (pow_le_width r) (Nat.le_refl _) (by omega)
      (middle_clock_lower_bound M hDecides r t hr (middleBlock r N) (enough_middleBlock r N hN)
        (wordAtLength_mem_CNFSAT_iff r N hN) hClock)

end PvsNP.SATCrossing.Palette
