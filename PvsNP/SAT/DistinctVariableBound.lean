module

public import PvsNP.SAT.BinaryEncoding

import Init.Data.List.Sort.Lemmas

/-! # Occurring variable names in a binary CNF word -/

public section

namespace PvsNP.CNFCode

open CNF (Clause Formula)
open scoped List

/-- List each variable that occurs in the formula, in first occurrence order. -/
@[expose] def occurringIndices (F : Formula Nat) : List Nat :=
  (F.flatten.map literalIndex).eraseDups

theorem mem_occurringIndices_iff {F : Formula Nat} {i : Nat} :
    i ∈ occurringIndices F ↔ ∃ c ∈ F, ∃ l ∈ c, literalIndex l = i := by
  simp only [occurringIndices, List.mem_eraseDups, List.mem_map, List.mem_flatten]
  constructor
  · rintro ⟨l, ⟨c, hc, hl⟩, h⟩
    exact ⟨c, hc, l, hl, h⟩
  · rintro ⟨c, hc, l, hl, h⟩
    exact ⟨l, ⟨c, hc, hl⟩, h⟩

private theorem eraseDups_nodup_sublist (xs : List Nat) :
    xs.eraseDups.Nodup ∧ xs.eraseDups <+ xs := by
  cases xs with
  | nil => simp
  | cons a xs =>
    rw [List.eraseDups_cons]
    obtain ⟨hDistinct, hSublist⟩ := eraseDups_nodup_sublist (xs.filter fun b ↦ !(b == a))
    refine ⟨List.nodup_cons.mpr ⟨?_, hDistinct⟩,
      .cons_cons a (hSublist.trans (List.filter_sublist ..))⟩
    simp [List.mem_eraseDups]
termination_by xs.length
decreasing_by
  exact Nat.lt_succ_of_le (List.filter_sublist ..).length_le

theorem occurringIndices_nodup (F : Formula Nat) : (occurringIndices F).Nodup :=
  (eraseDups_nodup_sublist _).1

private theorem length_encodeClause_eq (c : Clause Nat) :
    (encodeClause c).length = 1 + (c.map fun l ↦ literalIndex l + 3).sum := by
  induction c with
  | nil => simp
  | cons l c ih =>
    simp only [encodeClause_cons, List.length_cons, List.length_append, length_encodeLiteral,
      List.map_cons, List.sum_cons, ih]
    omega

/-- Count both levels of framing and the bits used by every literal occurrence. -/
theorem length_encode_eq (F : Formula Nat) :
    (encode F).length = 1 + 2 * F.length + (F.flatten.map fun l ↦ literalIndex l + 3).sum := by
  induction F with
  | nil => simp
  | cons c F ih =>
    simp only [encode_cons, List.length_cons, List.length_append, length_encodeClause_eq, ih,
      List.flatten_cons, List.map_append, List.sum_append]
    omega

private theorem sum_le_sum_of_sublist {xs ys : List Nat} (h : xs <+ ys) : xs.sum ≤ ys.sum := by
  induction h with
  | slnil => simp
  | cons _ _ ih =>
    simp only [List.sum_cons]
    omega
  | cons_cons a _ ih => simpa only [List.sum_cons] using Nat.add_le_add_left ih a

private theorem sorted_names_cost (xs : List Nat) (lo : Nat)
    (hSorted : xs.Pairwise (· < ·)) (hLower : ∀ a ∈ xs, lo ≤ a) :
    xs.length * (xs.length + 5) + 2 * lo * xs.length ≤ 2 * (xs.map (· + 3)).sum := by
  induction xs generalizing lo with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨hHead, hTail⟩ := List.pairwise_cons.mp hSorted
    have hLo := hLower a List.mem_cons_self
    have h := ih (lo + 1) hTail fun b hb ↦
      Nat.succ_le_of_lt (Nat.lt_of_le_of_lt hLo (hHead b hb))
    simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.add_mul, Nat.mul_add,
      Nat.one_mul, Nat.mul_one] at h ⊢
    omega

private theorem distinct_names_cost (xs : List Nat) (hDistinct : xs.Nodup) :
    xs.length * (xs.length + 5) ≤ 2 * (xs.map (· + 3)).sum := by
  let sorted := xs.mergeSort
  have hPerm : List.Perm sorted xs := List.mergeSort_perm _ _
  have hWeak : sorted.Pairwise (fun a b ↦ decide (a ≤ b)) := by
    apply List.pairwise_mergeSort
    · intro a b c
      simp only [decide_eq_true_eq]
      exact Nat.le_trans
    · intro a b
      simpa only [Bool.or_eq_true, decide_eq_true_eq] using Nat.le_total a b
  have hStrict : sorted.Pairwise (· < ·) := by
    have hNe : sorted.Nodup := hPerm.symm.nodup hDistinct
    exact (List.pairwise_and_iff.mpr ⟨hWeak, hNe⟩).imp fun ⟨hle, hne⟩ ↦
      Nat.lt_of_le_of_ne (of_decide_eq_true hle) hne
  have hBound := sorted_names_cost sorted 0 hStrict fun a _ ↦ Nat.zero_le a
  simpa only [hPerm.length_eq, (hPerm.map (· + 3)).sum_nat, Nat.mul_zero, Nat.zero_mul,
    Nat.add_zero] using hBound

/-- Distinct indices cost at least the names `0, …, k - 1`, including literal framing. -/
theorem occurringIndices_length_bound (F : Formula Nat) :
    let k := (occurringIndices F).length
    k * (k + 5) + 2 + 4 * F.length ≤ 2 * (encode F).length := by
  dsimp only
  have hDistinct := distinct_names_cost _ (occurringIndices_nodup F)
  have hSublist : occurringIndices F <+ F.flatten.map literalIndex :=
    (eraseDups_nodup_sublist _).2
  have hSum := sum_le_sum_of_sublist (hSublist.map (· + 3))
  rw [List.map_map] at hSum
  change _ ≤ (F.flatten.map fun l ↦ literalIndex l + 3).sum at hSum
  rw [length_encode_eq]
  omega

/-- The number of occurring variables is at most the square root of twice the bit length. -/
theorem occurringIndices_length_sq_le (F : Formula Nat) :
    (occurringIndices F).length ^ 2 ≤ 2 * (encode F).length := by
  have h := occurringIndices_length_bound F
  dsimp only at h
  rw [Nat.mul_add] at h
  rw [Nat.pow_two]
  omega

end PvsNP.CNFCode
