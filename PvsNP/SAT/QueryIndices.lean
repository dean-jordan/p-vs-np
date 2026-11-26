module

public import PvsNP.SAT.AppendQuery

import Mathlib.Data.List.Induction

/-! # Static stop positions for appended SAT queries

The length of a unit clause depends on its variable index. Its sign can
change during search, while the unary index and its stop position are fixed.
-/

@[expose] public section

namespace PvsNP.SATSearch

/-- Absolute position of the final terminator after appending `i` unit clauses. -/
def queryTail (n : Nat) : Nat → Nat
  | 0 => n - 1
  | i + 1 => queryTail n i + i + 5

@[simp] theorem queryTail_zero (n : Nat) : queryTail n 0 = n - 1 := rfl

theorem queryTail_succ (n i : Nat) : queryTail n (i + 1) = queryTail n i + i + 5 := rfl

/-- The absolute positions of the zero terminating each newly written unary index. -/
def unaryStopPositions (n k : Nat) : List Nat :=
  (List.range k).map (fun i ↦ queryTail n i + 3 + i)

theorem length_appendPrefixQuery_eq_queryTail_succ (word pref : BinaryWord)
    (hWord : word ≠ []) :
    (appendPrefixQuery word pref).length = queryTail word.length pref.length + 1 := by
  induction pref using List.reverseRecOn with
  | nil =>
    simp only [appendPrefixQuery_nil, List.length_nil, queryTail_zero]
    have hLength := List.length_pos_iff.mpr hWord
    omega
  | append_singleton pref bit ih =>
    have hBefore : appendPrefixQuery word pref ≠ [] :=
      List.length_pos_iff.mp (by rw [ih]; omega)
    rw [appendPrefixQuery_append_bit, length_appendUnitQuery_of_ne_nil hBefore, ih]
    simp only [List.length_append, List.length_singleton, queryTail_succ]
    omega

theorem dropLast_length_appendPrefixQuery (word pref : BinaryWord) (hWord : word ≠ []) :
    (appendPrefixQuery word pref).dropLast.length = queryTail word.length pref.length := by
  simp only [List.length_dropLast, length_appendPrefixQuery_eq_queryTail_succ word pref hWord,
    Nat.add_sub_cancel]

private theorem queryTail_le (n : Nat) {i j : Nat} (h : i ≤ j) :
    queryTail n i ≤ queryTail n j := by
  induction j with
  | zero =>
    have hi : i = 0 := by omega
    subst i
    exact Nat.le_refl _
  | succ j ih =>
    by_cases hBefore : i ≤ j
    · have hStep : queryTail n j ≤ queryTail n (j + 1) := by rw [queryTail_succ]; omega
      exact (ih hBefore).trans hStep
    · have hi : i = j + 1 := by omega
      subst i
      exact Nat.le_refl _

private theorem unary_stop_lt_tail (n : Nat) {i j : Nat} (h : i < j) :
    queryTail n i + 3 + i < queryTail n j := by
  have hNext := queryTail_le n (Nat.succ_le_of_lt h)
  rw [queryTail_succ] at hNext
  omega

/-- During any stage's unary scan, the schedule marks exactly that stage's final position. -/
theorem contains_unaryStopPositions (n k i a : Nat) (hi : i < k) (ha : a ≤ i) :
    (unaryStopPositions n k).contains (queryTail n i + 3 + a) = decide (a = i) := by
  apply Bool.eq_iff_iff.mpr
  rw [List.contains_iff_mem, decide_eq_true_eq]
  constructor
  · intro h
    obtain ⟨j, _, hPos⟩ := List.mem_map.mp h
    rcases Nat.lt_trichotomy j i with hji | rfl | hij
    · have hBefore := unary_stop_lt_tail n hji
      omega
    · omega
    · have hAfter := unary_stop_lt_tail n hij
      omega
  · intro h
    subst a
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

private theorem prefixQueryLengthFrom_next (i n k : Nat) :
    prefixQueryLengthFrom i n (k + 1) = prefixQueryLengthFrom i n k + (i + k + 5) := by
  induction k generalizing i with
  | zero => simp only [prefixQueryLengthFrom_cons, prefixQueryLengthFrom_nil, Nat.add_zero,
      Nat.add_comm]
  | succ k ih =>
    rw [prefixQueryLengthFrom_cons i n (k + 1), prefixQueryLengthFrom_cons i n k, ih (i + 1)]
    omega

theorem queryTail_add_one_eq_prefixQueryLength (n k : Nat) (hn : 0 < n) :
    queryTail n k + 1 = prefixQueryLength n k := by
  unfold prefixQueryLength
  induction k with
  | zero => simp only [queryTail_zero, prefixQueryLengthFrom_nil]; omega
  | succ k ih =>
    rw [queryTail_succ, prefixQueryLengthFrom_next, ← ih]
    omega

theorem queryTail_add_one_le (n k : Nat) (hn : 0 < n) (hk : k ≤ n) :
    queryTail n k + 1 ≤ n + n * (n + 5) := by
  rw [queryTail_add_one_eq_prefixQueryLength n k hn]
  exact prefixQueryLength_le n k hk

end PvsNP.SATSearch
