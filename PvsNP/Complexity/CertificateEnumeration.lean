module

public import Init.Data.List.Lemmas
public import Init.Data.List.Range

import Init.Data.List.Nat.Sum

/-! # Executable enumeration of bounded-length certificates -/

public section

namespace PvsNP

variable {α : Type} {alphabet : List α} {word : List α} {k : Nat}

/-- Enumerate the words of a prescribed length over a list of symbols. -/
@[expose] def wordsOfLength (alphabet : List α) : Nat → List (List α)
  | 0 => [[]]
  | k + 1 => alphabet.flatMap fun a ↦ (wordsOfLength alphabet k).map (a :: ·)

/-- Enumerate the words of lengths zero through `k`, in length order. -/
@[expose] def wordsUpToLength (alphabet : List α) : Nat → List (List α)
  | 0 => wordsOfLength alphabet 0
  | k + 1 => wordsUpToLength alphabet k ++ wordsOfLength alphabet (k + 1)

theorem mem_wordsOfLength_iff :
    word ∈ wordsOfLength alphabet k ↔ word.length = k ∧ ∀ a ∈ word, a ∈ alphabet := by
  induction k generalizing word with
  | zero => cases word <;> simp [wordsOfLength]
  | succ k ih =>
    rw [wordsOfLength, List.mem_flatMap]
    constructor
    · rintro ⟨a, ha, hWord⟩
      obtain ⟨tail, hTail, rfl⟩ := List.mem_map.mp hWord
      obtain ⟨hLen, hAlphabet⟩ := ih.mp hTail
      refine ⟨congrArg (· + 1) hLen, ?_⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ha
      · exact hAlphabet b hb
    · rintro ⟨hLen, hAlphabet⟩
      cases word with
      | nil => simp at hLen
      | cons a tail =>
        refine ⟨a, hAlphabet a (List.mem_cons_self ..), List.mem_map.mpr ⟨tail, ?_, rfl⟩⟩
        exact ih.mpr ⟨Nat.succ.inj hLen, fun b hb ↦ hAlphabet b (List.mem_cons_of_mem _ hb)⟩

theorem mem_wordsUpToLength_iff :
    word ∈ wordsUpToLength alphabet k ↔ word.length ≤ k ∧ ∀ a ∈ word, a ∈ alphabet := by
  induction k with
  | zero => simp [wordsUpToLength, mem_wordsOfLength_iff]
  | succ k ih =>
    simp only [wordsUpToLength, List.mem_append, ih, mem_wordsOfLength_iff]
    constructor
    · rintro (⟨hLen, hAlphabet⟩ | ⟨hLen, hAlphabet⟩) <;> exact ⟨by omega, hAlphabet⟩
    · rintro ⟨hLen, hAlphabet⟩
      by_cases h : word.length ≤ k
      · exact Or.inl ⟨h, hAlphabet⟩
      · exact Or.inr ⟨by omega, hAlphabet⟩

theorem mem_wordsOfLength_iff_of_covers (hCovers : ∀ a : α, a ∈ alphabet) :
    word ∈ wordsOfLength alphabet k ↔ word.length = k := by
  simp [mem_wordsOfLength_iff, hCovers]

theorem mem_wordsUpToLength_iff_of_covers (hCovers : ∀ a : α, a ∈ alphabet) :
    word ∈ wordsUpToLength alphabet k ↔ word.length ≤ k := by
  simp [mem_wordsUpToLength_iff, hCovers]

/-- The exact count uses the alphabet list length, including any repetitions. -/
@[simp] theorem length_wordsOfLength (alphabet : List α) (k : Nat) :
    (wordsOfLength alphabet k).length = alphabet.length ^ k := by
  induction k with
  | zero => simp [wordsOfLength]
  | succ k ih =>
    simp only [wordsOfLength, List.length_flatMap, List.length_map, List.map_const',
      List.sum_replicate_nat, ih, Nat.pow_succ, Nat.mul_comm]

theorem length_wordsUpToLength (alphabet : List α) (k : Nat) :
    (wordsUpToLength alphabet k).length =
      ((List.range (k + 1)).map fun j ↦ alphabet.length ^ j).sum := by
  induction k with
  | zero => simp [wordsUpToLength]
  | succ k ih =>
    rw [wordsUpToLength, List.length_append, ih, length_wordsOfLength,
      List.range_succ (n := k + 1), List.map_append, List.sum_append_nat]
    rfl

/-- Every size contribution is bounded by the count for maximum-length words. -/
theorem length_wordsUpToLength_le (alphabet : List α) (k : Nat) (hPos : 0 < alphabet.length) :
    (wordsUpToLength alphabet k).length ≤ (k + 1) * alphabet.length ^ k := by
  induction k with
  | zero => simp [wordsUpToLength]
  | succ k ih =>
    rw [wordsUpToLength, List.length_append, length_wordsOfLength]
    calc
      _ ≤ (k + 1) * alphabet.length ^ k + alphabet.length ^ (k + 1) :=
        Nat.add_le_add_right ih _
      _ ≤ (k + 1) * alphabet.length ^ (k + 1) + alphabet.length ^ (k + 1) :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hPos (Nat.le_succ k))) _
      _ = _ := (Nat.succ_mul ..).symm

end PvsNP
