module

public import PvsNP.Complexity.PairEncoding

import Init.Data.List.Sublist

/-! # Binary witness search using a prefix-extension oracle -/

public section

namespace PvsNP

/-- Append one bit at a time, recording the query tried at each step. -/
@[expose] def extendWitness (oracle : BinaryWord → Bool) :
    Nat → BinaryWord → BinaryWord × List BinaryWord
  | 0, p => (p, [])
  | k + 1, p =>
    let query := p ++ [false]
    let rest := extendWitness oracle k (p ++ [!(oracle query)])
    (rest.1, query :: rest.2)

/-- Ask whether a witness exists before trying to extend the empty prefix. -/
@[expose] def prefixWitnessSearch (oracle : BinaryWord → Bool) (n : Nat) :
    Option BinaryWord × List BinaryWord :=
  if oracle [] then
    let result := extendWitness oracle n []
    (some result.1, [] :: result.2)
  else
    (none, [[]])

@[simp] theorem extendWitness_length (oracle : BinaryWord → Bool) (k : Nat) (p : BinaryWord) :
    (extendWitness oracle k p).1.length = p.length + k := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih =>
    simp only [extendWitness, ih, List.length_append, List.length_singleton]
    omega

theorem extendWitness_prefix (oracle : BinaryWord → Bool) (k : Nat) (p : BinaryWord) :
    p <+: (extendWitness oracle k p).1 := by
  induction k generalizing p with
  | zero => exact List.prefix_rfl
  | succ k ih =>
    simp only [extendWitness]
    exact (List.prefix_append p _).trans (ih _)

@[simp] theorem extendWitness_query_count (oracle : BinaryWord → Bool) (k : Nat) (p : BinaryWord) :
    (extendWitness oracle k p).2.length = k := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih => simp [extendWitness, ih]

theorem extendWitness_query_length_bounds (oracle : BinaryWord → Bool) (k : Nat)
    (p q : BinaryWord) (hq : q ∈ (extendWitness oracle k p).2) :
    p.length < q.length ∧ q.length ≤ p.length + k := by
  induction k generalizing p with
  | zero => simp [extendWitness] at hq
  | succ k ih =>
    simp only [extendWitness, List.mem_cons] at hq
    rcases hq with rfl | hq
    · simp only [List.length_append, List.length_singleton]
      omega
    · have hBounds := ih _ hq
      simp only [List.length_append, List.length_singleton] at hBounds
      omega

variable {oracle : BinaryWord → Bool} {n : Nat} {R : BinaryWord → Prop}

/-- The chosen bit preserves feasibility when the prefix has room to grow. -/
theorem prefixOracle_append_feasible
    (hOracle : ∀ p, oracle p = true ↔ ∃ w, w.length = n ∧ p <+: w ∧ R w)
    {p : BinaryWord} (hLength : p.length < n) (hFeasible : oracle p = true) :
    oracle (p ++ [!(oracle (p ++ [false]))]) = true := by
  cases hQuery : oracle (p ++ [false]) with
  | true => simp only [hQuery, Bool.not_true]
  | false =>
    obtain ⟨w, hWord, ⟨suffix, hSuffix⟩, hR⟩ := (hOracle p).mp hFeasible
    cases suffix with
    | nil =>
      simp only [List.append_nil] at hSuffix
      rw [← hSuffix] at hWord
      omega
    | cons bit tail =>
      have hPrefix : p ++ [bit] <+: w := ⟨tail, by rw [List.append_assoc]; exact hSuffix⟩
      have hBit : oracle (p ++ [bit]) = true := (hOracle _).mpr ⟨w, hWord, hPrefix, hR⟩
      cases bit with
      | false => simp [hQuery] at hBit
      | true => simpa only [hQuery, Bool.not_false] using hBit

/-- Extending a feasible prefix to full length returns a witness extending it. -/
theorem extendWitness_spec
    (hOracle : ∀ p, oracle p = true ↔ ∃ w, w.length = n ∧ p <+: w ∧ R w)
    {k : Nat} {p : BinaryWord} (hLength : p.length + k = n) (hFeasible : oracle p = true) :
    p <+: (extendWitness oracle k p).1 ∧ (extendWitness oracle k p).1.length = n ∧
      R (extendWitness oracle k p).1 := by
  refine ⟨extendWitness_prefix oracle k p, (extendWitness_length oracle k p).trans hLength, ?_⟩
  induction k generalizing p with
  | zero =>
    obtain ⟨w, hWord, hPrefix, hR⟩ := (hOracle p).mp hFeasible
    have hp : p = w := hPrefix.eq_of_length (hLength.trans hWord.symm)
    exact hp ▸ hR
  | succ k ih =>
    simp only [extendWitness]
    apply ih
    · simp only [List.length_append, List.length_singleton]
      omega
    · exact prefixOracle_append_feasible hOracle (by omega) hFeasible

/-- A successful search returns a full-length word satisfying the relation. -/
theorem prefixWitnessSearch_sound
    (hOracle : ∀ p, oracle p = true ↔ ∃ w, w.length = n ∧ p <+: w ∧ R w)
    {w : BinaryWord} (hResult : (prefixWitnessSearch oracle n).1 = some w) :
    w.length = n ∧ R w := by
  cases hEmpty : oracle [] with
  | false => simp [prefixWitnessSearch, hEmpty] at hResult
  | true =>
    have hWord : (extendWitness oracle n []).1 = w := by
      simpa [prefixWitnessSearch, hEmpty] using hResult
    rw [← hWord]
    exact (extendWitness_spec hOracle (k := n) (p := []) (Nat.zero_add n) hEmpty).2

/-- The search succeeds exactly when a full-length witness exists. -/
theorem prefixWitnessSearch_complete
    (hOracle : ∀ p, oracle p = true ↔ ∃ w, w.length = n ∧ p <+: w ∧ R w) :
    (∃ w, (prefixWitnessSearch oracle n).1 = some w) ↔ ∃ w, w.length = n ∧ R w := by
  constructor
  · rintro ⟨w, hResult⟩
    exact ⟨w, prefixWitnessSearch_sound hOracle hResult⟩
  · rintro ⟨w, hWord, hR⟩
    have hEmpty : oracle [] = true := (hOracle []).mpr ⟨w, hWord, List.nil_prefix, hR⟩
    exact ⟨(extendWitness oracle n []).1, by simp [prefixWitnessSearch, hEmpty]⟩

theorem prefixWitnessSearch_none_iff
    (hOracle : ∀ p, oracle p = true ↔ ∃ w, w.length = n ∧ p <+: w ∧ R w) :
    (prefixWitnessSearch oracle n).1 = none ↔ ¬ ∃ w, w.length = n ∧ R w := by
  have hEmpty : (prefixWitnessSearch oracle n).1 = none ↔ oracle [] ≠ true := by
    cases h : oracle [] <;> simp [prefixWitnessSearch, h]
  rw [hEmpty, Ne, hOracle]
  simp

theorem prefixWitnessSearch_query_count (oracle : BinaryWord → Bool) (n : Nat) :
    (prefixWitnessSearch oracle n).2.length = if oracle [] then n + 1 else 1 := by
  cases h : oracle [] <;> simp [prefixWitnessSearch, h]

theorem prefixWitnessSearch_query_count_le (oracle : BinaryWord → Bool) (n : Nat) :
    (prefixWitnessSearch oracle n).2.length ≤ n + 1 := by
  rw [prefixWitnessSearch_query_count]
  split <;> omega

theorem prefixWitnessSearch_query_length_le (oracle : BinaryWord → Bool) (n : Nat)
    (q : BinaryWord) (hq : q ∈ (prefixWitnessSearch oracle n).2) : q.length ≤ n := by
  cases hEmpty : oracle [] with
  | false =>
    have hNil : q = [] := by simpa [prefixWitnessSearch, hEmpty] using hq
    simp [hNil]
  | true =>
    have hQueries : q = [] ∨ q ∈ (extendWitness oracle n []).2 := by
      simpa [prefixWitnessSearch, hEmpty] using hq
    rcases hQueries with rfl | hq
    · exact Nat.zero_le n
    · have hLength := (extendWitness_query_length_bounds oracle n [] q hq).2
      rwa [List.length_nil, Nat.zero_add] at hLength

end PvsNP
