module

public import PvsNP.Circuits.Description
public import PvsNP.Complexity.PrefixWitnessSearch
public import PvsNP.MCSP.StreamMerge

import Init.Data.List.TakeDrop

/-! # Finding a merge circuit from a prefix feasibility oracle -/

public section

namespace PvsNP.MCSP

open Circuits

variable {n : Nat}

/-- The length of a circuit description padded to the full gate budget. -/
@[expose] def mergeWitnessLength (n cap : Nat) : Nat :=
  let w := circuitFieldWidth n cap
  2 * w + cap * (3 + 2 * w)

/-- Put every bounded circuit description in a word of the same length. -/
@[expose] def encodeMergeWitness (cap : Nat) (c : BooleanCircuit n) : BinaryWord :=
  let code := encodeCircuit cap c
  code ++ List.replicate (mergeWitnessLength n cap - code.length) false

@[simp] theorem length_encodeMergeWitness (cap : Nat) (c : BooleanCircuit n)
    (hSize : c.size ≤ cap) : (encodeMergeWitness cap c).length = mergeWitnessLength n cap := by
  have hLength : (encodeCircuit cap c).length ≤ mergeWitnessLength n cap :=
    length_encodeCircuit_le cap c hSize
  simp only [encodeMergeWitness, List.length_append, List.length_replicate]
  omega

/-- Use the gate count header to remove the padding and decode the original circuit. -/
@[expose] def decodeMergeWitness (n cap : Nat) (word : BinaryWord) : Option (BooleanCircuit n) :=
  let w := circuitFieldWidth n cap
  let count := fieldValue (word.take w)
  let codeLength := 2 * w + count * (3 + 2 * w)
  if word.length = mergeWitnessLength n cap ∧ (word.drop codeLength).all (!·) then
    decodeCircuit n cap (word.take codeLength)
  else
    none

theorem decodeMergeWitness_encodeMergeWitness (cap : Nat) (c : BooleanCircuit n)
    (hSize : c.size ≤ cap) : decodeMergeWitness n cap (encodeMergeWitness cap c) = some c := by
  have hWidth : circuitFieldWidth n cap ≤ (encodeCircuit cap c).length := by
    rw [length_encodeCircuit]
    omega
  have hTake : (encodeMergeWitness cap c).take (circuitFieldWidth n cap) =
      (encodeCircuit cap c).take (circuitFieldWidth n cap) := by
    rw [encodeMergeWitness, List.take_append_of_le_length hWidth]
  rw [decodeMergeWitness, hTake, fieldValue_take_encodeCircuit cap c hSize,
    ← length_encodeCircuit cap c, length_encodeMergeWitness cap c hSize]
  simp [encodeMergeWitness, decodeCircuit_encodeCircuit, hSize]

/-- A feasible prefix extends to the padded description of an agreeing bounded circuit. -/
@[expose] def MergePrefixFeasible (cap : Nat) (old : BooleanCircuit n) (seen : Nat)
    (bit : Bool) (pref : BinaryWord) : Prop :=
  ∃ c, c.size ≤ cap ∧ MergeAgrees old seen bit c ∧ pref <+: encodeMergeWitness cap c

theorem mergePrefixFeasible_nil_iff (cap : Nat) (old : BooleanCircuit n) (seen : Nat) (bit : Bool) :
    MergePrefixFeasible cap old seen bit [] ↔ ∃ c, c.size ≤ cap ∧ MergeAgrees old seen bit c := by
  simp [MergePrefixFeasible, List.nil_prefix]

abbrev MergePrefixOracle (n : Nat) := BooleanCircuit n → Nat → Bool → BinaryWord → Bool

/-- An exact feasibility oracle for all merge requests and candidate prefixes. -/
@[expose] def CorrectMergePrefixOracle (oracle : MergePrefixOracle n) (cap : Nat) : Prop :=
  ∀ old seen bit pref, oracle old seen bit pref = true ↔ MergePrefixFeasible cap old seen bit pref

/-- Recover an agreeing circuit and record the prefix queries used to find it. -/
@[expose] def searchMergeWithPrefix (cap : Nat) (oracle : MergePrefixOracle n)
    (old : BooleanCircuit n) (seen : Nat) (bit : Bool) :
    Option (BooleanCircuit n) × List BinaryWord :=
  let result := prefixWitnessSearch (oracle old seen bit) (mergeWitnessLength n cap)
  (result.1.bind (decodeMergeWitness n cap), result.2)

/-- The search result alone can be used as a merger. -/
@[expose] def mergeByPrefixSearch (cap : Nat) (oracle : MergePrefixOracle n) : MergeOracle n :=
  fun old seen bit ↦ (searchMergeWithPrefix cap oracle old seen bit).1

private theorem prefixSearchOracle_spec {cap : Nat} {oracle : MergePrefixOracle n}
    (hOracle : CorrectMergePrefixOracle oracle cap) (old : BooleanCircuit n) (seen : Nat)
    (bit : Bool) (pref : BinaryWord) :
    oracle old seen bit pref = true ↔
      ∃ word, word.length = mergeWitnessLength n cap ∧ pref <+: word ∧
        ∃ c, c.size ≤ cap ∧ MergeAgrees old seen bit c ∧ word = encodeMergeWitness cap c := by
  rw [hOracle old seen bit pref]
  constructor
  · rintro ⟨c, hSize, hAgrees, hPrefix⟩
    exact ⟨encodeMergeWitness cap c, length_encodeMergeWitness cap c hSize, hPrefix,
      c, hSize, hAgrees, rfl⟩
  · rintro ⟨_, _, hPrefix, c, hSize, hAgrees, rfl⟩
    exact ⟨c, hSize, hAgrees, hPrefix⟩

theorem mergeByPrefixSearch_correct {cap : Nat} {oracle : MergePrefixOracle n}
    (hOracle : CorrectMergePrefixOracle oracle cap) :
    CorrectMerge (mergeByPrefixSearch cap oracle) cap := by
  constructor
  · intro old seen bit candidate hFound
    obtain ⟨word, hSearch, hDecode⟩ := Option.bind_eq_some_iff.mp hFound
    obtain ⟨c, hSize, hAgrees, rfl⟩ :=
      (prefixWitnessSearch_sound (prefixSearchOracle_spec hOracle old seen bit) hSearch).2
    rw [decodeMergeWitness_encodeMergeWitness cap c hSize] at hDecode
    cases hDecode
    exact ⟨hSize, hAgrees⟩
  · rintro old seen bit ⟨c, hSize, hAgrees⟩
    obtain ⟨word, hSearch⟩ :=
      (prefixWitnessSearch_complete (prefixSearchOracle_spec hOracle old seen bit)).mpr
        ⟨encodeMergeWitness cap c, length_encodeMergeWitness cap c hSize, c, hSize, hAgrees, rfl⟩
    obtain ⟨candidate, hCandidateSize, _, rfl⟩ :=
      (prefixWitnessSearch_sound (prefixSearchOracle_spec hOracle old seen bit) hSearch).2
    refine ⟨candidate, ?_⟩
    simp only [mergeByPrefixSearch, searchMergeWithPrefix, hSearch, Option.bind_some,
      decodeMergeWitness_encodeMergeWitness cap candidate hCandidateSize]

theorem searchMergeWithPrefix_query_count_le (cap : Nat) (oracle : MergePrefixOracle n)
    (old : BooleanCircuit n) (seen : Nat) (bit : Bool) :
    (searchMergeWithPrefix cap oracle old seen bit).2.length ≤ mergeWitnessLength n cap + 1 :=
  prefixWitnessSearch_query_count_le (oracle old seen bit) (mergeWitnessLength n cap)

theorem searchMergeWithPrefix_query_length_le (cap : Nat) (oracle : MergePrefixOracle n)
    (old : BooleanCircuit n) (seen : Nat) (bit : Bool) {query : BinaryWord}
    (hQuery : query ∈ (searchMergeWithPrefix cap oracle old seen bit).2) :
    query.length ≤ mergeWitnessLength n cap :=
  prefixWitnessSearch_query_length_le (oracle old seen bit) _ query hQuery

end PvsNP.MCSP
