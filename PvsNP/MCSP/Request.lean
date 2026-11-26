module

public import PvsNP.Complexity.Classes
public import PvsNP.MCSP.MergeSearch

import Init.Data.List.TakeDrop

/-! # Binary requests for bounded merge prefix feasibility -/

public section

namespace PvsNP.MCSP

open Circuits

/-- A merge query with all the bounds needed to encode it as binary input. -/
structure MergeRequest where
  arity : Nat
  cap : Nat
  old : BooleanCircuit arity
  seen : Nat
  bit : Bool
  pref : BinaryWord
  seen_le : seen ≤ 2 ^ arity
  old_size_le : old.size ≤ max 1 cap
  pref_length_le : pref.length ≤ mergeWitnessLength arity cap

@[expose] def unaryField (n : Nat) : BinaryWord := List.replicate n true ++ [false]

/-- Read a unary count followed by its zero terminator. -/
@[expose] def readUnaryField : BinaryWord → Option (Nat × BinaryWord)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => (readUnaryField rest).map fun (n, suffix) ↦ (n + 1, suffix)

theorem readUnaryField_append (n : Nat) (rest : BinaryWord) :
    readUnaryField (unaryField n ++ rest) = some (n, rest) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (readUnaryField (unaryField n ++ rest)).map _ = _
    rw [ih]
    rfl

theorem readUnaryField_eq_some_iff {word rest : BinaryWord} {n : Nat} :
    readUnaryField word = some (n, rest) ↔ word = unaryField n ++ rest := by
  constructor
  · induction word generalizing n rest with
    | nil => simp [readUnaryField]
    | cons bit tail ih =>
      cases bit
      · intro h
        obtain ⟨rfl, rfl⟩ := by simpa [readUnaryField] using h
        rfl
      · intro h
        obtain ⟨⟨k, suffix⟩, hTail, hFields⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨rfl, rfl⟩ := by simpa using hFields
        have hTail' := ih hTail
        simp [hTail', unaryField, List.replicate_succ]
  · rintro rfl
    exact readUnaryField_append _ _

/-- Unary arity and cap, a fixed-width row counter, the new bit, a padded old
circuit description, and the candidate prefix. The prefix is the remaining suffix. -/
@[expose] def encodeMergeRequest (r : MergeRequest) : BinaryWord :=
  unaryField r.arity ++ (unaryField r.cap ++ (fieldBits (r.arity + 1) r.seen ++
    (r.bit :: (encodeMergeWitness (max 1 r.cap) r.old ++ r.pref))))

private theorem old_size_of_decodeMergeWitness {n cap : Nat} {word : BinaryWord}
    {c : BooleanCircuit n} (h : decodeMergeWitness n cap word = some c) : c.size ≤ cap := by
  simp only [decodeMergeWitness] at h
  split at h
  · exact size_le_of_decodeCircuit_eq_some h
  · contradiction

private def parseMergeRequest (word : BinaryWord) : Option MergeRequest := do
  let (arity, rest) ← readUnaryField word
  let (cap, rest) ← readUnaryField rest
  let seen := fieldValue (rest.take (arity + 1))
  if hSeen : seen ≤ 2 ^ arity then
    match rest.drop (arity + 1) with
    | [] => none
    | bit :: rest =>
      let oldWidth := mergeWitnessLength arity (max 1 cap)
      let pref := rest.drop oldWidth
      if hPrefix : pref.length ≤ mergeWitnessLength arity cap then
        match hOld : decodeMergeWitness arity (max 1 cap) (rest.take oldWidth) with
        | none => none
        | some old =>
          some ⟨arity, cap, old, seen, bit, pref, hSeen, old_size_of_decodeMergeWitness hOld,
            hPrefix⟩
      else none
  else none

/-- Parse a request and check that its binary representation is canonical. -/
def decodeMergeRequest (word : BinaryWord) : Option MergeRequest := do
  let r ← parseMergeRequest word
  if encodeMergeRequest r = word then some r else none

private theorem parseMergeRequest_encodeMergeRequest (r : MergeRequest) :
    parseMergeRequest (encodeMergeRequest r) = some r := by
  have hFit : r.seen < 2 ^ (r.arity + 1) := by
    rw [Nat.pow_succ]
    have hPos := Nat.two_pow_pos r.arity
    have hSeen := r.seen_le
    omega
  have hRow := length_fieldBits (r.arity + 1) r.seen
  have hOld := length_encodeMergeWitness (max 1 r.cap) r.old r.old_size_le
  have hDecoded : decodeMergeWitness r.arity (max 1 r.cap)
      ((encodeMergeWitness (max 1 r.cap) r.old ++ r.pref).take
        (mergeWitnessLength r.arity (max 1 r.cap))) = some r.old := by
    rw [List.take_left' hOld, decodeMergeWitness_encodeMergeWitness _ _ r.old_size_le]
  simp only [parseMergeRequest, encodeMergeRequest, readUnaryField_append, Option.bind_eq_bind,
    Option.bind_some, List.take_left' hRow, fieldValue_bits _ _ hFit, dite_eq_left r.seen_le,
    List.drop_left' hRow, List.drop_left' hOld, dite_eq_left r.pref_length_le]
  split
  next hNone => simp [hDecoded] at hNone
  next old hSome =>
    rw [hDecoded, Option.some.injEq] at hSome
    subst old
    rfl

@[simp] theorem decodeMergeRequest_encodeMergeRequest (r : MergeRequest) :
    decodeMergeRequest (encodeMergeRequest r) = some r := by
  simp [decodeMergeRequest, parseMergeRequest_encodeMergeRequest]

theorem decodeMergeRequest_eq_some_iff {word : BinaryWord} {r : MergeRequest} :
    decodeMergeRequest word = some r ↔ encodeMergeRequest r = word := by
  constructor
  · intro h
    obtain ⟨request, _, hFound⟩ := Option.bind_eq_some_iff.mp h
    split at hFound
    · cases hFound
      assumption
    · contradiction
  · rintro rfl
    exact decodeMergeRequest_encodeMergeRequest r

/-- Only the candidate prefix can vary in length once arity and cap are fixed. -/
theorem length_encodeMergeRequest (r : MergeRequest) :
    (encodeMergeRequest r).length = 2 * r.arity + r.cap + 4 +
      mergeWitnessLength r.arity (max 1 r.cap) + r.pref.length := by
  simp only [encodeMergeRequest, unaryField, List.length_append, List.length_replicate,
    length_fieldBits, List.length_cons, List.length_nil,
    length_encodeMergeWitness _ _ r.old_size_le]
  omega

theorem arity_add_cap_le_length_encodeMergeRequest (r : MergeRequest) :
    r.arity + r.cap ≤ (encodeMergeRequest r).length := by
  rw [length_encodeMergeRequest]
  omega

/-- The unary fields, counter, bit, old circuit, and longest admissible prefix. -/
@[expose] def mergeRequestLengthBound (n cap : Nat) : Nat :=
  2 * n + cap + 4 + mergeWitnessLength n (max 1 cap) + mergeWitnessLength n cap

theorem length_encodeMergeRequest_le (r : MergeRequest) :
    (encodeMergeRequest r).length ≤ mergeRequestLengthBound r.arity r.cap := by
  rw [length_encodeMergeRequest, mergeRequestLengthBound]
  exact Nat.add_le_add_left r.pref_length_le _

private theorem mergeWitnessLength_le_quadratic {n cap k : Nat}
    (hK : 1 ≤ k) (hArity : n < k) (hCap : cap ≤ k) :
    mergeWitnessLength n cap ≤ 11 * (k * k) := by
  let w := circuitFieldWidth n cap
  have hLog := Nat.log2_le_self (n + cap)
  have hWidth : w ≤ 2 * k := by
    change (n + cap).log2 + 1 ≤ 2 * k
    omega
  have hGates : cap * (3 + 2 * w) ≤ k * (7 * k) := Nat.mul_le_mul hCap (by omega)
  rw [Nat.mul_comm k (7 * k), Nat.mul_assoc] at hGates
  have hSquare : k ≤ k * k := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left k hK
  change 2 * w + cap * (3 + 2 * w) ≤ 11 * (k * k)
  omega

theorem mergeRequestLengthBound_le_quadratic (n cap : Nat) :
    mergeRequestLengthBound n cap ≤ 26 * (n + cap + 1) ^ 2 := by
  let k := n + cap + 1
  have hK : 1 ≤ k := by omega
  have hArity : n < k := by omega
  have hCap : cap ≤ k := by omega
  have hOldCap : max 1 cap ≤ k := Nat.max_le.mpr ⟨hK, hCap⟩
  have hOld := mergeWitnessLength_le_quadratic hK hArity hOldCap
  have hPrefix := mergeWitnessLength_le_quadratic hK hArity hCap
  have hBase : 2 * n + cap + 4 ≤ 4 * k := by omega
  have hSquare : k ≤ k * k := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left k hK
  rw [mergeRequestLengthBound, Nat.pow_two]
  change _ ≤ 26 * (k * k)
  omega

/-- Witness length is polynomial in the raw input length of a decoded request. -/
theorem mergeWitnessLength_le_of_decodeMergeRequest {word : BinaryWord} {r : MergeRequest}
    (h : decodeMergeRequest word = some r) :
    mergeWitnessLength r.arity r.cap ≤ 11 * (word.length + 1) ^ 2 := by
  have hSize := arity_add_cap_le_length_encodeMergeRequest r
  rw [decodeMergeRequest_eq_some_iff.mp h] at hSize
  rw [Nat.pow_two]
  exact mergeWitnessLength_le_quadratic (by omega) (by omega) (by omega)

/-- The language of canonical binary requests with a feasible candidate prefix. -/
@[expose] def MergePrefixLanguage : BinaryLanguage :=
  {word | ∃ r, decodeMergeRequest word = some r ∧
    MergePrefixFeasible r.cap r.old r.seen r.bit r.pref}

@[simp] theorem encodeMergeRequest_mem_mergePrefixLanguage (r : MergeRequest) :
    encodeMergeRequest r ∈ MergePrefixLanguage ↔
      MergePrefixFeasible r.cap r.old r.seen r.bit r.pref := by
  change (∃ request, decodeMergeRequest (encodeMergeRequest r) = some request ∧
    MergePrefixFeasible request.cap request.old request.seen request.bit request.pref) ↔ _
  simp only [decodeMergeRequest_encodeMergeRequest, Option.some.injEq, exists_eq_left']

end PvsNP.MCSP
