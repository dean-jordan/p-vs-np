module

public import PvsNP.MCSP.StreamMerge

import Mathlib.Data.List.Induction

/-! # Streaming search for a circuit of bounded size -/

public section

namespace PvsNP.MCSP

open Circuits

structure StreamState (n : Nat) where
  seen : Nat
  circuit : BooleanCircuit n

/-- Before reading any rows, every circuit agrees with the empty prefix. -/
@[expose] def startStream (n : Nat) : StreamState n :=
  ⟨0, BooleanCircuit.const n false⟩

/-- Read a bit and replace the retained circuit. Failure ends all further requests. -/
@[expose] def pushBit {n : Nat} (merge : MergeOracle n)
    (before : Option (StreamState n)) (bit : Bool) : Option (StreamState n) :=
  match before with
  | none => none
  | some state =>
    if state.seen < 2 ^ n then
      (merge state.circuit state.seen bit).map fun c ↦ ⟨state.seen + 1, c⟩
    else none

@[expose] def runStream (n : Nat) (merge : MergeOracle n) (bits : BinaryWord) :
    Option (StreamState n) :=
  bits.foldl (pushBit merge) (some (startStream n))

@[expose] def searchStream (n : Nat) (merge : MergeOracle n) (bits : BinaryWord) :
    Option (BooleanCircuit n) :=
  match runStream n merge bits with
  | none => none
  | some state => if state.seen = 2 ^ n then some state.circuit else none

theorem runStream_append_bit (n : Nat) (merge : MergeOracle n) (bits : BinaryWord) (bit : Bool) :
    runStream n merge (bits ++ [bit]) = pushBit merge (runStream n merge bits) bit := by
  simp [runStream, List.foldl_append]

/-- A successful state counts exactly the rows read and represents their values. -/
theorem runStream_sound {n cap : Nat} {merge : MergeOracle n} (correct : CorrectMerge merge cap)
    {bits : BinaryWord} {state : StreamState n} (h : runStream n merge bits = some state) :
    state.seen = bits.length ∧ MatchesPrefix state.circuit bits ∧
      (bits ≠ [] → state.circuit.size ≤ cap) := by
  induction bits using List.reverseRecOn generalizing state with
  | nil =>
    change some (startStream n) = some state at h
    cases h
    simp [startStream, MatchesPrefix]
  | append_singleton pref bit ih =>
    rw [runStream_append_bit] at h
    cases hBefore : runStream n merge pref with
    | none => simp [hBefore, pushBit] at h
    | some old =>
      obtain ⟨hSeen, hPrefix, _⟩ := ih hBefore
      rw [hBefore] at h
      change (if old.seen < 2 ^ n then
        (merge old.circuit old.seen bit).map (fun c ↦ (⟨old.seen + 1, c⟩ : StreamState n))
        else none) = some state at h
      by_cases hRoom : old.seen < 2 ^ n
      · rw [ite_eq_left hRoom] at h
        cases hAnswer : merge old.circuit old.seen bit with
        | none => simp [hAnswer] at h
        | some candidate =>
          simp only [hAnswer, Option.map_some, Option.some.injEq] at h
          subst state
          obtain ⟨hSize, hAgrees⟩ := correct.sound _ _ _ _ hAnswer
          refine ⟨by simp [hSeen], ?_, fun _ ↦ hSize⟩
          exact (matchesPrefix_append_bit_iff pref bit hPrefix (hSeen ▸ hRoom)).mpr
            (hSeen ▸ hAgrees)
      · rw [ite_eq_right hRoom] at h
        contradiction

/-- Any bounded circuit for the requested prefix ensures that every request succeeds. -/
theorem runStream_complete {n cap : Nat} {merge : MergeOracle n} (correct : CorrectMerge merge cap)
    {bits : BinaryWord} (h : ∃ c : BooleanCircuit n, c.size ≤ cap ∧ MatchesPrefix c bits) :
    ∃ state, runStream n merge bits = some state := by
  induction bits using List.reverseRecOn with
  | nil => exact ⟨startStream n, rfl⟩
  | append_singleton pref bit ih =>
    obtain ⟨c, hSize, hPrefix⟩ := h
    obtain ⟨old, hBefore⟩ := ih ⟨c, hSize, matchesPrefix_of_append_bit hPrefix⟩
    obtain ⟨hSeen, hOld, _⟩ := runStream_sound correct hBefore
    have hRoom : pref.length < 2 ^ n := by
      have hLength := length_le_of_matchesPrefix hPrefix
      simp only [List.length_append, List.length_singleton] at hLength
      omega
    have hAgrees := (matchesPrefix_append_bit_iff pref bit hOld hRoom).mp hPrefix
    obtain ⟨candidate, hAnswer⟩ := correct.complete old.circuit old.seen bit
      ⟨c, hSize, hSeen.symm ▸ hAgrees⟩
    exact ⟨⟨old.seen + 1, candidate⟩, by
      simp only [runStream_append_bit, hBefore, pushBit, ite_eq_left (hSeen.symm ▸ hRoom),
        hAnswer, Option.map_some]⟩

theorem size_and_truthTable_of_searchStream_eq_some {n cap : Nat} {merge : MergeOracle n}
    (correct : CorrectMerge merge cap) {bits : BinaryWord} {c : BooleanCircuit n}
    (h : searchStream n merge bits = some c) : c.size ≤ cap ∧ truthTable n c.eval = bits := by
  unfold searchStream at h
  cases hRun : runStream n merge bits with
  | none => simp [hRun] at h
  | some state =>
    rw [hRun] at h
    change (if state.seen = 2 ^ n then some state.circuit else none) = some c at h
    by_cases hFull : state.seen = 2 ^ n
    · rw [ite_eq_left hFull] at h
      obtain ⟨hSeen, hPrefix, hSize⟩ := runStream_sound correct hRun
      have hLength : bits.length = 2 ^ n := hSeen.symm.trans hFull
      have hNonempty : bits ≠ [] := List.ne_nil_of_length_pos (hLength.symm ▸ Nat.two_pow_pos n)
      cases h
      refine ⟨hSize hNonempty, ?_⟩
      unfold MatchesPrefix at hPrefix
      rw [hLength, ← length_truthTable n state.circuit.eval, List.take_length] at hPrefix
      exact hPrefix
    · rw [ite_eq_right hFull] at h
      contradiction

theorem searchStream_isSome_iff {n cap : Nat} {merge : MergeOracle n}
    (correct : CorrectMerge merge cap) (bits : BinaryWord) :
    (searchStream n merge bits).isSome = true ↔ SizeBounded n cap bits := by
  rw [Option.isSome_iff_exists]
  constructor
  · rintro ⟨c, h⟩
    exact ⟨c, size_and_truthTable_of_searchStream_eq_some correct h⟩
  · rintro ⟨c, hSize, hTable⟩
    have hPrefix : MatchesPrefix c bits := by simp [MatchesPrefix, hTable]
    obtain ⟨state, hRun⟩ := runStream_complete correct ⟨c, hSize, hPrefix⟩
    have hSeen := (runStream_sound correct hRun).1
    have hFull : state.seen = 2 ^ n := by rw [hSeen, ← hTable, length_truthTable]
    exact ⟨state.circuit, by simp [searchStream, hRun, hFull]⟩

theorem referenceSearch_isSome_iff (n cap : Nat) (bits : BinaryWord) :
    (searchStream n (referenceMerge n cap) bits).isSome = true ↔ SizeBounded n cap bits :=
  searchStream_isSome_iff (referenceMerge_correct n cap) bits

end PvsNP.MCSP
