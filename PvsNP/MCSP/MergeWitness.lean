module

public import PvsNP.Circuits.Description
public import PvsNP.MCSP.MergeViolation
public import PvsNP.MCSP.MergeSearch
public import PvsNP.MCSP.Streaming

/-! # A short binary witness with a row check for each merge request -/

public section

namespace PvsNP.MCSP

open Circuits

/-- A malformed circuit description fails on every row. A valid description passes on a row
exactly when that row does not witness a violation. -/
@[expose] def checkMergeRow {n : Nat} (cap : Nat) (old : BooleanCircuit n) (seen : Nat) (bit : Bool)
    (code : BinaryWord) (x : Fin n → Bool) : Bool :=
  match decodeCircuit n cap code with
  | none => false
  | some c => !(mergeViolationCircuit old seen bit c).eval x

/-- The two quantifiers range over a bounded binary description and one table row. -/
theorem exists_bounded_merge_iff_short_code {n : Nat} (cap : Nat) (old : BooleanCircuit n)
    (seen : Nat) (bit : Bool) :
    (∃ c : BooleanCircuit n, c.size ≤ cap ∧ MergeAgrees old seen bit c) ↔
      ∃ code : BinaryWord,
        code.length ≤ 2 * circuitFieldWidth n cap + cap * (3 + 2 * circuitFieldWidth n cap) ∧
          ∀ x : Fin n → Bool, checkMergeRow cap old seen bit code x = true := by
  constructor
  · rintro ⟨c, hSize, hAgrees⟩
    refine ⟨encodeCircuit cap c, length_encodeCircuit_le cap c hSize, fun x ↦ ?_⟩
    have hRow := (mergeAgrees_iff_forall_mergeViolationCircuit_eq_false old seen bit c).mp hAgrees x
    simp [checkMergeRow, decodeCircuit_encodeCircuit cap c hSize, hRow]
  · rintro ⟨code, _, hRows⟩
    cases hCode : decodeCircuit n cap code with
    | none =>
      have hRow := hRows (fun _ ↦ false)
      simp [checkMergeRow, hCode] at hRow
    | some c =>
      refine ⟨c, size_le_of_decodeCircuit_eq_some hCode,
        (mergeAgrees_iff_forall_mergeViolationCircuit_eq_false old seen bit c).mpr fun x ↦ ?_⟩
      have hRow := hRows x
      simpa [checkMergeRow, hCode] using hRow

/-- This check also validates the requested prefix and the canonical padded encoding. -/
@[expose] def checkMergePrefixRow {n : Nat} (cap : Nat) (old : BooleanCircuit n) (seen : Nat)
    (bit : Bool) (pref word : BinaryWord) (x : Fin n → Bool) : Bool :=
  match decodeMergeWitness n cap word with
  | none => false
  | some c =>
    decide (c.size ≤ cap ∧ word = encodeMergeWitness cap c ∧ word.take pref.length = pref) &&
      !(mergeViolationCircuit old seen bit c).eval x

/-- Prefix feasibility itself has a bounded existential-universal binary witness. -/
theorem mergePrefixFeasible_iff_checked_rows {n : Nat} (cap : Nat) (old : BooleanCircuit n)
    (seen : Nat) (bit : Bool) (pref : BinaryWord) :
    MergePrefixFeasible cap old seen bit pref ↔
      ∃ word : BinaryWord, word.length = mergeWitnessLength n cap ∧
        ∀ x : Fin n → Bool, checkMergePrefixRow cap old seen bit pref word x = true := by
  constructor
  · rintro ⟨c, hSize, hAgrees, hPrefix⟩
    refine ⟨encodeMergeWitness cap c, length_encodeMergeWitness cap c hSize, fun x ↦ ?_⟩
    have hRow := (mergeAgrees_iff_forall_mergeViolationCircuit_eq_false old seen bit c).mp hAgrees x
    simp [checkMergePrefixRow, decodeMergeWitness_encodeMergeWitness cap c hSize,
      (List.prefix_iff_eq_take.mp hPrefix).symm, hSize, hRow]
  · rintro ⟨word, _, hRows⟩
    cases hCode : decodeMergeWitness n cap word with
    | none =>
      have hRow := hRows (fun _ ↦ false)
      simp [checkMergePrefixRow, hCode] at hRow
    | some c =>
      have hChecks (x : Fin n → Bool) := hRows x
      simp only [checkMergePrefixRow, hCode, Bool.and_eq_true, decide_eq_true_eq,
        Bool.not_eq_true'] at hChecks
      obtain ⟨hSize, hWord, hPrefix⟩ := (hChecks fun _ ↦ false).1
      refine ⟨c, hSize, (mergeAgrees_iff_forall_mergeViolationCircuit_eq_false old seen bit c).mpr
        (fun x ↦ (hChecks x).2), ?_⟩
      exact hWord ▸ List.prefix_iff_eq_take.mpr hPrefix.symm

theorem searchStream_prefixOracle_isSome_iff {n cap : Nat} {oracle : MergePrefixOracle n}
    (correct : CorrectMergePrefixOracle oracle cap) (bits : BinaryWord) :
    (searchStream n (mergeByPrefixSearch cap oracle) bits).isSome = true ↔
      SizeBounded n cap bits :=
  searchStream_isSome_iff (mergeByPrefixSearch_correct correct) bits

end PvsNP.MCSP
