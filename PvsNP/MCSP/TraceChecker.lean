module

public import PvsNP.MCSP.TraceViolationLanguage

import Init.Data.List.TakeDrop

/-! # Executable checking of packed merge trace certificates -/

public section

namespace PvsNP.MCSP

open Circuits

private structure DecodedTraceQuery where
  request : MergeRequest
  code : BinaryWord
  candidate : BooleanCircuit request.arity

private def decodeTraceQuery (query : BinaryWord) : Option DecodedTraceQuery := do
  let (r, code) ← decodeMergePrefixQuery query
  let c ← decodeMergeWitness r.arity r.cap code
  if c.size ≤ r.cap ∧ code = encodeMergeWitness r.cap c ∧ code.take r.pref.length = r.pref then
    some ⟨r, code, c⟩
  else none

private theorem decodeTraceQuery_eq_some_iff {query code : BinaryWord} {r : MergeRequest}
    {c : BooleanCircuit r.arity} : decodeTraceQuery query = some ⟨r, code, c⟩ ↔
      ValidMergePrefixTraceQuery query r code c := by
  constructor
  · intro h
    obtain ⟨⟨request, raw⟩, hPacked, hRest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨candidate, hDecoded, hRest⟩ := Option.bind_eq_some_iff.mp hRest
    split at hRest
    next hChecks =>
      have hSame := Option.some.inj hRest
      cases hSame
      exact ⟨decodeMergePrefixQuery_eq_some_iff.mp hPacked, hDecoded,
        hChecks.1, hChecks.2.1, hChecks.2.2⟩
    next => contradiction
  · intro h
    have hChecks : c.size ≤ r.cap ∧ code = encodeMergeWitness r.cap c ∧
        code.take r.pref.length = r.pref := ⟨h.size_le, h.code_eq, h.prefix_eq⟩
    simp only [decodeTraceQuery, Option.bind_eq_bind,
      decodeMergePrefixQuery_eq_some_iff.mpr h.packed, Option.bind_some, h.decoded,
      ite_eq_left hChecks]

private def rowFromLittleEndian {n : Nat} (bits : BinaryWord) (i : Fin n) : Bool :=
  (bits.reverse[i.val]?).getD false

private theorem rowFromLittleEndian_ofFn {n : Nat} (x : Fin n → Bool) :
    rowFromLittleEndian (List.ofFn x).reverse = x := by
  funext i
  simp [rowFromLittleEndian, i.isLt]

private def checkTraceFields (r : MergeRequest) (c : BooleanCircuit r.arity)
    (cert : BinaryWord) : Bool :=
  let row := rowFromLittleEndian (cert.take r.arity)
  let body := cert.drop (r.arity + 1)
  let oldWidth := r.arity + r.old.size
  let newWidth := r.arity + c.size
  let oldTrace := body.take oldWidth
  let newTrace := (body.drop oldWidth).take newWidth
  match (body.drop oldWidth).drop newWidth with
  | [oldValue, newValue] =>
    decide (cert = encodeMergeTraceCertificate row oldTrace newTrace oldValue newValue) &&
      checkMergeTraceViolation r.old r.seen r.bit c row oldTrace newTrace oldValue newValue
  | _ => false

private theorem mergeTraceLengths (r : MergeRequest) (c : BooleanCircuit r.arity)
    (x : Fin r.arity → Bool) (oldTrace newTrace : BinaryWord) (oldValue newValue : Bool)
    (h : checkMergeTraceViolation r.old r.seen r.bit c x oldTrace newTrace oldValue newValue =
      true) : oldTrace.length = r.arity + r.old.size ∧ newTrace.length = r.arity + c.size := by
  simp only [checkMergeTraceViolation, Bool.and_eq_true] at h
  obtain hOld := (r.old.checkWireTrace_eq_true_iff x oldTrace oldValue).mp h.1.1
  obtain hNew := (c.checkWireTrace_eq_true_iff x newTrace newValue).mp h.1.2
  rw [hOld.1, hNew.1, BooleanCircuit.length_wireTrace, BooleanCircuit.length_wireTrace]
  exact ⟨rfl, rfl⟩

private theorem checkTraceFields_eq_true_iff (r : MergeRequest) (c : BooleanCircuit r.arity)
    (cert : BinaryWord) : checkTraceFields r c cert = true ↔
      ∃ (x : Fin r.arity → Bool) (oldTrace newTrace : BinaryWord) (oldValue newValue : Bool),
        cert = encodeMergeTraceCertificate x oldTrace newTrace oldValue newValue ∧
        oldTrace.length + newTrace.length = 2 * r.arity + r.old.size + c.size ∧
        checkMergeTraceViolation r.old r.seen r.bit c x oldTrace newTrace oldValue newValue =
          true := by
  constructor
  · intro h
    simp only [checkTraceFields] at h
    split at h
    next oldValue newValue _ =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      have ⟨hOldLength, hNewLength⟩ := mergeTraceLengths r c _ _ _ oldValue newValue h.2
      exact ⟨_, _, _, oldValue, newValue, h.1, by omega, h.2⟩
    next => contradiction
  · rintro ⟨x, oldTrace, newTrace, oldValue, newValue, rfl, _, hCheck⟩
    have ⟨hOld, hNew⟩ := mergeTraceLengths r c x oldTrace newTrace oldValue newValue hCheck
    have hBits : (List.ofFn x).reverse.length = r.arity := by simp
    have hRow : (encodeMergeTraceCertificate x oldTrace newTrace oldValue newValue).take r.arity =
        (List.ofFn x).reverse := by
      simp only [encodeMergeTraceCertificate, mergeRowField, List.append_assoc,
        List.take_left' hBits]
    have hBody : (encodeMergeTraceCertificate x oldTrace newTrace oldValue newValue).drop
        (r.arity + 1) = oldTrace ++ (newTrace ++ [oldValue, newValue]) := by
      simp only [encodeMergeTraceCertificate, List.append_assoc,
        List.drop_left' (length_mergeRowField x)]
    simp only [checkTraceFields, hRow, hBody, rowFromLittleEndian_ofFn, List.take_left' hOld,
      List.drop_left' hOld, List.take_left' hNew, List.drop_left' hNew, decide_true, hCheck,
      Bool.and_self]

/-- Malformed queries need an empty certificate. Otherwise, check that the
row, both wire traces, and the claimed output bits constitute a violation. -/
def checkMergePrefixTraceViolation (query cert : BinaryWord) : Bool :=
  match decodeTraceQuery query with
  | none => cert.isEmpty
  | some fields => checkTraceFields fields.request fields.candidate cert

theorem checkMergePrefixTraceViolation_eq_true_iff (query cert : BinaryWord) :
    checkMergePrefixTraceViolation query cert = true ↔ MergePrefixTraceViolation query cert := by
  cases hTrace : decodeTraceQuery query with
  | none =>
    have hInvalid : ¬ ∃ r code c, ValidMergePrefixTraceQuery query r code c := by
      rintro ⟨r, code, c, hValid⟩
      rw [decodeTraceQuery_eq_some_iff.mpr hValid] at hTrace
      contradiction
    simp only [checkMergePrefixTraceViolation, hTrace, List.isEmpty_iff]
    constructor
    · exact fun hEmpty ↦ Or.inl ⟨hEmpty, hInvalid⟩
    · rintro (⟨hEmpty, _⟩ | ⟨r, code, c, _, _, _, _, _, hValid, _, _, _⟩)
      · exact hEmpty
      · exact (hInvalid ⟨r, code, c, hValid⟩).elim
  | some fields =>
    obtain ⟨r, code, c⟩ := fields
    have hValid := decodeTraceQuery_eq_some_iff.mp hTrace
    simp only [checkMergePrefixTraceViolation, hTrace, checkTraceFields_eq_true_iff]
    constructor
    · rintro ⟨x, u, v, a, b, hCert, hLength, hCheck⟩
      exact Or.inr ⟨r, code, c, x, u, v, a, b, hValid, hCert, hLength, hCheck⟩
    · rintro (⟨_, hInvalid⟩ | ⟨s, raw, d, x, u, v, a, b, hOther, hCert, hLength, hCheck⟩)
      · exact (hInvalid ⟨r, code, c, hValid⟩).elim
      · have hSame := Option.some.inj (hTrace.symm.trans (decodeTraceQuery_eq_some_iff.mpr hOther))
        cases hSame
        exact ⟨x, u, v, a, b, hCert, hLength, hCheck⟩

/-- Check one binary word consisting of an exactly packed query and certificate. -/
def checkPackedMergePrefixTraceViolation (word : BinaryWord) : Bool :=
  match decodePackedPair word with
  | none => false
  | some (query, cert) => checkMergePrefixTraceViolation query cert

theorem checkPackedMergePrefixTraceViolation_eq_true_iff (word : BinaryWord) :
    checkPackedMergePrefixTraceViolation word = true ↔
      word ∈ packedCheckingLanguage MergePrefixTraceViolation := by
  cases hPair : decodePackedPair word with
  | none =>
    simp only [checkPackedMergePrefixTraceViolation, hPair, Bool.false_eq_true, false_iff]
    rintro ⟨query, cert, hPacked, _⟩
    rw [decodePackedPair_eq_some_iff.mpr hPacked] at hPair
    contradiction
  | some parts =>
    obtain ⟨query, cert⟩ := parts
    have hLanguage : word ∈ packedCheckingLanguage MergePrefixTraceViolation ↔
        MergePrefixTraceViolation query cert := by
      rw [decodePackedPair_eq_some_iff.mp hPair, packedPair_mem_packedCheckingLanguage_iff]
    rw [hLanguage, checkPackedMergePrefixTraceViolation, hPair,
      checkMergePrefixTraceViolation_eq_true_iff]

end PvsNP.MCSP
