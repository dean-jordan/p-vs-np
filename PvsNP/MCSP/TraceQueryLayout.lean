module

public import PvsNP.MCSP.RequestLayout
public import PvsNP.MCSP.TraceChecker

/-! # Exact structural validity of a packed trace query -/

public section

namespace PvsNP.MCSP

open Circuits

/-- These checks use only the two query fields. No row or wire trace is supplied. -/
def MergeTraceQueryFieldsValid (request candidate : BinaryWord) : Prop :=
  ∃ fields : MergeRequestFields, readMergeRequestFields request = some fields ∧
    mergeSeenFieldInRange fields.counter = true ∧
    ∃ old new : BooleanCircuit fields.arity,
      old.size ≤ max 1 fields.cap ∧ fields.oldCode = encodeMergeWitness (max 1 fields.cap) old ∧
      new.size ≤ fields.cap ∧ candidate = encodeMergeWitness fields.cap new ∧
      candidate.take fields.pref.length = fields.pref

theorem mergeTraceQueryFieldsValid_iff (request candidate : BinaryWord) :
    MergeTraceQueryFieldsValid request candidate ↔
      ∃ r code c, ValidMergePrefixTraceQuery (packedPair request candidate) r code c := by
  constructor
  · rintro ⟨fields, hFields, hCounter, old, new, hOldSize, hOld, hNewSize, hNew, hPref⟩
    obtain ⟨r, hRequest, hEqual⟩ := readMergeRequestFields_decodes
      hFields hCounter hOldSize hOld
    subst fields
    have hPacked : PackedMergePrefixQuery (packedPair request candidate) r candidate := by
      refine ⟨congrArg (fun word ↦ packedPair word candidate)
        (decodeMergeRequest_eq_some_iff.mp hRequest).symm, ?_⟩
      rw [hNew]
      exact length_encodeMergeWitness _ _ hNewSize
    have hDecoded : decodeMergeWitness r.arity r.cap candidate = some new := by
      rw [hNew]
      exact decodeMergeWitness_encodeMergeWitness _ _ hNewSize
    exact ⟨r, candidate, new, hPacked, hDecoded, hNewSize, hNew, hPref⟩
  · rintro ⟨r, code, c, hValid⟩
    have hPair : (request, candidate) = (encodeMergeRequest r, code) :=
      packedPair_injective hValid.packed.1
    obtain ⟨hRequest, hCandidate⟩ := Prod.mk.inj hPair
    subst request candidate
    have hFields : readMergeRequestFields (encodeMergeRequest r) = some r.fields :=
      decodeMergeRequest_eq_some_iff_readFields.mp (decodeMergeRequest_encodeMergeRequest r)
    have hRange : mergeSeenFieldInRange r.fields.counter = true := by
      apply (mergeSeenFieldInRange_eq_true_iff r.fields_fits.counter).mpr
      change fieldValue (fieldBits (r.arity + 1) r.seen) ≤ 2 ^ r.arity
      have hFit : r.seen < 2 ^ (r.arity + 1) := by
        rw [Nat.pow_succ]
        have hPositive := Nat.two_pow_pos r.arity
        have hSeen := r.seen_le
        omega
      rw [fieldValue_bits _ _ hFit]
      exact r.seen_le
    exact ⟨r.fields, hFields, hRange, r.old, c, r.old_size_le, rfl,
      hValid.size_le, hValid.code_eq, hValid.prefix_eq⟩

/-- Replace reconstructed circuits with the bounded checks on the two raw descriptions. -/
theorem mergeTraceQueryFieldsValid_iff_padded (request candidate : BinaryWord) :
    MergeTraceQueryFieldsValid request candidate ↔
      ∃ fields : MergeRequestFields, readMergeRequestFields request = some fields ∧
        mergeSeenFieldInRange fields.counter = true ∧
        PaddedCircuitDescriptionValid fields.arity (max 1 fields.cap) fields.oldCode ∧
        PaddedCircuitDescriptionValid fields.arity fields.cap candidate ∧
        candidate.take fields.pref.length = fields.pref := by
  constructor
  · rintro ⟨fields, hFields, hCounter, old, new, hOldSize, hOld, hNewSize, hNew, hPref⟩
    exact ⟨fields, hFields, hCounter, paddedCircuitDescriptionValid_iff_canonical.mpr
      ⟨old, hOldSize, hOld⟩, paddedCircuitDescriptionValid_iff_canonical.mpr
      ⟨new, hNewSize, hNew⟩, hPref⟩
  · rintro ⟨fields, hFields, hCounter, hOld, hNew, hPref⟩
    obtain ⟨old, hOldSize, hOldWord⟩ := paddedCircuitDescriptionValid_iff_canonical.mp hOld
    obtain ⟨new, hNewSize, hNewWord⟩ := paddedCircuitDescriptionValid_iff_canonical.mp hNew
    exact ⟨fields, hFields, hCounter, old, new, hOldSize, hOldWord, hNewSize, hNewWord, hPref⟩

/-- For a well-framed pair with no certificate, the structural check alone
determines the trace verifier's answer. -/
theorem checkPackedMergePrefixTraceViolation_empty_iff (request candidate : BinaryWord) :
    checkPackedMergePrefixTraceViolation (packedPair (packedPair request candidate) []) = true ↔
      ¬ MergeTraceQueryFieldsValid request candidate := by
  rw [checkPackedMergePrefixTraceViolation_eq_true_iff,
    packedPair_mem_packedCheckingLanguage_iff, mergeTraceQueryFieldsValid_iff]
  constructor
  · rintro (⟨_, hInvalid⟩ | ⟨_, _, _, row, oldTrace, newTrace, oldValue, newValue, _, hCert, _⟩)
    · exact hInvalid
    · have hLength := congrArg List.length hCert
      simp only [List.length_nil, encodeMergeTraceCertificate, List.length_append,
        length_mergeRowField, List.length_cons] at hLength
      omega
  · exact fun h ↦ Or.inl ⟨rfl, h⟩

end PvsNP.MCSP
