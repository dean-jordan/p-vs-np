module

public import PvsNP.MCSP.PrefixViolationLanguage
public import PvsNP.MCSP.TraceViolation

/-! # Merge prefix violations with certified circuit wire values -/

public section

namespace PvsNP.MCSP

open Circuits

/-- The query contains a canonical candidate whose description extends the requested prefix. -/
structure ValidMergePrefixTraceQuery (query : BinaryWord) (r : MergeRequest)
    (code : BinaryWord) (candidate : BooleanCircuit r.arity) : Prop where
  packed : PackedMergePrefixQuery query r code
  decoded : decodeMergeWitness r.arity r.cap code = some candidate
  size_le : candidate.size ≤ r.cap
  code_eq : code = encodeMergeWitness r.cap candidate
  prefix_eq : code.take r.pref.length = r.pref

/-- The row fields come first, followed by both complete wire traces and their answers. -/
@[expose] def encodeMergeTraceCertificate {n : Nat} (x : Fin n → Bool)
    (oldTrace newTrace : BinaryWord) (oldValue newValue : Bool) : BinaryWord :=
  mergeRowField x ++ oldTrace ++ newTrace ++ [oldValue, newValue]

/-- Invalid framing, candidate encoding, or prefix has the empty certificate.
A valid query needs a row and the two certified evaluations to exhibit a violation. -/
@[expose] def MergePrefixTraceViolation (query cert : BinaryWord) : Prop :=
  (cert = [] ∧ ¬ ∃ r code c, ValidMergePrefixTraceQuery query r code c) ∨
    ∃ (r : MergeRequest) (code : BinaryWord) (c : BooleanCircuit r.arity)
      (x : Fin r.arity → Bool) (oldTrace newTrace : BinaryWord) (oldValue newValue : Bool),
      ValidMergePrefixTraceQuery query r code c ∧
      cert = encodeMergeTraceCertificate x oldTrace newTrace oldValue newValue ∧
      oldTrace.length + newTrace.length = 2 * r.arity + r.old.size + c.size ∧
      checkMergeTraceViolation r.old r.seen r.bit c x oldTrace newTrace oldValue newValue = true

private theorem checkMergePrefixRow_of_validTraceQuery {query code : BinaryWord} {r : MergeRequest}
    {c : BooleanCircuit r.arity} (h : ValidMergePrefixTraceQuery query r code c)
    (x : Fin r.arity → Bool) :
    checkMergePrefixRow r.cap r.old r.seen r.bit r.pref code x =
      !(mergeViolationCircuit r.old r.seen r.bit c).eval x := by
  have hChecks : decide (c.size ≤ r.cap ∧ code = encodeMergeWitness r.cap c ∧
      code.take r.pref.length = r.pref) = true := decide_eq_true ⟨h.size_le, h.code_eq, h.prefix_eq⟩
  simp only [checkMergePrefixRow, h.decoded, hChecks, Bool.true_and]

private theorem checkMergePrefixRow_of_invalidTraceQuery {query code : BinaryWord}
    {r : MergeRequest} (hPacked : PackedMergePrefixQuery query r code)
    (hInvalid : ¬ ∃ c, ValidMergePrefixTraceQuery query r code c) (x : Fin r.arity → Bool) :
    checkMergePrefixRow r.cap r.old r.seen r.bit r.pref code x = false := by
  cases hDecoded : decodeMergeWitness r.arity r.cap code with
  | none => simp [checkMergePrefixRow, hDecoded]
  | some c =>
    have hChecks : ¬ (c.size ≤ r.cap ∧ code = encodeMergeWitness r.cap c ∧
        code.take r.pref.length = r.pref) := by
      rintro ⟨hSize, hCode, hPrefix⟩
      exact hInvalid ⟨c, hPacked, hDecoded, hSize, hCode, hPrefix⟩
    simp only [checkMergePrefixRow, hDecoded, decide_eq_false hChecks, Bool.false_and]

theorem mergePrefixTraceViolation_cert_length_le {query cert : BinaryWord}
    (h : MergePrefixTraceViolation query cert) : cert.length ≤ query.length := by
  rcases h with ⟨rfl, _⟩ | ⟨r, code, c, x, oldTrace, newTrace, oldValue, newValue,
    hValid, rfl, hTraceLength, _⟩
  · exact Nat.zero_le _
  · have hOld : r.old.size ≤ r.cap + 1 :=
      r.old_size_le.trans (Nat.max_le.mpr ⟨by omega, Nat.le_succ _⟩)
    have hNew := hValid.size_le
    rw [hValid.packed.1, length_packedPair, length_encodeMergeRequest]
    simp only [encodeMergeTraceCertificate, List.length_append, length_mergeRowField,
      List.length_cons, List.length_nil]
    omega

theorem mem_mergePrefixViolationLanguage_iff_exists_trace (query : BinaryWord) :
    query ∈ MergePrefixViolationLanguage ↔ ∃ cert, MergePrefixTraceViolation query cert := by
  constructor
  · intro hBad
    classical
    by_contra hNoCertificate
    obtain ⟨r, code, c, hValid⟩ : ∃ r code c, ValidMergePrefixTraceQuery query r code c := by
      by_contra hInvalid
      exact hNoCertificate ⟨[], Or.inl ⟨rfl, hInvalid⟩⟩
    refine (not_mem_mergePrefixViolationLanguage_iff query).mpr ⟨r, code, hValid.packed, ?_⟩ hBad
    intro x
    rw [checkMergePrefixRow_of_validTraceQuery hValid]
    cases hEval : (mergeViolationCircuit r.old r.seen r.bit c).eval x with
    | false => rfl
    | true =>
      obtain ⟨oldTrace, newTrace, oldValue, newValue, hLength, hCheck⟩ :=
        (exists_checkMergeTraceViolation_iff r.old r.seen r.bit c x).mpr hEval
      exact (hNoCertificate ⟨_, Or.inr ⟨r, code, c, x, oldTrace, newTrace, oldValue, newValue,
        hValid, rfl, hLength, hCheck⟩⟩).elim
  · rintro ⟨_, ⟨_, hInvalid⟩ | ⟨r, code, c, x, oldTrace, newTrace, oldValue, newValue,
      hValid, _, hLength, hCheck⟩⟩
    · classical
      by_cases hFramed : ∃ r code, PackedMergePrefixQuery query r code
      · obtain ⟨r, code, hPacked⟩ := hFramed
        let x : Fin r.arity → Bool := fun _ ↦ false
        have hInvalidCode : ¬ ∃ c, ValidMergePrefixTraceQuery query r code c := by
          rintro ⟨c, hC⟩
          exact hInvalid ⟨r, code, c, hC⟩
        exact ⟨List.ofFn x, Or.inr ⟨r, code, x, hPacked, rfl,
          checkMergePrefixRow_of_invalidTraceQuery hPacked hInvalidCode x⟩⟩
      · exact ⟨[], Or.inl ⟨rfl, hFramed⟩⟩
    · have hEval := (exists_checkMergeTraceViolation_iff r.old r.seen r.bit c x).mp
        ⟨oldTrace, newTrace, oldValue, newValue, hLength, hCheck⟩
      exact ⟨List.ofFn x, Or.inr ⟨r, code, x, hValid.packed, rfl, by
        simp only [checkMergePrefixRow_of_validTraceQuery hValid, hEval, Bool.not_true]⟩⟩

theorem mem_mergePrefixViolationLanguage_iff_bounded_trace (query : BinaryWord) :
    query ∈ MergePrefixViolationLanguage ↔
      ∃ cert, cert.length ≤ query.length ∧ MergePrefixTraceViolation query cert := by
  rw [mem_mergePrefixViolationLanguage_iff_exists_trace]
  exact ⟨fun ⟨cert, h⟩ ↦ ⟨cert, mergePrefixTraceViolation_cert_length_le h, h⟩,
    fun ⟨cert, _, h⟩ ↦ ⟨cert, h⟩⟩

/-- A Cook checker for the trace certificate suffices for the inner violation language. -/
theorem mergePrefixViolationLanguage_mem_NP_of_trace_checker
    (hChecker : packedCheckingLanguage MergePrefixTraceViolation ∈ P) :
    MergePrefixViolationLanguage ∈ NP :=
  mem_NP_of_packedCheckingLanguage_mem_P hChecker 1 fun query ↦ by
    simpa only [Nat.pow_one] using mem_mergePrefixViolationLanguage_iff_bounded_trace query

/-- Under the Cook collapse, checking trace certificates suffices to decide merge prefixes. -/
theorem mergePrefixLanguage_mem_P_of_trace_checker (hCollapse : P = NP)
    (hChecker : packedCheckingLanguage MergePrefixTraceViolation ∈ P) :
    MergePrefixLanguage ∈ P := by
  have hBad := mergePrefixViolationLanguage_mem_NP_of_trace_checker hChecker
  rw [← hCollapse] at hBad
  have hOuter : packedCheckingLanguage MergePrefixCandidatePasses ∈ P := by
    rw [packedCheckingLanguage_mergePrefixCandidatePasses_eq]
    exact mem_POver_compl hBad
  rw [hCollapse]
  exact mem_NP_of_packedCheckingLanguage_mem_P hOuter 9 mergePrefixLanguage_iff_exists_nonviolation

end PvsNP.MCSP
