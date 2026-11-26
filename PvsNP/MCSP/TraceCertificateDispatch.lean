module

public import PvsNP.MCSP.TraceCertificateRegister
public import PvsNP.TuringMachine.Registers.PositiveBranch

import PvsNP.CookLevin.Generator.AcceptingBlock

/-! # Reject malformed certificates before checking their contents -/

public section

namespace PvsNP.MCSP

open Circuits RegisterMachine RegisterMachine.Fragment

variable {R : Type}

/-- The header, description scans, and framing supply these five fields. -/
structure TraceCertificateDispatchReady (lanes : TraceCertificateLane → R)
    (query cert : BinaryWord) (arity oldCount newCount : Nat) (before : R → Nat) : Prop where
  inputLength : before (lanes .inputLength) = (packedPair query cert).length
  arityValue : before (lanes .arity) = arity
  oldCountValue : before (lanes .oldCount) = oldCount
  newCountValue : before (lanes .newCount) = newCount
  certificateLength : before (lanes .certificateLength) = cert.length
  zero : ∀ lane, lane ∉ [.inputLength, .arity, .oldCount, .newCount, .certificateLength] →
    before (lanes lane) = 0

/-- Check the certificate's framing before reading either circuit trace. -/
def traceCertificateDispatch (lanes : TraceCertificateLane → R) (continuation : Fragment R) :
    Fragment R :=
  (traceCertificateRegister lanes).seq
    (ifRegisterPositive (lanes .failure) (emitBit false) continuation)

/-- An instruction bound for the guarded dispatch and its continuation. -/
@[expose] def traceCertificateDispatchCost (length bound : Nat) : Nat :=
  500 * length + 103 + bound

theorem traceCertificateDispatchCost_polynomiallyBounded {length bound : Nat → Nat}
    (hLength : PolynomiallyBounded length) (hBound : PolynomiallyBounded bound) :
    PolynomiallyBounded (fun n ↦ traceCertificateDispatchCost (length n) (bound n)) :=
  (((PolynomiallyBounded.const 500).mul hLength).add (PolynomiallyBounded.const 103)).add hBound

/-- On a valid query, an incorrectly framed certificate always rejects. -/
theorem checkPackedMergePrefixTraceViolation_of_invalid_certificate
    {query code : BinaryWord} {r : MergeRequest} {candidate : BooleanCircuit r.arity}
    (hValid : ValidMergePrefixTraceQuery query r code candidate) (cert : BinaryWord)
    (hInvalid : ¬ MergeTraceCertificateLayout r.arity r.old.size candidate.size cert) :
    checkPackedMergePrefixTraceViolation (packedPair query cert) = false := by
  apply Bool.eq_false_iff.mpr
  intro hCheck
  have hChecks := (checkPackedMergePrefixTraceViolation_eq_true_iff_certificateChecks
    hValid cert).mp hCheck
  exact hInvalid hChecks.layout

private theorem certificateDispatch_inputs_le {query code : BinaryWord} {r : MergeRequest}
    {candidate : BooleanCircuit r.arity}
    (hValid : ValidMergePrefixTraceQuery query r code candidate)
    (cert : BinaryWord) :
    let length := (packedPair query cert).length
    r.arity ≤ length ∧ r.old.size ≤ length ∧ candidate.size ≤ length ∧ cert.length ≤ length := by
  have hQuery : query = packedPair (encodeMergeRequest r) code := hValid.packed.1
  have hHeader := arity_add_cap_le_length_encodeMergeRequest r
  have hOld := r.old_size_le
  have hCap : max 1 r.cap ≤ r.cap + 1 := Nat.max_le.mpr ⟨by omega, by omega⟩
  have hCandidate := hValid.size_le
  rw [hQuery, length_packedPair, length_packedPair]
  exact ⟨by omega, by omega, by omega, by omega⟩

variable [DecidableEq R]

/-- The successful continuation receives the original register values and the
verified layout. The failed branch emits false within a raw-length linear bound. -/
theorem runsOutput_traceCertificateDispatch (lanes : TraceCertificateLane → R)
    (hLanes : Function.Injective lanes) (continuation : Fragment R) {query code : BinaryWord}
    {r : MergeRequest} {candidate : BooleanCircuit r.arity}
    (hValid : ValidMergePrefixTraceQuery query r code candidate) (cert : BinaryWord)
    (before : R → Nat)
    (hReady : TraceCertificateDispatchReady lanes query cert r.arity r.old.size candidate.size
      before) (suffix : BinaryWord) (bound : Nat)
    (hNext : MergeTraceCertificateLayout r.arity r.old.size candidate.size cert →
      ∃ ticks ≤ bound, ∃ after,
        continuation.RunsOutput (packedPair query cert) ticks before after suffix
          (checkPackedMergePrefixTraceViolation (packedPair query cert) :: suffix)) :
    let word := packedPair query cert
    ∃ ticks ≤ traceCertificateDispatchCost word.length bound, ∃ after,
      (traceCertificateDispatch lanes continuation).RunsOutput word ticks before after suffix
        (checkPackedMergePrefixTraceViolation word :: suffix) := by
  let word := packedPair query cert
  let failureLane := lanes .failure
  obtain ⟨scanTicks, hScanTime, failure, hScan, hLayout⟩ :=
    runsValues_traceCertificateRegister lanes hLanes query cert before hReady.inputLength
      hReady.certificateLength hReady.zero
  rw [hReady.inputLength, hReady.arityValue, hReady.oldCountValue, hReady.newCountValue]
    at hScanTime
  rw [hReady.arityValue, hReady.oldCountValue, hReady.newCountValue] at hLayout
  let measured := setValue failureLane failure before
  have hFailure : measured failureLane = failure := setValue_same ..
  have hInitial : before failureLane = 0 := hReady.zero .failure (by simp)
  have hSelected : ∃ ticks ≤ bound + 1, ∃ after,
      (if 0 < measured failureLane then emitBit false else continuation).RunsOutput
        word ticks measured after suffix (checkPackedMergePrefixTraceViolation word :: suffix) := by
    by_cases h : failure = 0
    · obtain ⟨ticks, hTicks, after, hRun⟩ := hNext (hLayout.mp h)
      have hSame : measured = before := by
        change setValue failureLane failure before = before
        rw [h, ← hInitial]
        exact setValue_current failureLane before
      refine ⟨ticks, by omega, after, ?_⟩
      simpa only [hSame, hInitial, Nat.lt_irrefl, ite_false] using hRun
    · have hPositive : 0 < measured failureLane := hFailure.symm ▸ Nat.pos_of_ne_zero h
      have hInvalid : ¬ MergeTraceCertificateLayout r.arity r.old.size candidate.size cert :=
        fun layout ↦ h (hLayout.mpr layout)
      have hCheck : checkPackedMergePrefixTraceViolation word = false :=
        checkPackedMergePrefixTraceViolation_of_invalid_certificate hValid cert hInvalid
      refine ⟨1, by omega, measured, ?_⟩
      rw [ite_eq_left hPositive, hCheck]
      exact run_emitBit false word (⟨none, measured, none, suffix⟩ : Config R Unit) rfl
  obtain ⟨branchTicks, hBranchTime, after, hBranch⟩ := hSelected
  have hTestTime := ifRegisterPositiveTime_le (measured failureLane)
  have hRun := (hScan.withOutput suffix).seq
    (runsOutput_ifRegisterPositive failureLane (emitBit false) continuation word measured hBranch)
  refine ⟨scanTicks + (ifRegisterPositiveTime (measured failureLane) + branchTicks),
    ?_, after, hRun⟩
  obtain ⟨hArity, hOld, hNew, hCert⟩ := certificateDispatch_inputs_le hValid cert
  change scanTicks + (ifRegisterPositiveTime (measured failureLane) + branchTicks) ≤
    traceCertificateDispatchCost word.length bound
  change scanTicks ≤ traceCertificateRegisterCost word.length r.arity r.old.size
    candidate.size cert.length at hScanTime
  change r.arity ≤ word.length at hArity
  change r.old.size ≤ word.length at hOld
  change candidate.size ≤ word.length at hNew
  change cert.length ≤ word.length at hCert
  unfold traceCertificateDispatchCost
  unfold traceCertificateRegisterCost at hScanTime
  omega

end PvsNP.MCSP
