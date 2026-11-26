module

public import PvsNP.MCSP.StructuredVerifier
public import PvsNP.MCSP.TraceCertificateLink

/-! # Compose the raw query verifier with the trace certificate guard -/

public section

namespace PvsNP.MCSP

open RegisterMachine RegisterMachine.Fragment

variable {R : Type}

/-- Check the entire query and then the certificate layout before reading the traces. -/
def traceCertificateVerifier (headers : TraceHeaderLane → R) (extents : TraceExtentLane → R)
    (structureFresh : QueryStructureFreshLane → R) (certificateFresh : TraceCertificateLane → R)
    (continuation : Fragment R) : Fragment R :=
  traceStructuredVerifier headers extents structureFresh
    (traceCertificateDispatch
      (traceCertificateLanesFromFront headers extents structureFresh certificateFresh) continuation)

variable [DecidableEq R]

/-- The remaining trace computation starts only when the query and its certificate
layout are both valid. It can use the data measured by the front end. -/
@[expose] def TraceCertificateVerifierContinuation (headers : TraceHeaderLane → R)
    (extents : TraceExtentLane → R) (structureFresh : QueryStructureFreshLane → R)
    (continuation : Fragment R) (word : BinaryWord) (initial : R → Nat)
    (suffix : BinaryWord) (bound : Nat) : Prop :=
  ∀ request candidate cert, word = packedPair (packedPair request candidate) cert →
    ∀ measured, TraceHeaderRegisterResult headers word initial measured →
    ∀ shaped, TraceExtentRegisterResult extents measured shaped →
    ∀ fields, readMergeRequestFields request = some fields →
    ∀ checked, QueryStructureRegisterResult
        (queryStructureRegistersFromFront headers extents structureFresh)
        request candidate cert fields shaped checked →
    ∀ r code c, ValidMergePrefixTraceQuery (packedPair request candidate) r code c →
    MergeTraceCertificateLayout r.arity r.old.size c.size cert →
      ∃ ticks ≤ bound, ∃ after,
        continuation.RunsOutput word ticks checked after suffix
          (checkPackedMergePrefixTraceViolation word :: suffix)

/-- One polynomial clock covers the raw query and the initial certificate checks. -/
theorem exists_traceCertificateVerifierClock (headers : TraceHeaderLane → R)
    (extents : TraceExtentLane → R) (structureFresh : QueryStructureFreshLane → R)
    (certificateFresh : TraceCertificateLane → R)
    (hStructure : QueryStructureFrontWiring headers extents structureFresh)
    (hCertificate : TraceCertificateFrontWiring headers extents structureFresh certificateFresh)
    (hLink : TraceExtentLink headers extents)
    (hSeparate : ∀ lane ∈ extentDispatchHeaderLanes, ∀ k, headers lane ≠ extents k)
    (hNewExtents : ∀ lane, lane ∉ traceExtentInputLanes → ∀ k, extents lane ≠ headers k)
    (continuation : Fragment R) {bound : Nat → Nat} (hBound : PolynomiallyBounded bound) :
    ∃ clock : Nat → Nat, PolynomiallyBounded clock ∧
      ∀ word initial suffix, (∀ r, initial r = 0) →
        TraceCertificateVerifierContinuation headers extents structureFresh continuation word
          initial suffix (bound word.length) →
        ∃ ticks ≤ clock word.length, ∃ after,
          (traceCertificateVerifier headers extents structureFresh certificateFresh
            continuation).RunsOutput word ticks initial after suffix
              (checkPackedMergePrefixTraceViolation word :: suffix) := by
  let lanes := traceCertificateLanesFromFront headers extents structureFresh certificateFresh
  let guarded := traceCertificateDispatch lanes continuation
  obtain ⟨clock, hClock, hRun⟩ :=
    exists_traceStructuredVerifierClock headers extents structureFresh hStructure hLink
      hSeparate hNewExtents guarded
      (traceCertificateDispatchCost_polynomiallyBounded PolynomiallyBounded.id hBound)
  refine ⟨clock, hClock, fun word initial suffix hZero hNext ↦
    hRun word initial suffix hZero ?_⟩
  intro request candidate cert hWord measured hMeasured shaped hShaped fields hFields
    checked hChecked r code c hValid
  have hOuter : decodePackedPair word = some (packedPair request candidate, cert) :=
    decodePackedPair_eq_some_iff.mpr hWord
  have hReady := traceCertificateDispatchReady_fromFront hStructure hCertificate
    hMeasured hShaped hChecked hOuter hFields hValid (fun _ ↦ hZero _)
  have hContinue := hNext request candidate cert hWord measured hMeasured shaped hShaped
    fields hFields checked hChecked r code c hValid
  subst word
  exact runsOutput_traceCertificateDispatch lanes
    (traceCertificateLanesFromFront_injective hStructure hCertificate) continuation hValid cert
    checked hReady suffix _ hContinue

/-- A polynomial continuation for the well-shaped certificate branch suffices for
the Cook collapse implication. -/
theorem mergePrefixLanguage_mem_P_of_traceCertificateVerifierContinuation [Finite R]
    (headers : TraceHeaderLane → R) (extents : TraceExtentLane → R)
    (structureFresh : QueryStructureFreshLane → R) (certificateFresh : TraceCertificateLane → R)
    (hStructure : QueryStructureFrontWiring headers extents structureFresh)
    (hCertificate : TraceCertificateFrontWiring headers extents structureFresh certificateFresh)
    (hLink : TraceExtentLink headers extents)
    (hSeparate : ∀ lane ∈ extentDispatchHeaderLanes, ∀ k, headers lane ≠ extents k)
    (hNewExtents : ∀ lane, lane ∉ traceExtentInputLanes → ∀ k, extents lane ≠ headers k)
    (continuation : Fragment R) {bound : Nat → Nat} (hBound : PolynomiallyBounded bound)
    (hNext : ∀ word, TraceCertificateVerifierContinuation headers extents structureFresh
      continuation word (fun _ ↦ 0) [] (bound word.length)) (hCollapse : P = NP) :
    MergePrefixLanguage ∈ P := by
  obtain ⟨clock, hClock, hRun⟩ :=
    exists_traceCertificateVerifierClock headers extents structureFresh certificateFresh hStructure
      hCertificate hLink hSeparate hNewExtents continuation hBound
  let program :=
    traceCertificateVerifier headers extents structureFresh certificateFresh continuation
  refine mergePrefixLanguage_mem_P_of_trace_checker_run program.entry program.close
    (hClock.add (PolynomiallyBounded.const 1)) ?_ hCollapse
  intro word
  obtain ⟨ticks, hTicks, _, hOutput⟩ := hRun word (fun _ ↦ 0) [] (fun _ ↦ rfl) (hNext word)
  exact ⟨ticks + 1, Nat.add_le_add_right hTicks 1, _,
    Fragment.run_close hOutput rfl rfl, rfl, rfl⟩

end PvsNP.MCSP
