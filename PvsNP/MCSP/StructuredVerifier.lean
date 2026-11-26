module

public import PvsNP.MCSP.QueryStructureDispatch
public import PvsNP.MCSP.QueryStructureFront
public import PvsNP.MCSP.VerifierProgram

/-! # Run the structural verifier from blank registers -/

public section

namespace PvsNP.MCSP

open RegisterMachine RegisterMachine.Fragment

variable {R : Type}

/-- The front end now runs through the last query check before calling the trace checker. -/
def traceStructuredVerifier (headers : TraceHeaderLane → R) (extents : TraceExtentLane → R)
    (fresh : QueryStructureFreshLane → R) (continuation : Fragment R) : Fragment R :=
  traceFrontRegister headers extents
    (queryStructureDispatch (queryStructureRegistersFromFront headers extents fresh)
      headers continuation)

variable [DecidableEq R]

/-- The trace checker starts with the actual front-end results and a valid decoded query. -/
@[expose] def TraceStructuredContinuation (headers : TraceHeaderLane → R)
    (extents : TraceExtentLane → R) (fresh : QueryStructureFreshLane → R)
    (continuation : Fragment R) (word : BinaryWord) (initial : R → Nat)
    (suffix : BinaryWord) (bound : Nat) : Prop :=
  ∀ request candidate cert, word = packedPair (packedPair request candidate) cert →
    ∀ measured, TraceHeaderRegisterResult headers word initial measured →
    ∀ shaped, TraceExtentRegisterResult extents measured shaped →
    ∀ fields, readMergeRequestFields request = some fields →
      QueryStructureContinuation (queryStructureRegistersFromFront headers extents fresh)
        continuation request candidate cert fields shaped suffix bound

private theorem structuredHeaderLanes_disjoint (lane : TraceHeaderLane)
    (h : lane ∈ extentDispatchHeaderLanes) (other : TraceHeaderLane)
    (hOther : other ∈ queryStructureFrontHeaderLanes) : lane ≠ other := by
  simp only [extentDispatchHeaderLanes, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [queryStructureFrontHeaderLanes, List.mem_cons, List.not_mem_nil, or_false] at hOther
  rcases h with rfl | rfl | rfl | rfl | rfl <;> rcases hOther with rfl | rfl | rfl <;> simp

/-- Choose one polynomial clock before fixing the input. All raw malformed inputs
are handled by the program. The callback is used only for a valid decoded query. -/
theorem exists_traceStructuredVerifierClock (headers : TraceHeaderLane → R)
    (extents : TraceExtentLane → R) (fresh : QueryStructureFreshLane → R)
    (hWiring : QueryStructureFrontWiring headers extents fresh)
    (hLink : TraceExtentLink headers extents)
    (hSeparate : ∀ lane ∈ extentDispatchHeaderLanes, ∀ k, headers lane ≠ extents k)
    (hNewExtents : ∀ lane, lane ∉ traceExtentInputLanes → ∀ k, extents lane ≠ headers k)
    (continuation : Fragment R) {bound : Nat → Nat} (hBound : PolynomiallyBounded bound) :
    ∃ clock : Nat → Nat, PolynomiallyBounded clock ∧
      ∀ word initial suffix, (∀ r, initial r = 0) →
        TraceStructuredContinuation headers extents fresh continuation word initial suffix
          (bound word.length) →
        ∃ ticks ≤ clock word.length, ∃ after,
          (traceStructuredVerifier headers extents fresh continuation).RunsOutput
            word ticks initial after suffix
              (checkPackedMergePrefixTraceViolation word :: suffix) := by
  obtain ⟨structureClock, hClock, hTime⟩ := exists_queryStructureRegisterClock
  let tailClock := fun n ↦ structureClock n + (bound n + 6 * n + 15)
  have hTail : PolynomiallyBounded tailClock := hClock.add
    ((hBound.add ((PolynomiallyBounded.const 6).mul PolynomiallyBounded.id)).add
      (PolynomiallyBounded.const 15))
  refine ⟨fun n ↦ traceFrontRegisterCost n (tailClock n),
    traceFrontRegisterCost_polynomiallyBounded hTail, ?_⟩
  intro word initial suffix hZero hNext
  let regs := queryStructureRegistersFromFront headers extents fresh
  have hStructureSeparate (lane : TraceHeaderLane) (h : lane ∈ extentDispatchHeaderLanes) :
      (∀ k, headers lane ≠ regs.bases k) ∧ (∀ k, headers lane ≠ regs.counterPrefix k) ∧
        (∀ k, headers lane ≠ regs.descriptions k) :=
    queryStructureRegistersFromFront_separate headers extents fresh (headers lane)
      (fun k hk he ↦ structuredHeaderLanes_disjoint lane h k hk (hWiring.headersInjective he))
      (hSeparate lane h) (fun k he ↦ hWiring.freshHeaders k lane he.symm)
  apply runsOutput_traceFrontRegister headers extents hWiring.headersInjective
    hWiring.extentsInjective hLink hSeparate hNewExtents
    (queryStructureDispatch regs headers continuation) word initial
    hZero suffix (tailClock word.length)
  intro measured hHeader query cert request candidate hOuter hInner _ _ shaped hExtent
    fields hFields hLength
  have hReady := queryStructureReady_fromFront hWiring hLink hHeader hExtent hOuter hInner
    hFields (fun _ ↦ hZero _)
  have hCert := (hHeader.outerLengths query cert hOuter).2
  have keep (lane : TraceHeaderLane) (h : lane ∈ extentDispatchHeaderLanes) :
      shaped (headers lane) = measured (headers lane) :=
    hExtent.external _ (hSeparate lane h)
  have hQuery := decodePackedPair_eq_some_iff.mp hInner
  have hWord := (decodePackedPair_eq_some_iff.mp hOuter).trans
    (congrArg (fun q ↦ packedPair q cert) hQuery)
  have hContinue := hNext request candidate cert hWord measured hHeader shaped hExtent
    fields hFields
  subst word
  obtain ⟨ticks, hTicks, after, hRun⟩ :=
    runsOutput_queryStructureDispatch regs (queryStructureWiring_fromFront hWiring)
      headers hWiring.headersInjective hStructureSeparate continuation hFields hLength shaped hReady
      ((keep _ (by simp [extentDispatchHeaderLanes])).trans hCert)
      ((keep _ (by simp [extentDispatchHeaderLanes])).trans hHeader.branchZero)
      ⟨(keep _ (by simp [extentDispatchHeaderLanes])).trans hHeader.branchScratch.1,
        (keep _ (by simp [extentDispatchHeaderLanes])).trans hHeader.branchScratch.2.1,
        (keep _ (by simp [extentDispatchHeaderLanes])).trans hHeader.branchScratch.2.2⟩
      suffix _ hContinue
  exact ⟨ticks, hTicks.trans (Nat.add_le_add_right
    (hTime _ _ (queryStructureMeasures_le_length hFields hLength)) _), after, hRun⟩

/-- To obtain the merge-prefix oracle under Cook's collapse, it now suffices to
implement the certificate continuation on structurally valid queries. -/
theorem mergePrefixLanguage_mem_P_of_traceStructuredContinuation [Finite R]
    (headers : TraceHeaderLane → R) (extents : TraceExtentLane → R)
    (fresh : QueryStructureFreshLane → R)
    (hWiring : QueryStructureFrontWiring headers extents fresh)
    (hLink : TraceExtentLink headers extents)
    (hSeparate : ∀ lane ∈ extentDispatchHeaderLanes, ∀ k, headers lane ≠ extents k)
    (hNewExtents : ∀ lane, lane ∉ traceExtentInputLanes → ∀ k, extents lane ≠ headers k)
    (continuation : Fragment R) {bound : Nat → Nat} (hBound : PolynomiallyBounded bound)
    (hNext : ∀ word, TraceStructuredContinuation headers extents fresh continuation word
      (fun _ ↦ 0) [] (bound word.length)) (hCollapse : P = NP) : MergePrefixLanguage ∈ P := by
  obtain ⟨clock, hClock, hRun⟩ :=
    exists_traceStructuredVerifierClock headers extents fresh hWiring hLink hSeparate hNewExtents
      continuation hBound
  let program := traceStructuredVerifier headers extents fresh continuation
  refine mergePrefixLanguage_mem_P_of_trace_checker_run program.entry program.close
    (hClock.add (PolynomiallyBounded.const 1)) ?_ hCollapse
  intro word
  obtain ⟨ticks, hTicks, _, hOutput⟩ := hRun word (fun _ ↦ 0) [] (fun _ ↦ rfl) (hNext word)
  exact ⟨ticks + 1, Nat.add_le_add_right hTicks 1, _, Fragment.run_close hOutput rfl rfl, rfl, rfl⟩

end PvsNP.MCSP
