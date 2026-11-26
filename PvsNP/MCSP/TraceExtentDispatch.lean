module

public import PvsNP.MCSP.TraceExtentLink
public import PvsNP.MCSP.TraceHeaderDispatch
public import PvsNP.MCSP.TraceQueryLayout

/-! # Reject malformed extents before reading their fields -/

public section

namespace PvsNP.MCSP

open Circuits RegisterMachine RegisterMachine.Fragment

variable {R : Type}

/-- The length calculation preserves these lanes for the failure branch. -/
@[expose] def extentDispatchHeaderLanes : List TraceHeaderLane :=
  [.zero, .leftCopy, .rightCopy, .scratch, .pair .certificateLength]

def traceExtentDispatch (headers : TraceHeaderLane → R) (extents : TraceExtentLane → R)
    (continuation : Fragment R) : Fragment R :=
  (traceExtentRegister extents).seq
    (ifLess (headers .zero) (extents .failures) (headers .leftCopy) (headers .rightCopy)
      (headers .scratch) (emitEmptyCertificate headers) continuation)

@[expose] def traceExtentDispatchCost (length continuationCost : Nat) : Nat :=
  traceExtentRegisterCost length length length length + (continuationCost + 6 * length + 31)

theorem traceExtentDispatchCost_polynomiallyBounded {bound : Nat → Nat}
    (hBound : PolynomiallyBounded bound) :
    PolynomiallyBounded (fun n ↦ traceExtentDispatchCost n (bound n)) :=
  traceExtentRegisterCost_length_polynomiallyBounded.add
    ((hBound.add ((PolynomiallyBounded.const 6).mul PolynomiallyBounded.id)).add
      (PolynomiallyBounded.const 31))

variable [DecidableEq R]

/-- The remaining checker starts only when the request body splits and the
candidate has the expected length. Its inputs are the measured extent registers. -/
@[expose] def TraceExtentContinuation (continuation : Fragment R)
    (extents : TraceExtentLane → R) (word request candidate : BinaryWord)
    (before : R → Nat) (suffix : BinaryWord) (bound : Nat) : Prop :=
  ∀ after, TraceExtentRegisterResult extents before after →
    ∀ fields, readMergeRequestFields request = some fields →
      candidate.length = mergeWitnessLength fields.arity fields.cap →
    ∃ ticks ≤ bound, ∃ final,
      continuation.RunsOutput word ticks after final suffix
        (checkPackedMergePrefixTraceViolation word :: suffix)

private theorem invalidQuery_of_bad_extents {query request candidate : BinaryWord}
    (hInner : decodePackedPair query = some (request, candidate))
    (hBad : ¬ ((readMergeRequestFields request).isSome ∧
      candidate.length = mergeWitnessLength (requestHeaderProgress request).arity
        (requestHeaderProgress request).cap)) :
    ¬ ∃ r code c, ValidMergePrefixTraceQuery query r code c := by
  rw [decodePackedPair_eq_some_iff.mp hInner, ← mergeTraceQueryFieldsValid_iff,
    mergeTraceQueryFieldsValid_iff_padded]
  rintro ⟨fields, hFields, _, _, hCandidate, _⟩
  obtain ⟨hArity, hCap, _⟩ := readMergeRequestFields_header_progress hFields
  apply hBad
  refine ⟨by simp [hFields], ?_⟩
  rw [hArity, hCap]
  exact hCandidate.length_eq

/-- Handle bad extents with the same certificate rule as a malformed header.
On success, delegate only with a concrete split and the exact candidate length. -/
theorem runsOutput_traceExtentDispatch (headers : TraceHeaderLane → R)
    (extents : TraceExtentLane → R) (hHeadersInj : Function.Injective headers)
    (hExtents : Function.Injective extents) (hLink : TraceExtentLink headers extents)
    (hSeparate : ∀ lane ∈ extentDispatchHeaderLanes, ∀ k, headers lane ≠ extents k)
    (continuation : Fragment R) {word query cert request candidate : BinaryWord}
    {initial before : R → Nat} (hHeaders : TraceHeaderRegisterResult headers word initial before)
    (hOuter : decodePackedPair word = some (query, cert))
    (hInner : decodePackedPair query = some (request, candidate))
    (hArity : (requestHeaderProgress request).arityValid = true)
    (hCap : (requestHeaderProgress request).capValid = true)
    (hZero : ∀ lane, lane ∉ traceExtentInputLanes → before (extents lane) = 0)
    (suffix : BinaryWord) (bound : Nat)
    (hNext : TraceExtentContinuation continuation extents word request candidate
      before suffix bound) :
    ∃ ticks ≤ traceExtentDispatchCost word.length bound, ∃ after,
      (traceExtentDispatch headers extents continuation).RunsOutput word ticks before after suffix
        (checkPackedMergePrefixTraceViolation word :: suffix) := by
  obtain ⟨extentTicks, hExtentTime, measured, hExtentRun, hResult, hValid⟩ :=
    runsValues_traceExtentRegister_of_headers extents hExtents hLink hHeaders hOuter hInner
      hArity hCap hZero
  let output := checkPackedMergePrefixTraceViolation word :: suffix
  let malformed := emitEmptyCertificate headers
  let branchBound := bound + 6 * word.length + 7
  have hKeep (lane : TraceHeaderLane) (h : lane ∈ extentDispatchHeaderLanes) :
      measured (headers lane) = before (headers lane) :=
    hResult.external _ (hSeparate lane h)
  have hReadZero : measured (headers .zero) = 0 :=
    (hKeep .zero (by simp [extentDispatchHeaderLanes])).trans hHeaders.branchZero
  have hReadLeft : measured (headers .leftCopy) = 0 :=
    (hKeep .leftCopy (by simp [extentDispatchHeaderLanes])).trans hHeaders.branchScratch.1
  have hReadRight : measured (headers .rightCopy) = 0 :=
    (hKeep .rightCopy (by simp [extentDispatchHeaderLanes])).trans hHeaders.branchScratch.2.1
  have hReadScratch : measured (headers .scratch) = 0 :=
    (hKeep .scratch (by simp [extentDispatchHeaderLanes])).trans hHeaders.branchScratch.2.2
  have hReadCert : measured (headers (.pair .certificateLength)) = cert.length :=
    (hKeep _ (by simp [extentDispatchHeaderLanes])).trans
      (hHeaders.outerLengths query cert hOuter).2
  have hLeft := List.Nodup.map hHeadersInj
    (show ([.zero, .leftCopy, .rightCopy, .scratch] : List TraceHeaderLane).Nodup by simp)
  have hCopies := List.Nodup.map hHeadersInj
    (show ([.leftCopy, .rightCopy, .scratch] : List TraceHeaderLane).Nodup by simp)
  have hRight : [extents .failures, headers .leftCopy, headers .rightCopy,
      headers .scratch].Nodup := by
    rw [List.nodup_cons]
    refine ⟨?_, hCopies⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨(hSeparate .leftCopy (by simp [extentDispatchHeaderLanes]) _).symm,
      (hSeparate .rightCopy (by simp [extentDispatchHeaderLanes]) _).symm,
      (hSeparate .scratch (by simp [extentDispatchHeaderLanes]) _).symm⟩
  have hBranch : ∃ ticks ≤ branchBound, ∃ after,
      (if measured (headers .zero) < measured (extents .failures) then malformed
        else continuation).RunsOutput word ticks measured after suffix output := by
    rw [hReadZero]
    by_cases hBad : 0 < measured (extents .failures)
    · have hInvalid := invalidQuery_of_bad_extents hInner (fun hGood ↦
        (Nat.ne_of_gt hBad) (hValid.mpr hGood))
      obtain ⟨ticks, hTime, after, hRun⟩ :=
        runsOutput_emitEmptyCertificate_of_count headers hHeadersInj hReadCert hReadZero
          ⟨hReadLeft, hReadRight, hReadScratch⟩ hOuter hInvalid suffix
      exact ⟨ticks, by dsimp [branchBound]; omega, after, by
        simpa only [ite_eq_left hBad] using hRun⟩
    · have hNone : measured (extents .failures) = 0 := by omega
      obtain ⟨hSome, hLength⟩ := hValid.mp hNone
      obtain ⟨fields, hFields⟩ := Option.isSome_iff_exists.mp hSome
      obtain ⟨hn, hc, _⟩ := readMergeRequestFields_header_progress hFields
      rw [hn, hc] at hLength
      obtain ⟨ticks, hTime, after, hRun⟩ := hNext measured hResult fields hFields hLength
      exact ⟨ticks, by dsimp [branchBound]; omega, after, by
        simpa only [ite_eq_right hBad] using hRun⟩
  obtain ⟨branchTicks, hBranchTime, after, hBranchRun⟩ := hBranch
  obtain ⟨testTicks, hTime, hRun⟩ := runsOutput_ifLess word measured after suffix output branchBound
    hLeft hRight hReadLeft hReadRight hReadScratch
    (fun h ↦ ⟨branchTicks, hBranchTime, by simpa only [ite_eq_left h] using hBranchRun⟩)
    (fun h ↦ ⟨branchTicks, hBranchTime, by simpa only [ite_eq_right h] using hBranchRun⟩)
  have hFailLimit := hResult.failureBound
  rw [hReadZero, ifEqualTime] at hTime
  refine ⟨extentTicks + testTicks, ?_, after, (hExtentRun.withOutput suffix).seq hRun⟩
  unfold traceExtentDispatchCost
  dsimp only [branchBound] at hTime
  omega

/-- The front of the trace verifier handles framing, headers, and wire-code lengths. -/
def traceFrontRegister (headers : TraceHeaderLane → R) (extents : TraceExtentLane → R)
    (continuation : Fragment R) : Fragment R :=
  (traceHeaderRegister headers).seq
    (traceHeaderDispatch headers (traceExtentDispatch headers extents continuation))

@[expose] def traceFrontRegisterCost (length continuationCost : Nat) : Nat :=
  traceHeaderRegisterCost length +
    traceHeaderDispatchCost length (traceExtentDispatchCost length continuationCost)

theorem traceFrontRegisterCost_polynomiallyBounded {bound : Nat → Nat}
    (hBound : PolynomiallyBounded bound) :
    PolynomiallyBounded (fun n ↦ traceFrontRegisterCost n (bound n)) :=
  traceHeaderRegisterCost_polynomiallyBounded.add
    (traceHeaderDispatchCost_polynomiallyBounded PolynomiallyBounded.id
      (traceExtentDispatchCost_polynomiallyBounded hBound))

/-- The callback for the successful shape branch of the raw verifier. -/
@[expose] def TraceFrontContinuation (headers : TraceHeaderLane → R)
    (extents : TraceExtentLane → R) (continuation : Fragment R) (word : BinaryWord)
    (before : R → Nat) (suffix : BinaryWord) (bound : Nat) : Prop :=
  ∀ initialized, TraceHeaderRegisterResult headers word before initialized →
    ∀ query cert request candidate, decodePackedPair word = some (query, cert) →
      decodePackedPair query = some (request, candidate) →
      (requestHeaderProgress request).arityValid = true →
      (requestHeaderProgress request).capValid = true →
      TraceExtentContinuation continuation extents word request candidate initialized suffix bound

/-- From empty registers, only correctly framed and sized inputs need a continuation.
Every other raw input receives the exact verifier answer within the same clock. -/
theorem runsOutput_traceFrontRegister (headers : TraceHeaderLane → R)
    (extents : TraceExtentLane → R) (hHeadersInj : Function.Injective headers)
    (hExtents : Function.Injective extents) (hLink : TraceExtentLink headers extents)
    (hSeparate : ∀ lane ∈ extentDispatchHeaderLanes, ∀ k, headers lane ≠ extents k)
    (hNewLanes : ∀ lane, lane ∉ traceExtentInputLanes → ∀ k, extents lane ≠ headers k)
    (continuation : Fragment R) (word : BinaryWord) (before : R → Nat)
    (hZero : ∀ r, before r = 0) (suffix : BinaryWord) (bound : Nat)
    (hNext : TraceFrontContinuation headers extents continuation word before suffix bound) :
    ∃ ticks ≤ traceFrontRegisterCost word.length bound, ∃ after,
      (traceFrontRegister headers extents continuation).RunsOutput word ticks before after suffix
        (checkPackedMergePrefixTraceViolation word :: suffix) := by
  apply runsOutput_traceHeaderRegister_dispatch headers hHeadersInj
    (traceExtentDispatch headers extents continuation) word before
    (fun _ ↦ hZero _) suffix (traceExtentDispatchCost word.length bound)
  intro init hHeaders query cert request candidate hOuter hInner hArity hCap
  have hExtentZero (lane : TraceExtentLane) (h : lane ∉ traceExtentInputLanes) :
      init (extents lane) = 0 :=
    (hHeaders.external _ (hNewLanes lane h)).trans (hZero _)
  exact runsOutput_traceExtentDispatch headers extents hHeadersInj hExtents hLink hSeparate
    continuation hHeaders hOuter hInner hArity hCap hExtentZero suffix bound
    (hNext init hHeaders query cert request candidate hOuter hInner hArity hCap)

end PvsNP.MCSP
