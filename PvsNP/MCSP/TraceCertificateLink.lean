module

public import PvsNP.MCSP.QueryStructureFront
public import PvsNP.MCSP.TraceCertificateDispatch

/-! # Supply the certificate guard with the actual measured sizes -/

public section

namespace PvsNP.MCSP

open Circuits RegisterMachine RegisterMachine.Fragment

variable {R : Type}

/-- The certificate guard owns fresh workspace and retains the measured certificate length. -/
structure TraceCertificateFrontWiring (headers : TraceHeaderLane → R)
    (extents : TraceExtentLane → R)
    (structureFresh : QueryStructureFreshLane → R) (certificateFresh : TraceCertificateLane → R) :
    Prop where
  freshInjective : Function.Injective certificateFresh
  freshHeaders : ∀ lane k, certificateFresh lane ≠ headers k
  freshExtents : ∀ lane k, certificateFresh lane ≠ extents k
  freshStructure : ∀ lane k, certificateFresh lane ≠ structureFresh k
  certificateExtents : ∀ k, headers (.pair .certificateLength) ≠ extents k

private inductive CertificateRef where
  | description (lane : QueryDescriptionsLane)
  | certificateLength
  | fresh (lane : TraceCertificateLane)

private def certificateRef : TraceCertificateLane → CertificateRef
  | .inputLength => .description .inputLength
  | .arity => .description .arity
  | .oldCount => .description (.side true .count)
  | .newCount => .description (.side false .count)
  | .certificateLength => .certificateLength
  | lane => .fresh lane

private theorem certificateRef_injective : Function.Injective certificateRef := by
  intro a b h
  cases a <;> cases b <;> simp_all [certificateRef]

private def resolveCertificateRef (headers : TraceHeaderLane → R)
    (regs : QueryStructureRegisters R) (fresh : TraceCertificateLane → R) : CertificateRef → R
  | .description lane => regs.descriptions lane
  | .certificateLength => headers (.pair .certificateLength)
  | .fresh lane => fresh lane

/-- Reuse the certificate length, arity, raw input length, and the two validated counts. -/
def traceCertificateLanesFromFront (headers : TraceHeaderLane → R) (extents : TraceExtentLane → R)
    (structureFresh : QueryStructureFreshLane → R) (certificateFresh : TraceCertificateLane → R) :
    TraceCertificateLane → R :=
  resolveCertificateRef headers (queryStructureRegistersFromFront headers extents structureFresh)
    certificateFresh ∘ certificateRef

@[simp] theorem traceCertificateLanesFromFront_failure (headers : TraceHeaderLane → R)
    (extents : TraceExtentLane → R) (structureFresh : QueryStructureFreshLane → R)
    (certificateFresh : TraceCertificateLane → R) :
    traceCertificateLanesFromFront headers extents structureFresh certificateFresh .failure =
      certificateFresh .failure := by
  simp [traceCertificateLanesFromFront, resolveCertificateRef, certificateRef]

private theorem certificateLength_separateFromStructure {headers : TraceHeaderLane → R}
    {extents : TraceExtentLane → R} {structureFresh : QueryStructureFreshLane → R}
    {certificateFresh : TraceCertificateLane → R}
    (hFront : QueryStructureFrontWiring headers extents structureFresh)
    (hCert : TraceCertificateFrontWiring headers extents structureFresh certificateFresh) :
    let regs := queryStructureRegistersFromFront headers extents structureFresh
    let r := headers (.pair .certificateLength)
    (∀ lane, r ≠ regs.bases lane) ∧ (∀ lane, r ≠ regs.counterPrefix lane) ∧
      (∀ lane, r ≠ regs.descriptions lane) := by
  apply queryStructureRegistersFromFront_separate headers extents structureFresh
  · intro lane hLane hEq
    have h := hFront.headersInjective hEq
    subst lane
    simp [queryStructureFrontHeaderLanes] at hLane
  · exact hCert.certificateExtents
  · exact fun lane ↦ (hFront.freshHeaders lane _).symm

theorem traceCertificateFresh_separateFromStructure {headers : TraceHeaderLane → R}
    {extents : TraceExtentLane → R} {structureFresh : QueryStructureFreshLane → R}
    {certificateFresh : TraceCertificateLane → R}
    (hCert : TraceCertificateFrontWiring headers extents structureFresh certificateFresh)
    (key : TraceCertificateLane) :
    let regs := queryStructureRegistersFromFront headers extents structureFresh
    (∀ lane, certificateFresh key ≠ regs.bases lane) ∧
      (∀ lane, certificateFresh key ≠ regs.counterPrefix lane) ∧
      (∀ lane, certificateFresh key ≠ regs.descriptions lane) :=
  queryStructureRegistersFromFront_separate headers extents structureFresh _
    (fun lane _ ↦ hCert.freshHeaders key lane) (hCert.freshExtents key) (hCert.freshStructure key)

theorem traceCertificateLanesFromFront_injective {headers : TraceHeaderLane → R}
    {extents : TraceExtentLane → R} {structureFresh : QueryStructureFreshLane → R}
    {certificateFresh : TraceCertificateLane → R}
    (hFront : QueryStructureFrontWiring headers extents structureFresh)
    (hCert : TraceCertificateFrontWiring headers extents structureFresh certificateFresh) :
    Function.Injective (traceCertificateLanesFromFront headers extents structureFresh
      certificateFresh) := by
  have hDescriptions := (queryStructureWiring_fromFront hFront).descriptions
  have hCertDesc := (certificateLength_separateFromStructure hFront hCert).2.2
  have hFreshDesc (lane : TraceCertificateLane) :=
    (traceCertificateFresh_separateFromStructure hCert lane).2.2
  have hResolve : Function.Injective (resolveCertificateRef headers
      (queryStructureRegistersFromFront headers extents structureFresh) certificateFresh) := by
    intro a b h
    cases a with
    | description a =>
      cases b with
      | description b => exact congrArg _ (hDescriptions h)
      | certificateLength => exact (hCertDesc a h.symm).elim
      | fresh b => exact (hFreshDesc b a h.symm).elim
    | certificateLength =>
      cases b with
      | description b => exact (hCertDesc b h).elim
      | certificateLength => rfl
      | fresh b => exact (hCert.freshHeaders b _ h.symm).elim
    | fresh a =>
      cases b with
      | description b => exact (hFreshDesc a b h).elim
      | certificateLength => exact (hCert.freshHeaders a _ h).elim
      | fresh b => exact congrArg _ (hCert.freshInjective h)
  exact hResolve.comp certificateRef_injective

private theorem count_encodeMergeWitness {n cap : Nat} (c : BooleanCircuit n)
    (hSize : c.size ≤ cap) : circuitDescriptionCount n cap (encodeMergeWitness cap c) = c.size := by
  have hWidth : circuitFieldWidth n cap ≤ (encodeCircuit cap c).length := by
    rw [length_encodeCircuit]
    omega
  rw [circuitDescriptionCount, encodeMergeWitness, List.take_append_of_le_length hWidth]
  exact fieldValue_take_encodeCircuit cap c hSize

/-- Successful structure checks supply the actual circuit sizes, with the certificate length
and zero workspace preserved by all preceding stages. -/
theorem traceCertificateDispatchReady_fromFront {headers : TraceHeaderLane → R}
    {extents : TraceExtentLane → R} {structureFresh : QueryStructureFreshLane → R}
    {certificateFresh : TraceCertificateLane → R}
    (hFront : QueryStructureFrontWiring headers extents structureFresh)
    (hCert : TraceCertificateFrontWiring headers extents structureFresh certificateFresh)
    {word query request candidate cert : BinaryWord} {initial measured shaped checked : R → Nat}
    (hHeader : TraceHeaderRegisterResult headers word initial measured)
    (hExtent : TraceExtentRegisterResult extents measured shaped) {fields : MergeRequestFields}
    (hStructure : QueryStructureRegisterResult
      (queryStructureRegistersFromFront headers extents structureFresh)
      request candidate cert fields shaped checked)
    (hOuter : decodePackedPair word = some (query, cert))
    (hFields : readMergeRequestFields request = some fields)
    {r : MergeRequest} {code : BinaryWord} {c : BooleanCircuit r.arity}
    (hValid : ValidMergePrefixTraceQuery (packedPair request candidate) r code c)
    (hFreshZero : ∀ lane, initial (certificateFresh lane) = 0) :
    TraceCertificateDispatchReady
      (traceCertificateLanesFromFront headers extents structureFresh certificateFresh)
      (packedPair request candidate) cert r.arity r.old.size c.size checked := by
  let regs := queryStructureRegistersFromFront headers extents structureFresh
  let certLane := headers (.pair .certificateLength)
  have hComponents : (request, candidate) = (encodeMergeRequest r, code) :=
    packedPair_injective hValid.packed.1
  obtain ⟨hRequest, hCandidate⟩ := Prod.mk.inj hComponents
  have hCanonical : readMergeRequestFields request = some r.fields :=
    decodeMergeRequest_eq_some_iff_readFields.mp (decodeMergeRequest_eq_some_iff.mpr hRequest.symm)
  have hSame := Option.some.inj (hFields.symm.trans hCanonical)
  subst fields
  obtain ⟨hb, hc, hd⟩ := certificateLength_separateFromStructure hFront hCert
  have hCertLength : checked certLane = cert.length :=
    (hStructure.external _ hb hc hd).trans
      ((hExtent.external _ hCert.certificateExtents).trans
        (hHeader.outerLengths query cert hOuter).2)
  have hFresh (lane : TraceCertificateLane) : checked (certificateFresh lane) = 0 := by
    obtain ⟨hb, hc, hd⟩ := traceCertificateFresh_separateFromStructure hCert lane
    exact (hStructure.external _ hb hc hd).trans
      ((hExtent.external _ (hCert.freshExtents lane)).trans
        ((hHeader.external _ (hCert.freshHeaders lane)).trans (hFreshZero lane)))
  have hOldCount : checked (regs.descriptions (.side true .count)) = r.old.size :=
    hStructure.oldCount.trans (count_encodeMergeWitness r.old r.old_size_le)
  have hNewCount : checked (regs.descriptions (.side false .count)) = c.size := by
    apply hStructure.candidateCount.trans
    rw [hCandidate, hValid.code_eq]
    exact count_encodeMergeWitness c hValid.size_le
  refine ⟨hStructure.descriptionSeeds.old.inputLength,
    hStructure.descriptionSeeds.old.arityValue, hOldCount, hNewCount, hCertLength, ?_⟩
  intro lane h
  cases lane <;> first | exact hFresh _ | exact (h (by simp)).elim

end PvsNP.MCSP
