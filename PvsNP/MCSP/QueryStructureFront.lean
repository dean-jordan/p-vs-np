module

public import PvsNP.MCSP.QueryStructureRegister

/-! # Seed the query structure checker from the measured front of the verifier -/

public section

namespace PvsNP.MCSP

open Circuits RegisterMachine RegisterMachine.Fragment

/-- Fresh addresses, workspace, and outputs for the three structure stages. -/
inductive QueryStructureFreshLane where
  | bases (lane : TraceQueryBaseLane)
  | counterPrefix (lane : QueryCounterPrefixLane)
  | descriptions (lane : QueryDescriptionsLane)
  deriving DecidableEq

/-- The header registers that the structure checker reads directly. -/
@[expose] def queryStructureFrontHeaderLanes : List TraceHeaderLane :=
  [.header .inputLength, .header .position, .pair .requestLength]

variable {R : Type}

/-- The extent calculation must preserve the three reused header registers. -/
structure QueryStructureFrontWiring (headers : TraceHeaderLane → R) (extents : TraceExtentLane → R)
    (fresh : QueryStructureFreshLane → R) : Prop where
  headersInjective : Function.Injective headers
  extentsInjective : Function.Injective extents
  freshInjective : Function.Injective fresh
  preservedHeaders : ∀ lane ∈ queryStructureFrontHeaderLanes, ∀ k, headers lane ≠ extents k
  freshHeaders : ∀ lane k, fresh lane ≠ headers k
  freshExtents : ∀ lane k, fresh lane ≠ extents k

private inductive FrontHeader where
  | length | counter | request

private def frontHeaderLane : FrontHeader → TraceHeaderLane
  | .length => .header .inputLength
  | .counter => .header .position
  | .request => .pair .requestLength

private theorem frontHeaderLane_injective : Function.Injective frontHeaderLane := by
  intro a b h
  cases a <;> cases b <;> simp_all [frontHeaderLane]

private theorem frontHeaderLane_mem (lane : FrontHeader) :
    frontHeaderLane lane ∈ queryStructureFrontHeaderLanes := by
  cases lane <;> simp [frontHeaderLane, queryStructureFrontHeaderLanes]

private inductive FrontRef where
  | header (lane : FrontHeader)
  | extent (lane : TraceExtentLane)
  | fresh (lane : QueryStructureFreshLane)

private def resolveFrontRef (headers : TraceHeaderLane → R) (extents : TraceExtentLane → R)
    (fresh : QueryStructureFreshLane → R) : FrontRef → R
  | .header lane => headers (frontHeaderLane lane)
  | .extent lane => extents lane
  | .fresh lane => fresh lane

private theorem resolveFrontRef_injective {headers : TraceHeaderLane → R}
    {extents : TraceExtentLane → R} {fresh : QueryStructureFreshLane → R}
    (h : QueryStructureFrontWiring headers extents fresh) :
    Function.Injective (resolveFrontRef headers extents fresh) := by
  intro a b he
  cases a with
  | header a =>
    cases b with
    | header b => exact congrArg _ (frontHeaderLane_injective (h.headersInjective he))
    | extent b => exact (h.preservedHeaders _ (frontHeaderLane_mem a) b he).elim
    | fresh b => exact (h.freshHeaders b _ he.symm).elim
  | extent a =>
    cases b with
    | header b => exact (h.preservedHeaders _ (frontHeaderLane_mem b) a he.symm).elim
    | extent b => exact congrArg _ (h.extentsInjective he)
    | fresh b => exact (h.freshExtents b a he.symm).elim
  | fresh a =>
    cases b with
    | header b => exact (h.freshHeaders a _ he).elim
    | extent b => exact (h.freshExtents a b he).elim
    | fresh b => exact congrArg _ (h.freshInjective he)

private def frontBaseRef : TraceQueryBaseLane → FrontRef
  | .arity => .extent .arity
  | .header => .header .counter
  | .requestLength => .header .request
  | .prefixLength => .extent .prefixLength
  | lane => .fresh (.bases lane)

private theorem frontBaseRef_injective : Function.Injective frontBaseRef := by
  intro a b h
  cases a <;> cases b <;> simp_all [frontBaseRef]

private def frontCounterPrefixRef : QueryCounterPrefixLane → FrontRef
  | .inputLength => .header .length
  | .counterStart => .header .counter
  | .requestLength => .header .request
  | .requestPrefixStart => .fresh (.bases .prefixStart)
  | .arity => .extent .arity
  | .prefixLength => .extent .prefixLength
  | lane => .fresh (.counterPrefix lane)

private theorem frontCounterPrefixRef_injective : Function.Injective frontCounterPrefixRef := by
  let back : FrontRef → QueryCounterPrefixLane
    | .header .length => .inputLength
    | .header .counter => .counterStart
    | .header .request => .requestLength
    | .fresh (.bases .prefixStart) => .requestPrefixStart
    | .extent .arity => .arity
    | .extent .prefixLength => .prefixLength
    | .fresh (.counterPrefix lane) => lane
    | _ => .order
  have hBack : Function.LeftInverse back frontCounterPrefixRef := by intro lane; cases lane <;> rfl
  exact hBack.injective

private def frontDescriptionRef : QueryDescriptionsLane → FrontRef
  | .arity => .extent .arity
  | .inputLength => .header .length
  | .side old .base => .fresh (.bases (if old then .oldBase else .candidateBase))
  | .side old .cap => .extent (if old then .oldCap else .cap)
  | .side old .width => .extent (.width old)
  | .side old .span => .extent (.span old)
  | .side old .paddedLength => .extent (.paddedLength old)
  | lane => .fresh (.descriptions lane)

private theorem frontDescriptionRef_injective : Function.Injective frontDescriptionRef := by
  let back : FrontRef → QueryDescriptionsLane
    | .extent .arity => .arity
    | .header .length => .inputLength
    | .fresh (.bases .oldBase) => .side true .base
    | .fresh (.bases .candidateBase) => .side false .base
    | .extent .oldCap => .side true .cap
    | .extent .cap => .side false .cap
    | .extent (.width old) => .side old .width
    | .extent (.span old) => .side old .span
    | .extent (.paddedLength old) => .side old .paddedLength
    | .fresh (.descriptions lane) => lane
    | _ => .failures
  have hBack : Function.LeftInverse back frontDescriptionRef := by
    intro lane
    cases lane with
    | side old lane => cases old <;> cases lane <;> rfl
    | arity | inputLength | failures => rfl
  exact hBack.injective

/-- Reuse the measured lengths and layouts and share the computed bases with their consumers. -/
def queryStructureRegistersFromFront (headers : TraceHeaderLane → R) (extents : TraceExtentLane → R)
    (fresh : QueryStructureFreshLane → R) : QueryStructureRegisters R :=
  let resolve := resolveFrontRef headers extents fresh
  ⟨resolve ∘ frontBaseRef, resolve ∘ frontCounterPrefixRef, resolve ∘ frontDescriptionRef⟩

/-- The count outputs are the fresh description registers. -/
@[simp] theorem queryStructureRegistersFromFront_count (headers : TraceHeaderLane → R)
    (extents : TraceExtentLane → R) (fresh : QueryStructureFreshLane → R) (old : Bool) :
    (queryStructureRegistersFromFront headers extents fresh).descriptions (.side old .count) =
      fresh (.descriptions (.side old .count)) := by
  simp [queryStructureRegistersFromFront, frontDescriptionRef, resolveFrontRef]

@[simp] theorem queryStructureRegistersFromFront_failures (headers : TraceHeaderLane → R)
    (extents : TraceExtentLane → R) (fresh : QueryStructureFreshLane → R) :
    (queryStructureRegistersFromFront headers extents fresh).descriptions .failures =
      fresh (.descriptions .failures) := by
  simp [queryStructureRegistersFromFront, frontDescriptionRef, resolveFrontRef]

theorem queryStructureWiring_fromFront {headers : TraceHeaderLane → R}
    {extents : TraceExtentLane → R} {fresh : QueryStructureFreshLane → R}
    (hWiring : QueryStructureFrontWiring headers extents fresh) :
    QueryStructureWiring (queryStructureRegistersFromFront headers extents fresh) := by
  have hInj := resolveFrontRef_injective hWiring
  have hExcept (lane : QueryDescriptionsLane) (side : QueryCounterPrefixLane) :
      FrontRef.fresh (.counterPrefix side) ≠ frontDescriptionRef lane := by
    cases lane with
    | side old lane => cases old <;> cases lane <;> simp [frontDescriptionRef]
    | arity | inputLength | failures => simp [frontDescriptionRef]
  exact ⟨hInj.comp frontBaseRef_injective, hInj.comp frontCounterPrefixRef_injective,
    hInj.comp frontDescriptionRef_injective, fun lane he ↦ hExcept lane .high (hInj he),
    fun lane he ↦ hExcept lane .lowerOnes (hInj he), fun lane he ↦ hExcept lane .order (hInj he)⟩

/-- Registers outside the reused inputs and fresh bank are outside every structure stage. -/
theorem queryStructureRegistersFromFront_separate (headers : TraceHeaderLane → R)
    (extents : TraceExtentLane → R) (fresh : QueryStructureFreshLane → R) (r : R)
    (hHeaders : ∀ lane ∈ queryStructureFrontHeaderLanes, r ≠ headers lane)
    (hExtents : ∀ lane, r ≠ extents lane) (hFresh : ∀ lane, r ≠ fresh lane) :
    let regs := queryStructureRegistersFromFront headers extents fresh
    (∀ lane, r ≠ regs.bases lane) ∧ (∀ lane, r ≠ regs.counterPrefix lane) ∧
      (∀ lane, r ≠ regs.descriptions lane) := by
  have hRef (ref : FrontRef) : r ≠ resolveFrontRef headers extents fresh ref := by
    cases ref with
    | header p => exact hHeaders _ (frontHeaderLane_mem p)
    | extent p => exact hExtents p
    | fresh p => exact hFresh p
  exact ⟨fun lane ↦ hRef (frontBaseRef lane), fun lane ↦ hRef (frontCounterPrefixRef lane),
    fun lane ↦ hRef (frontDescriptionRef lane)⟩

variable [DecidableEq R]

/-- The successful header and extent results provide every structure seed. The fresh
bank remains zero until the structure stage writes the three addresses. -/
theorem queryStructureReady_fromFront {headers : TraceHeaderLane → R}
    {extents : TraceExtentLane → R} {fresh : QueryStructureFreshLane → R}
    (hWiring : QueryStructureFrontWiring headers extents fresh)
    (hLink : TraceExtentLink headers extents)
    {word query cert request candidate : BinaryWord} {initial measured shaped : R → Nat}
    (hHeader : TraceHeaderRegisterResult headers word initial measured)
    (hExtent : TraceExtentRegisterResult extents measured shaped)
    (hOuter : decodePackedPair word = some (query, cert))
    (hInner : decodePackedPair query = some (request, candidate))
    {fields : MergeRequestFields} (hFields : readMergeRequestFields request = some fields)
    (hFreshZero : ∀ lane, initial (fresh lane) = 0) :
    QueryStructureReady (queryStructureRegistersFromFront headers extents fresh)
      word request fields shaped := by
  let regs := queryStructureRegistersFromFront headers extents fresh
  let resolve := resolveFrontRef headers extents fresh
  let seeded := queryStructureAddressValues regs request fields shaped
  let oldBase := FrontRef.fresh (.bases .oldBase)
  let newBase := FrontRef.fresh (.bases .candidateBase)
  let prefStart := FrontRef.fresh (.bases .prefixStart)
  have hInj : Function.Injective resolve := resolveFrontRef_injective hWiring
  have hHeaderKeep (lane : TraceHeaderLane) (h : lane ∈ queryStructureFrontHeaderLanes) :
      shaped (headers lane) = measured (headers lane) :=
    hExtent.external _ (hWiring.preservedHeaders lane h)
  have hFresh (lane : QueryStructureFreshLane) : shaped (fresh lane) = 0 :=
    (hExtent.external _ (hWiring.freshExtents lane)).trans
      ((hHeader.external _ (hWiring.freshHeaders lane)).trans (hFreshZero lane))
  obtain ⟨_, hMeasured⟩ := hHeader.headers query cert request candidate hOuter hInner
  obtain ⟨hn, hc, _⟩ := readMergeRequestFields_header_progress hFields
  have hFlags := (readMergeRequestFields_isSome_iff request).mp (by simp [hFields])
  have hLength : shaped (headers (.header .inputLength)) = word.length :=
    (hHeaderKeep _ (frontHeaderLane_mem .length)).trans hHeader.inputLength
  have hCounter : shaped (headers (.header .position)) = 4 * fields.counterStart + 3 := by
    have hPosition : measured (headers (.header .position)) =
        3 + 4 * (requestHeaderProgress request).consumed := hMeasured.position
    rw [hHeaderKeep (.header .position) (by simp [queryStructureFrontHeaderLanes]), hPosition]
    simp only [RequestHeaderProgress.consumed, hFlags.1, hFlags.2.1, Bool.toNat_true,
      hn, hc, MergeRequestFields.counterStart]
    omega
  have hRequest : shaped (headers (.pair .requestLength)) = request.length :=
    (hHeaderKeep _ (frontHeaderLane_mem .request)).trans
      (hHeader.innerLengths query cert request candidate hOuter hInner).1
  have hArity : measured (extents .arity) = (requestHeaderProgress request).arity := by
    rw [hLink.arity]
    exact hMeasured.arity
  have hCap : measured (extents .cap) = (requestHeaderProgress request).cap := by
    rw [hLink.cap]
    exact hMeasured.cap
  have hBody : measured (extents .bodyLength) =
      (request.drop (requestHeaderProgress request).consumed).length := by
    rw [hLink.bodyLength]
    exact hMeasured.remaining
  have hPrefix := hExtent.prefixLength_of_fields hFields hArity hCap hBody
  have hAfterArity : shaped (extents .arity) = fields.arity :=
    (hExtent.inputs .arity (by simp [traceExtentInputLanes])).trans (hArity.trans hn)
  have hAfterCap : ∀ old : Bool, shaped (extents (if old then .oldCap else .cap)) =
      (if old then max 1 fields.cap else fields.cap) := by
    intro old
    cases old
    · exact (hExtent.inputs .cap (by simp [traceExtentInputLanes])).trans (hCap.trans hc)
    · exact hExtent.oldCap.trans (congrArg (max 1) (hCap.trans hc))
  have hWidth (old : Bool) : shaped (extents (.width old)) = circuitFieldWidth fields.arity
      (if old then max 1 fields.cap else fields.cap) := by
    rw [hExtent.width, hArity, hCap, hn, hc]
  have hPadded (old : Bool) : shaped (extents (.paddedLength old)) = mergeWitnessLength fields.arity
      (if old then max 1 fields.cap else fields.cap) := by
    rw [hExtent.paddedLength, hArity, hCap, hn, hc]
  have hKeep (ref : FrontRef) (hp : ref ≠ prefStart) (hn : ref ≠ newBase) (ho : ref ≠ oldBase) :
      seeded (resolve ref) = shaped (resolve ref) :=
    (setValue_other (fun h ↦ hp (hInj h)) ..).trans
      ((setValue_other (fun h ↦ hn (hInj h)) ..).trans (setValue_other (fun h ↦ ho (hInj h)) ..))
  have hDistinct {a b : FrontRef} (h : a ≠ b) : resolve a ≠ resolve b := fun e ↦ h (hInj e)
  have hNewPref : newBase ≠ prefStart := by simp [newBase, prefStart]
  have hOldPref : oldBase ≠ prefStart := by simp [oldBase, prefStart]
  have hOldNew : oldBase ≠ newBase := by simp [oldBase, newBase]
  have hPrefAddress : seeded (resolve prefStart) = fields.prefStart := setValue_same ..
  have hNewAddress : seeded (resolve newBase) = 4 * (request.length + 1) + 3 :=
    (setValue_other (hDistinct hNewPref) ..).trans (setValue_same ..)
  have hOldAddress : seeded (resolve oldBase) = 4 * fields.oldStart + 3 :=
    (setValue_other (hDistinct hOldPref) ..).trans
      ((setValue_other (hDistinct hOldNew) ..).trans (setValue_same ..))
  have hKeepHeader (lane : FrontHeader) : seeded (headers (frontHeaderLane lane)) =
      shaped (headers (frontHeaderLane lane)) := hKeep (.header lane) (by simp [prefStart])
    (by simp [newBase]) (by simp [oldBase])
  have hKeepExtent (lane : TraceExtentLane) : seeded (extents lane) = shaped (extents lane) :=
    hKeep (.extent lane) (by simp [prefStart]) (by simp [newBase]) (by simp [oldBase])
  have hCounterZero (lane : QueryCounterPrefixLane)
      (h : lane ∉ [.inputLength, .counterStart, .requestLength, .requestPrefixStart,
        .arity, .prefixLength]) : seeded (regs.counterPrefix lane) = 0 := by
    have hFreshCounter (lane : QueryCounterPrefixLane) :
        seeded (resolve (.fresh (.counterPrefix lane))) = 0 :=
      (hKeep _ (by simp [prefStart]) (by simp [newBase]) (by simp [oldBase])).trans
        (hFresh (.counterPrefix lane))
    cases lane <;> first | exact hFreshCounter _ | exact (h (by simp)).elim
  have hDescriptionSeed (old : Bool) :
      CheckedDescriptionSeed (regs.descriptions ∘ queryDescriptionLanes old) word
        (if old then 4 * fields.oldStart + 3 else 4 * (request.length + 1) + 3) fields.arity
        (if old then max 1 fields.cap else fields.cap) seeded := by
    refine ⟨(hKeepExtent .arity).trans hAfterArity,
      (hKeepExtent _).trans (hAfterCap old), (hKeepExtent _).trans (hWidth old), ?_,
      (hKeepExtent _).trans (hPadded old), (hKeepHeader .length).trans hLength, ?_⟩
    · exact (hKeepExtent _).trans ((hExtent.span old).trans
        (congrArg (fun width ↦ 3 + 2 * width) (hWidth old)))
    · cases old
      · exact hNewAddress
      · exact hOldAddress
  have hFreshDesc (lane : QueryDescriptionsLane) : seeded (resolve (.fresh (.descriptions lane))) =
      0 := (hKeep _ (by simp [prefStart]) (by simp [newBase]) (by simp [oldBase])).trans
        (hFresh (.descriptions lane))
  refine ⟨hAfterArity, hCounter, hRequest, hPrefix, ?_, ?_,
    ⟨hDescriptionSeed true, hDescriptionSeed false⟩, ?_, hFreshDesc .failures⟩
  · intro lane ha hh hr hp
    cases lane <;>
      first | exact (ha rfl).elim | exact (hh rfl).elim | exact (hr rfl).elim |
        exact (hp rfl).elim | exact hFresh (.bases _)
  · exact ⟨(hKeepHeader .length).trans hLength, (hKeepHeader .counter).trans hCounter,
      (hKeepHeader .request).trans hRequest, hPrefAddress, (hKeepExtent .arity).trans hAfterArity,
      (hKeepExtent .prefixLength).trans hPrefix, hCounterZero⟩
  · intro old lane h
    cases lane <;> first | exact hFreshDesc (.side old _) |
      exact (h (by simp [checkedDescriptionInputLanes])).elim

end PvsNP.MCSP
