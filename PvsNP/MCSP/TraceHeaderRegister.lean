module

public import PvsNP.MCSP.NestedPairRegister
public import PvsNP.MCSP.RequestHeaderRegister

/-! # Initialize the trace verifier from the raw packed input -/

public section

namespace PvsNP.MCSP

open RegisterMachine RegisterMachine.Fragment

inductive TraceHeaderLane where
  | pair (lane : NestedPairLane)
  | header (lane : RequestHeaderLane)
  | zero | leftCopy | rightCopy | scratch
  deriving DecidableEq

private def pairHeaderCompareLanes : Fin 5 → TraceHeaderLane
  | 0 => .zero
  | 1 => .pair .innerValid
  | 2 => .leftCopy
  | 3 => .rightCopy
  | _ => .scratch

private theorem pairHeaderCompareLanes_injective : Function.Injective pairHeaderCompareLanes := by
  decide

variable {R : Type}

private def prepareTraceHeaders (lanes : TraceHeaderLane → R) : Fragment R :=
  ((incrementBy (lanes (.header .position)) 3).seq
    (add (lanes (.pair .requestLength)) (lanes (.header .remaining))
      (lanes (.header .scratch)))).seq (requestHeaderRegister (lanes ∘ TraceHeaderLane.header))

/-- Read both frames from the input, then run the unary header scans exactly
when the request and candidate are present. All lanes start empty. -/
def traceHeaderRegister (lanes : TraceHeaderLane → R) : Fragment R :=
  (inputLength (lanes (.header .inputLength))).seq
    ((scanNestedPairRegister (lanes ∘ TraceHeaderLane.pair)).seq
      (ifLess (lanes .zero) (lanes (.pair .innerValid)) (lanes .leftCopy)
        (lanes .rightCopy) (lanes .scratch) (prepareTraceHeaders lanes) skip))

@[expose] def traceHeaderRegisterCost (length : Nat) : Nat :=
  nestedPairRegisterCost length + requestHeaderRegisterCost length length + 7 * length + 24

theorem traceHeaderRegisterCost_polynomiallyBounded : PolynomiallyBounded traceHeaderRegisterCost :=
  have hHeaders := requestHeaderRegisterCost_polynomiallyBounded
    PolynomiallyBounded.id PolynomiallyBounded.id
  ((nestedPairRegisterCost_polynomiallyBounded.add hHeaders).add
    ((PolynomiallyBounded.const 7).mul PolynomiallyBounded.id)).add (PolynomiallyBounded.const 24)

private theorem requestHeaderRegisterCost_mono (length : Nat) {a b : Nat} (h : a ≤ b) :
    requestHeaderRegisterCost length a ≤ requestHeaderRegisterCost length b := by
  unfold requestHeaderRegisterCost unaryFieldWindowCost
  exact Nat.mul_le_mul_left 2 (Nat.add_le_add_right (Nat.mul_le_mul_right _ h) _)

/-- The subordinate scanners retain their exact data, with header registers
untouched when the inner packed pair is absent. -/
structure TraceHeaderRegisterResult (lanes : TraceHeaderLane → R) (word : BinaryWord)
    (before after : R → Nat) : Prop where
  inputLength : after (lanes (.header .inputLength)) = word.length
  outerValid : after (lanes (.pair .outerValid)) = (decodePackedPair word).isSome.toNat
  innerValid : after (lanes (.pair .innerValid)) =
    ((decodePackedPair word).bind fun pair ↦ decodePackedPair pair.1).isSome.toNat
  outerLengths : ∀ query cert, decodePackedPair word = some (query, cert) →
    after (lanes (.pair .queryLength)) = query.length ∧
    after (lanes (.pair .certificateLength)) = cert.length
  innerLengths : ∀ query cert request candidate, decodePackedPair word = some (query, cert) →
    decodePackedPair query = some (request, candidate) →
    after (lanes (.pair .requestLength)) = request.length ∧
    after (lanes (.pair .candidateLength)) = candidate.length
  headers : ∀ query cert request candidate, decodePackedPair word = some (query, cert) →
    decodePackedPair query = some (request, candidate) →
    ∃ seeded, RequestHeaderRegisterResult (lanes ∘ TraceHeaderLane.header) request seeded after
  noHeaders : ((decodePackedPair word).bind fun pair ↦ decodePackedPair pair.1) = none →
    ∀ lane : RequestHeaderLane, lane ≠ .inputLength → after (lanes (.header lane)) = 0
  branchZero : after (lanes .zero) = 0
  branchScratch : after (lanes .leftCopy) = 0 ∧ after (lanes .rightCopy) = 0 ∧
    after (lanes .scratch) = 0
  external : ∀ r, (∀ lane, r ≠ lanes lane) → after r = before r

variable [DecidableEq R]

private theorem runsValues_prepareTraceHeaders (lanes : TraceHeaderLane → R)
    (hLanes : Function.Injective lanes) (request candidate cert : BinaryWord) (before : R → Nat)
    (hLength : before (lanes (.header .inputLength)) =
      (packedPair (packedPair request candidate) cert).length)
    (hRequest : before (lanes (.pair .requestLength)) = request.length)
    (hZero : ∀ lane : RequestHeaderLane, lane ≠ .inputLength →
      before (lanes (.header lane)) = 0) :
    let word := packedPair (packedPair request candidate) cert
    ∃ ticks ≤ 5 * request.length + 5 + requestHeaderRegisterCost word.length request.length,
      ∃ after : R → Nat, (prepareTraceHeaders lanes).RunsValues word ticks before after ∧
        after (lanes (.header .inputLength)) = word.length ∧
        (∃ seeded, RequestHeaderRegisterResult (lanes ∘ TraceHeaderLane.header)
          request seeded after) ∧
        ∀ r, (∀ lane, r ≠ lanes (.header lane)) → after r = before r := by
  let word := packedPair (packedPair request candidate) cert
  let position := lanes (.header .position)
  let remaining := lanes (.header .remaining)
  let scratch := lanes (.header .scratch)
  let positioned := setValue position 3 before
  let seeded := setValue remaining request.length positioned
  have hEq (a b : TraceHeaderLane) : lanes a = lanes b ↔ a = b :=
    ⟨fun h ↦ hLanes h, congrArg lanes⟩
  have hInc : (incrementBy position 3).RunsValues word 3 before positioned := by
    simpa only [positioned, position, hZero .position (by decide), Nat.zero_add] using
      runsValues_incrementBy position 3 word before
  have hCopy := runsValues_add (lanes (.pair .requestLength)) remaining scratch word positioned
    (by simp [remaining, hEq]) (by simp [scratch, hEq]) (by simp [remaining, scratch, hEq])
    (by simp [positioned, position, scratch, setValue, hEq, hZero])
  have hCopyRun : (add (lanes (.pair .requestLength)) remaining scratch).RunsValues
      word (5 * request.length + 2) positioned seeded := by
    have hRead : positioned (lanes (.pair .requestLength)) = request.length := by
      simpa [positioned, position, setValue, hEq] using hRequest
    have hEmpty : positioned remaining = 0 := by
      simp [positioned, position, remaining, setValue, hEq, hZero]
    simpa only [hRead, hEmpty, Nat.zero_add, seeded] using hCopy
  have hSeedFrame (r : R) (hPos : r ≠ position) (hRem : r ≠ remaining) :
      seeded r = before r := by simp [seeded, positioned, setValue, hPos, hRem]
  have hSeedZero (lane : RequestHeaderLane) (hl : lane ≠ .inputLength)
      (hp : lane ≠ .position) (hw : lane ≠ .remaining) : seeded (lanes (.header lane)) = 0 :=
    (hSeedFrame _ (by simpa [position, hEq] using hp)
      (by simpa [remaining, hEq] using hw)).trans (hZero lane hl)
  have hSeedPosition : seeded position = 3 := by
    simp [seeded, positioned, position, remaining, setValue, hEq]
  obtain ⟨ticks, hTicks, after, hRun, hResult⟩ :=
    runsValues_requestHeaderRegister (lanes ∘ TraceHeaderLane.header)
      (hLanes.comp fun _ _ h ↦ TraceHeaderLane.header.inj h)
      request candidate cert seeded
      ((hSeedFrame _ (by simp [position, hEq]) (by simp [remaining, hEq])).trans hLength)
      hSeedPosition (setValue_same ..) hSeedZero
  refine ⟨3 + (5 * request.length + 2) + ticks, by omega, after,
    (hInc.seq hCopyRun).seq hRun, ?_, ⟨seeded, hResult⟩, ?_⟩
  · rw [hResult.frame _ (by simp [hEq]) (by simp [hEq]) (by simp [hEq]) (by simp [hEq])
      (by simp [hEq]) (by simp [hEq])]
    exact (hSeedFrame _ (by simp [position, hEq]) (by simp [remaining, hEq])).trans hLength
  · intro r hLane
    exact (hResult.frame r (hLane _) (hLane _) (hLane _) (hLane _) (hLane _) (hLane _)).trans
      (hSeedFrame r (hLane _) (hLane _))

/-- On any binary input, initialize only the registers justified by successful
frames and preserve the exact results for malformed input as well. -/
theorem runsValues_traceHeaderRegister (lanes : TraceHeaderLane → R)
    (hLanes : Function.Injective lanes) (word : BinaryWord) (before : R → Nat)
    (hZero : ∀ lane, before (lanes lane) = 0) :
    ∃ ticks ≤ traceHeaderRegisterCost word.length, ∃ after : R → Nat,
      (traceHeaderRegister lanes).RunsValues word ticks before after ∧
      TraceHeaderRegisterResult lanes word before after := by
  let lengthLane := lanes (.header .inputLength)
  let measured := setValue lengthLane word.length before
  let pairLanes := lanes ∘ TraceHeaderLane.pair
  let branch := prepareTraceHeaders lanes
  let inner := (decodePackedPair word).bind fun pair ↦ decodePackedPair pair.1
  have hEq (a b : TraceHeaderLane) : lanes a = lanes b ↔ a = b :=
    ⟨fun h ↦ hLanes h, congrArg lanes⟩
  have hMeasured (lane : TraceHeaderLane) (h : lane ≠ .header .inputLength) :
      measured (lanes lane) = 0 :=
    (setValue_other (by simpa [lengthLane, hEq] using h) ..).trans (hZero lane)
  have hLength : (inputLength lengthLane).RunsValues word
      (2 * word.length + 1) before measured := by
    simpa only [measured, lengthLane, hZero (.header .inputLength), Nat.zero_add] using
      runsValues_inputLength lengthLane word before
  obtain ⟨pairTicks, hPairTicks, mid, hPairRun, hPairResult⟩ :=
    runsValues_scanNestedPairRegister pairLanes
      (hLanes.comp fun _ _ h ↦ TraceHeaderLane.pair.inj h) word measured
      (fun lane ↦ hMeasured (.pair lane) (by simp))
  have hMidLanes (lane : TraceHeaderLane) (h : ∀ p, lane ≠ .pair p) :
      mid (lanes lane) = measured (lanes lane) :=
    hPairResult.frame _ (fun p ↦ fun he ↦ h p (hLanes he))
  have hMidLength : mid lengthLane = word.length :=
    (hMidLanes (.header .inputLength) (by simp)).trans (setValue_same ..)
  have hMidZero (lane : TraceHeaderLane) (h : ∀ p, lane ≠ .pair p)
      (hLen : lane ≠ .header .inputLength) : mid (lanes lane) = 0 :=
    (hMidLanes lane h).trans (hMeasured lane hLen)
  have hMidHeader (lane : RequestHeaderLane) (h : lane ≠ .inputLength) :
      mid (lanes (.header lane)) = 0 := hMidZero _ (by simp) (by simpa using h)
  have hFlag : mid (lanes (.pair .innerValid)) = inner.isSome.toNat := hPairResult.innerValid
  have hBranchZero : mid (lanes .zero) = 0 := hMidZero _ (by simp) (by simp)
  have hLeft : mid (lanes .leftCopy) = 0 := hMidZero _ (by simp) (by simp)
  have hRight : mid (lanes .rightCopy) = 0 := hMidZero _ (by simp) (by simp)
  have hScratch : mid (lanes .scratch) = 0 := hMidZero _ (by simp) (by simp)
  have hMake {after : R → Nat} (hFrame : ∀ r,
      (∀ lane : RequestHeaderLane, r ≠ lanes (.header lane)) → after r = mid r)
      (hLen : after lengthLane = word.length)
      (hHeaders : ∀ query cert request candidate, decodePackedPair word = some (query, cert) →
        decodePackedPair query = some (request, candidate) →
        ∃ seeded, RequestHeaderRegisterResult (lanes ∘ TraceHeaderLane.header)
          request seeded after)
      (hAbsent : inner = none → ∀ lane : RequestHeaderLane, lane ≠ .inputLength →
        after (lanes (.header lane)) = 0) :
      TraceHeaderRegisterResult lanes word before after := by
    have hKeepPair (lane : NestedPairLane) : after (pairLanes lane) = mid (pairLanes lane) :=
      hFrame _ (by simp [pairLanes, hEq])
    have hKeepOthers (lane : TraceHeaderLane) (h : ∀ p, lane ≠ .header p) :
        after (lanes lane) = mid (lanes lane) := hFrame _ (fun p he ↦ h p (hLanes he))
    refine ⟨hLen, (hKeepPair _).trans hPairResult.outerValid,
      (hKeepPair _).trans hPairResult.innerValid, ?_, ?_, hHeaders, hAbsent,
      (hKeepOthers .zero (by simp)).trans hBranchZero,
      ⟨(hKeepOthers .leftCopy (by simp)).trans hLeft,
        (hKeepOthers .rightCopy (by simp)).trans hRight,
        (hKeepOthers .scratch (by simp)).trans hScratch⟩, ?_⟩
    · intro q c h
      obtain ⟨hq, hc⟩ := hPairResult.outerLengths q c h
      exact ⟨(hKeepPair _).trans hq, (hKeepPair _).trans hc⟩
    · intro q c r t h₁ h₂
      obtain ⟨hr, ht⟩ := hPairResult.innerLengths q c r t h₁ h₂
      exact ⟨(hKeepPair _).trans hr, (hKeepPair _).trans ht⟩
    · intro r h
      exact (hFrame r (fun lane ↦ h (.header lane))).trans
        ((hPairResult.frame r (fun lane ↦ h (.pair lane))).trans
          (setValue_other (h (.header .inputLength)) ..))
  have hChoose {ticks : Nat} {after : R → Nat}
      (h : (if mid (lanes .zero) < mid (lanes (.pair .innerValid)) then branch else skip).RunsValues
        word ticks mid after) :
      (ifLess (lanes .zero) (lanes (.pair .innerValid)) (lanes .leftCopy) (lanes .rightCopy)
        (lanes .scratch) branch skip).RunsValues word
          (ifEqualTime (mid (lanes .zero)) (mid (lanes (.pair .innerValid))) + ticks) mid after :=
    runsValues_ifLess (lanes ∘ pairHeaderCompareLanes)
      (hLanes.comp pairHeaderCompareLanes_injective) branch skip word mid hLeft hRight hScratch h
  cases hInner : inner with
  | none =>
    have hBad : mid (lanes (.pair .innerValid)) = 0 := by simp [hFlag, hInner]
    have hSkip := hChoose (by
      simpa only [hBranchZero, hBad, Nat.lt_irrefl, ite_false] using runsValues_skip word mid)
    rw [hBranchZero, hBad] at hSkip
    refine ⟨2 * word.length + 1 + (pairTicks + (ifEqualTime 0 0 + 0)), ?_, mid,
      hLength.seq (hPairRun.seq hSkip), hMake (fun _ _ ↦ rfl) hMidLength ?_ (fun _ ↦ hMidHeader)⟩
    · unfold traceHeaderRegisterCost ifEqualTime
      omega
    · intro query cert request candidate hOuter hDecoded
      simp only [inner, hOuter, Option.bind_some, hDecoded] at hInner
      contradiction
  | some pair =>
    obtain ⟨request, candidate⟩ := pair
    obtain ⟨⟨query, cert⟩, hOuter, hDecoded⟩ := Option.bind_eq_some_iff.mp hInner
    change decodePackedPair query = some (request, candidate) at hDecoded
    have hValid : mid (lanes (.pair .innerValid)) = 1 := by simp [hFlag, hInner]
    have hPacking : word = packedPair (packedPair request candidate) cert := by
      rw [decodePackedPair_eq_some_iff.mp hOuter, decodePackedPair_eq_some_iff.mp hDecoded]
    have hReq := (hPairResult.innerLengths query cert request candidate hOuter hDecoded).1
    obtain ⟨headerTicks, hHeaderTicks, after, hHeadersRun, hAfterLength, hHeaders, hFrame⟩ :=
      runsValues_prepareTraceHeaders lanes hLanes request candidate cert mid
        (hMidLength.trans (congrArg List.length hPacking)) hReq hMidHeader
    rw [← hPacking] at hHeaderTicks hHeadersRun hAfterLength
    have hRun := hChoose (by simpa only [hBranchZero, hValid, Nat.zero_lt_one, ite_true]
      using hHeadersRun)
    rw [hBranchZero, hValid] at hRun
    refine ⟨2 * word.length + 1 + (pairTicks + (ifEqualTime 0 1 + headerTicks)), ?_, after,
      hLength.seq (hPairRun.seq hRun), hMake hFrame hAfterLength ?_ ?_⟩
    · have hReqLen : request.length ≤ word.length := by
        rw [hPacking, length_packedPair, length_packedPair]
        omega
      have hHeadBound := requestHeaderRegisterCost_mono word.length hReqLen
      unfold traceHeaderRegisterCost ifEqualTime
      omega
    · intro q c req cand h₁ h₂
      rw [hOuter, Option.some.injEq, Prod.mk.injEq] at h₁
      obtain ⟨rfl, rfl⟩ := h₁
      rw [hDecoded, Option.some.injEq, Prod.mk.injEq] at h₂
      obtain ⟨rfl, rfl⟩ := h₂
      exact hHeaders
    · intro h
      rw [h] at hInner
      contradiction

end PvsNP.MCSP
