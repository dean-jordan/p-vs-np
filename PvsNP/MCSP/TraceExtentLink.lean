module

public import PvsNP.MCSP.TraceExtentRegister
public import PvsNP.MCSP.TraceHeaderRegister
public import PvsNP.MCSP.TraceQueryBaseRegister
public import PvsNP.MCSP.PackedRequestLayout

/-! # Connect measured packed fields to the extent calculation -/

public section

namespace PvsNP.MCSP

open Circuits RegisterMachine RegisterMachine.Fragment

private theorem fieldWidth_le {n m cap budget : Nat} (hn : n ≤ m) (hc : cap ≤ budget) :
    circuitFieldWidth n cap ≤ circuitFieldWidth m budget := by
  have hAdd := Nat.add_le_add hn hc
  unfold circuitFieldWidth
  apply Nat.succ_le_succ
  by_cases hZero : n + cap = 0
  · simp [hZero]
  · have hPositive : m + budget ≠ 0 := by omega
    exact (Nat.le_log2 hPositive).mpr ((Nat.log2_self_le hZero).trans hAdd)

private theorem witnessLength_le {n m cap budget : Nat} (hn : n ≤ m) (hc : cap ≤ budget) :
    mergeWitnessLength n cap ≤ mergeWitnessLength m budget := by
  have hWidth := fieldWidth_le hn hc
  have hSpan : 3 + 2 * circuitFieldWidth n cap ≤ 3 + 2 * circuitFieldWidth m budget := by omega
  exact Nat.add_le_add (Nat.mul_le_mul_left 2 hWidth) (Nat.mul_le_mul hc hSpan)

private theorem layoutCost_le {n m cap budget : Nat} (hn : n ≤ m) (hc : cap ≤ budget) :
    circuitLayoutRegisterCost n cap ≤ circuitLayoutRegisterCost m budget := by
  let w := circuitFieldWidth n cap
  let W := circuitFieldWidth m budget
  have hWidth : w ≤ W := fieldWidth_le hn hc
  have hBound := Nat.add_le_add hn hc
  have hProduct : cap * (5 * (3 + 2 * w) + 3) ≤ budget * (5 * (3 + 2 * W) + 3) :=
    Nat.mul_le_mul hc (by omega)
  have hLoop : (n + cap) * (40 * (n + cap + 1) + 10) ≤
      (m + budget) * (40 * (m + budget + 1) + 10) :=
    Nat.mul_le_mul hBound (by omega)
  have hLogCost : fieldWidthRegisterCost (n + cap) ≤ fieldWidthRegisterCost (m + budget) := by
    unfold fieldWidthRegisterCost
    omega
  have hSpan := affineTime_mono 2 3 hWidth
  have hHeader := affineTime_mono 2 0 hWidth
  change (5 * n + 2) + (5 * cap + 2) + fieldWidthRegisterCost (n + cap) +
    affineTime 2 3 w + affineTime 2 0 w + (5 * cap + 2) + (cap * (5 * (3 + 2 * w) + 3) + 1) ≤
    (5 * m + 2) + (5 * budget + 2) + fieldWidthRegisterCost (m + budget) +
    affineTime 2 3 W + affineTime 2 0 W + (5 * budget + 2) +
      (budget * (5 * (3 + 2 * W) + 3) + 1)
  omega

/-- A single input length bounds the cost whenever all four measured values fit it. -/
theorem traceExtentRegisterCost_le_length {n cap body candidate length : Nat}
    (hn : n ≤ length) (hc : cap ≤ length) (hb : body ≤ length) (hl : candidate ≤ length) :
    traceExtentRegisterCost n cap body candidate ≤
      traceExtentRegisterCost length length length length := by
  have hCap : max 1 cap ≤ max 1 length :=
    Nat.max_le.mpr ⟨Nat.le_max_left .., hc.trans (Nat.le_max_right ..)⟩
  have hOld := layoutCost_le hn hCap
  have hNew := layoutCost_le hn hc
  have hOldLength := witnessLength_le hn hCap
  have hNewLength := witnessLength_le hn hc
  unfold traceExtentRegisterCost requestShapeRegisterCost
  omega

theorem traceExtentRegisterCost_length_polynomiallyBounded :
    PolynomiallyBounded (fun length ↦ traceExtentRegisterCost length length length length) :=
  traceExtentRegisterCost_polynomiallyBounded PolynomiallyBounded.id PolynomiallyBounded.id
    PolynomiallyBounded.id PolynomiallyBounded.id

private theorem parsedHeaderCounts_le (request : BinaryWord) :
    (requestHeaderProgress request).arity + (requestHeaderProgress request).cap ≤
      request.length := by
  let first := unaryWindowResult request
  let used := first.1 + first.2.toNat
  let rest := request.drop used
  have hFirst : used ≤ request.length := unaryWindowResult_consumed_le request
  have hRest := unaryWindowResult_consumed_le rest
  change (unaryWindowResult rest).1 + (unaryWindowResult rest).2.toNat ≤
    (request.drop used).length at hRest
  rw [List.length_drop] at hRest
  change first.1 + (unaryWindowResult rest).1 ≤ request.length
  dsimp only [used] at hFirst hRest
  omega

/-- Four extent inputs can reuse the measured registers directly. -/
structure TraceExtentLink {R : Type} (headers : TraceHeaderLane → R)
    (extents : TraceExtentLane → R) : Prop where
  arity : extents .arity = headers (.header .arity)
  cap : extents .cap = headers (.header .cap)
  bodyLength : extents .bodyLength = headers (.header .remaining)
  candidateLength : extents .candidateLength = headers (.pair .candidateLength)

/-- A successfully measured pair of headers fixes the layout and exact shape check.
The time bound uses the raw input length alone. -/
theorem runsValues_traceExtentRegister_of_headers {R : Type} [DecidableEq R]
    {headers : TraceHeaderLane → R} (extents : TraceExtentLane → R)
    (hExtents : Function.Injective extents) (hLink : TraceExtentLink headers extents)
    {word query cert request candidate : BinaryWord} {initial before : R → Nat}
    (hHeaders : TraceHeaderRegisterResult headers word initial before)
    (hOuter : decodePackedPair word = some (query, cert))
    (hInner : decodePackedPair query = some (request, candidate))
    (hArity : (requestHeaderProgress request).arityValid = true)
    (hCap : (requestHeaderProgress request).capValid = true)
    (hZero : ∀ lane, lane ∉ traceExtentInputLanes → before (extents lane) = 0) :
    ∃ ticks ≤ traceExtentRegisterCost word.length word.length word.length word.length,
      ∃ after : R → Nat, (traceExtentRegister extents).RunsValues word ticks before after ∧
        TraceExtentRegisterResult extents before after ∧
        (after (extents .failures) = 0 ↔ (readMergeRequestFields request).isSome ∧
          candidate.length = mergeWitnessLength (requestHeaderProgress request).arity
            (requestHeaderProgress request).cap) := by
  let p := requestHeaderProgress request
  obtain ⟨_, hMeasured⟩ := hHeaders.headers query cert request candidate hOuter hInner
  have hn : before (extents .arity) = p.arity := by
    rw [hLink.arity]
    exact hMeasured.arity
  have hc : before (extents .cap) = p.cap := by
    rw [hLink.cap]
    exact hMeasured.cap
  have hb : before (extents .bodyLength) = (request.drop p.consumed).length := by
    rw [hLink.bodyLength]
    exact hMeasured.remaining
  have hl : before (extents .candidateLength) = candidate.length := by
    rw [hLink.candidateLength]
    exact (hHeaders.innerLengths query cert request candidate hOuter hInner).2
  have hPacking : word = packedPair (packedPair request candidate) cert := by
    rw [decodePackedPair_eq_some_iff.mp hOuter, decodePackedPair_eq_some_iff.mp hInner]
  have hLimits : request.length ≤ word.length ∧ candidate.length ≤ word.length := by
    rw [hPacking, length_packedPair, length_packedPair]
    omega
  obtain ⟨ticks, hTicks, after, hRun, hResult⟩ :=
    runsValues_traceExtentRegister extents hExtents word before hZero
  have hSum : p.arity + p.cap ≤ request.length := parsedHeaderCounts_le request
  have hBound := traceExtentRegisterCost_le_length
    (show before (extents .arity) ≤ word.length by rw [hn]; omega)
    (show before (extents .cap) ≤ word.length by rw [hc]; omega)
    (show before (extents .bodyLength) ≤ word.length by
      rw [hb, List.length_drop]
      omega)
    (show before (extents .candidateLength) ≤ word.length by rw [hl]; exact hLimits.2)
  refine ⟨ticks, hTicks.trans hBound, after, hRun, hResult, ?_⟩
  rw [hResult.valid, hn, hc, hb, hl, readMergeRequestFields_isSome_iff]
  simp only [p, hArity, hCap, true_and, and_assoc]

/-- The length check and field split use the same measured unary values. -/
theorem readMergeRequestFields_header_progress {request : BinaryWord} {fields : MergeRequestFields}
    (hFields : readMergeRequestFields request = some fields) :
    let p := requestHeaderProgress request
    p.arity = fields.arity ∧ p.cap = fields.cap ∧ request.drop p.consumed = fields.body := by
  have hWord := (readMergeRequestFields_eq_some_iff.mp hFields).2
  have hParse : (do
      let (arity, rest) ← readUnaryField request
      let (cap, suffix) ← readUnaryField rest
      pure (arity, cap, suffix)) = some (fields.arity, fields.cap, fields.body) := by
    rw [hWord]
    simp [MergeRequestFields.word, readUnaryField_append]
  have hProgress := (readUnaryFields_iff_requestHeaderProgress request fields.body
    fields.arity fields.cap).mp hParse
  simpa only [Prod.mk.injEq] using hProgress.2.2

/-- The suffix length returned by the extent calculation is the split prefix length. -/
theorem TraceExtentRegisterResult.prefixLength_of_fields {R : Type} {lanes : TraceExtentLane → R}
    {before after : R → Nat} (hResult : TraceExtentRegisterResult lanes before after)
    {request : BinaryWord} {fields : MergeRequestFields}
    (hFields : readMergeRequestFields request = some fields)
    (hArity : before (lanes .arity) = (requestHeaderProgress request).arity)
    (hCap : before (lanes .cap) = (requestHeaderProgress request).cap)
    (hLength : before (lanes .bodyLength) =
      (request.drop (requestHeaderProgress request).consumed).length) :
    after (lanes .prefixLength) = fields.pref.length := by
  obtain ⟨hn, hc, hb⟩ := readMergeRequestFields_header_progress hFields
  have hFit := (readMergeRequestFields_eq_some_iff.mp hFields).1
  rw [hResult.prefixLength, hArity, hCap, hLength, hn, hc, hb]
  simp only [MergeRequestFields.body, mergeRequestBodyMinLength, hFit.counter, hFit.oldCode,
    List.length_append, List.length_cons]
  omega

/-- From the measured header cursor and prefix length, initialize the ordinary
addresses for both packed descriptions and the logical start of the prefix. -/
theorem runsValues_traceQueryBaseRegister_of_fields {R : Type} [DecidableEq R]
    (lanes : TraceQueryBaseLane → R) (hLanes : Function.Injective lanes)
    {request : BinaryWord} {fields : MergeRequestFields}
    (hFields : readMergeRequestFields request = some fields) (candidate cert : BinaryWord)
    (before : R → Nat)
    (hArity : before (lanes .arity) = fields.arity)
    (hHead : before (lanes .header) = 3 + 4 * (requestHeaderProgress request).consumed)
    (hRequest : before (lanes .requestLength) = request.length)
    (hPrefix : before (lanes .prefixLength) = fields.pref.length)
    (hZero : ∀ lane, lane ≠ .arity → lane ≠ .header → lane ≠ .requestLength →
      lane ≠ .prefixLength → before (lanes lane) = 0) :
    let word := packedPair (packedPair request candidate) cert
    ∃ after : R → Nat, (traceQueryBaseRegister lanes).RunsValues word
      (traceQueryBaseRegisterCost (before (lanes .arity)) (before (lanes .header))
        (before (lanes .requestLength)) (before (lanes .prefixLength))) before after ∧
      TraceQueryBaseRegisterResult lanes before after ∧
      after (lanes .oldBase) = 4 * fields.oldStart + 3 ∧
      after (lanes .candidateBase) = 4 * (request.length + 1) + 3 ∧
      after (lanes .prefixStart) = fields.prefStart := by
  let word := packedPair (packedPair request candidate) cert
  obtain ⟨after, hRun, hResult⟩ :=
    runsValues_traceQueryBaseRegister lanes hLanes word before hZero
  obtain ⟨hn, hc, _⟩ := readMergeRequestFields_header_progress hFields
  have hFlags := (readMergeRequestFields_isSome_iff request).mp (by simp [hFields])
  obtain ⟨hFlagArity, hFlagCap, _, _⟩ := hFlags
  obtain ⟨hFit, hWord⟩ := readMergeRequestFields_eq_some_iff.mp hFields
  refine ⟨after, hRun, hResult, ?_, ?_, ?_⟩
  · rw [hResult.oldBase, hHead, hArity]
    simp only [RequestHeaderProgress.consumed, hFlagArity, hFlagCap, Bool.toNat_true,
      hn, hc, MergeRequestFields.oldStart, MergeRequestFields.counterStart]
    omega
  · rw [hResult.candidateBase, hRequest]
    omega
  · rw [hResult.prefixStart, hRequest, hPrefix, hWord]
    simp only [MergeRequestFields.word, MergeRequestFields.body, MergeRequestFields.prefStart,
      MergeRequestFields.oldStart, MergeRequestFields.counterStart, unaryField, hFit.counter,
      List.length_append, List.length_cons, List.length_nil, List.length_replicate]
    omega

end PvsNP.MCSP
