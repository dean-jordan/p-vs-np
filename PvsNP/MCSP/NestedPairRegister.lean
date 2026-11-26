module

public import PvsNP.TuringMachine.Registers.Affine
public import PvsNP.TuringMachine.Registers.LessThan
public import PvsNP.TuringMachine.Registers.PackedPairWindow

/-! # Register framing for the nested packed trace-checking input -/

public section

namespace PvsNP.MCSP

open RegisterMachine RegisterMachine.Fragment

/-- The result lanes and the scratch lanes used by the nested scanner. -/
inductive NestedPairLane where
  | queryLength | certificateLength | outerValid
  | requestLength | candidateLength | innerValid
  | position | width | lookupIndex | scratch | mode
  deriving DecidableEq

private def comparisonLanes : Fin 5 → NestedPairLane
  | 0 => .innerValid
  | 1 => .outerValid
  | 2 => .position
  | 3 => .lookupIndex
  | _ => .scratch

private theorem comparisonLanes_injective : Function.Injective comparisonLanes := by decide

private def innerWindowLanes : Fin 8 → NestedPairLane
  | 0 => .position
  | 1 => .width
  | 2 => .requestLength
  | 3 => .candidateLength
  | 4 => .innerValid
  | 5 => .lookupIndex
  | 6 => .scratch
  | _ => .mode

private theorem innerWindowLanes_injective : Function.Injective innerWindowLanes := by decide

variable {R : Type}

private def scanNestedInner (lanes : NestedPairLane → R) : Fragment R :=
  ((accumulateAffine (lanes .certificateLength) (lanes .position) (lanes .lookupIndex)
    (lanes .scratch) 2 2).seq (add (lanes .queryLength) (lanes .width) (lanes .scratch))).seq
    (packedPairWindow (lanes ∘ innerWindowLanes) 2)

/-- Read the outer pair. Its left field is scanned in place at stride two if
its framing is valid. The scanner takes all its lanes initially zero. -/
def scanNestedPairRegister (lanes : NestedPairLane → R) : Fragment R :=
  (packedPairScan (lanes .queryLength) (lanes .certificateLength) (lanes .outerValid)).seq
    (ifLess (lanes .innerValid) (lanes .outerValid) (lanes .position) (lanes .lookupIndex)
      (lanes .scratch) (scanNestedInner lanes) skip)

/-- A quadratic instruction bound uniform in the raw input bits. -/
@[expose] def nestedPairRegisterCost (length : Nat) : Nat :=
  packedPairWindowCost length length 2 + 17 * length + 30

theorem nestedPairRegisterCost_polynomiallyBounded : PolynomiallyBounded nestedPairRegisterCost :=
  ((packedPairWindowCost_polynomiallyBounded 2 PolynomiallyBounded.id PolynomiallyBounded.id).add
    ((PolynomiallyBounded.const 17).mul PolynomiallyBounded.id)).add (PolynomiallyBounded.const 30)

/-- Validity flags are exact even for malformed input. The length fields are
specified once their containing pair parses. Lanes outside the scanner are preserved. -/
structure NestedPairRegisterResult (lanes : NestedPairLane → R) (word : BinaryWord)
    (before after : R → Nat) : Prop where
  outerValid : after (lanes .outerValid) = (decodePackedPair word).isSome.toNat
  innerValid : after (lanes .innerValid) =
    ((decodePackedPair word).bind fun pair ↦ decodePackedPair pair.1).isSome.toNat
  outerLengths : ∀ query cert, decodePackedPair word = some (query, cert) →
    after (lanes .queryLength) = query.length ∧ after (lanes .certificateLength) = cert.length
  innerLengths : ∀ query cert request candidate, decodePackedPair word = some (query, cert) →
    decodePackedPair query = some (request, candidate) →
    after (lanes .requestLength) = request.length ∧
      after (lanes .candidateLength) = candidate.length
  position : after (lanes .position) = if (decodePackedPair word).isSome then word.length else 0
  widthZero : after (lanes .width) = 0
  lookupIndexZero : after (lanes .lookupIndex) = 0
  scratchZero : after (lanes .scratch) = 0
  modeZero : after (lanes .mode) = 0
  frame : ∀ r, (∀ lane, r ≠ lanes lane) → after r = before r

variable [DecidableEq R]

private theorem runsValues_scanNestedInner (lanes : NestedPairLane → R)
    (hLanes : Function.Injective lanes) (query cert : BinaryWord) (v : R → Nat)
    (hQuery : v (lanes .queryLength) = query.length)
    (hCert : v (lanes .certificateLength) = cert.length)
    (hOuter : v (lanes .outerValid) = 1)
    (hZero : ∀ k, k ≠ .queryLength → k ≠ .certificateLength → k ≠ .outerValid → v (lanes k) = 0) :
    ∃ (ticks : Nat) (after : R → Nat),
      (scanNestedInner lanes).RunsValues (packedPair query cert) ticks v after ∧
      NestedPairRegisterResult lanes (packedPair query cert) v after ∧
      ticks + (2 * (packedPair query cert).length + 2) + ifEqualTime 0 1 ≤
        nestedPairRegisterCost (packedPair query cert).length := by
  let word := packedPair query cert
  let start := 2 * (cert.length + 1)
  have hDiff {a b : NestedPairLane} (h : a ≠ b) : lanes a ≠ lanes b := fun eq ↦ h (hLanes eq)
  have hLane (a b : NestedPairLane) : lanes a = lanes b ↔ a = b :=
    ⟨fun e ↦ hLanes e, congrArg lanes⟩
  have hPosition := hZero .position (by decide) (by decide) (by decide)
  have hWidth := hZero .width (by decide) (by decide) (by decide)
  have hIndex := hZero .lookupIndex (by decide) (by decide) (by decide)
  have hScratch := hZero .scratch (by decide) (by decide) (by decide)
  have hMode := hZero .mode (by decide) (by decide) (by decide)
  have hNodup :
      [lanes .certificateLength, lanes .position, lanes .lookupIndex, lanes .scratch].Nodup :=
    ((by decide : ([.certificateLength, .position, .lookupIndex, .scratch] :
      List NestedPairLane).Nodup)).map hLanes
  let positioned := setValue (lanes .position) start v
  have hAffine : (accumulateAffine (lanes .certificateLength) (lanes .position) (lanes .lookupIndex)
      (lanes .scratch) 2 2).RunsValues word (affineTime 2 2 cert.length) v positioned := by
    have hRun := runsValues_accumulateAffine (lanes .certificateLength) (lanes .position)
      (lanes .lookupIndex) (lanes .scratch) 2 2 word v hNodup hIndex hScratch
    simpa only [hPosition, hCert, Nat.zero_add, positioned, start, Nat.mul_add, Nat.mul_one]
      using hRun
  have hPosFrame {k : NestedPairLane} (hk : k ≠ .position) : positioned (lanes k) = v (lanes k) :=
    setValue_other (hDiff hk) ..
  let prepared := setValue (lanes .width) query.length positioned
  have hCopy : (add (lanes .queryLength) (lanes .width) (lanes .scratch)).RunsValues word
      (5 * query.length + 2) positioned prepared := by
    have hRun := runsValues_add (lanes .queryLength) (lanes .width) (lanes .scratch) word positioned
      (hDiff (by decide)) (hDiff (by decide)) (hDiff (by decide))
      ((hPosFrame (by decide)).trans hScratch)
    simpa only [hPosFrame (show NestedPairLane.queryLength ≠ .position by decide),
      hPosFrame (show NestedPairLane.width ≠ .position by decide), hQuery, hWidth, Nat.zero_add,
      prepared] using hRun
  have hPreparedFrame {k : NestedPairLane} (hp : k ≠ .position) (hw : k ≠ .width) :
      prepared (lanes k) = v (lanes k) := (setValue_other (hDiff hw) ..).trans (hPosFrame hp)
  have hReadyPos : prepared (lanes .position) = start := by
    simp [prepared, positioned, setValue, hLane]
  obtain ⟨windowTicks, hWindowCost, after, hWindow, hAfterPos, hAfterWidth, hAfterMode,
    hDecoded, hWindowFrame⟩ := runsValues_packedPairWindow (lanes ∘ innerWindowLanes)
      (hLanes.comp innerWindowLanes_injective) 2 word query start prepared hReadyPos
      (setValue_same ..)
      ((hPreparedFrame (by decide) (by decide)).trans hIndex)
      ((hPreparedFrame (by decide) (by decide)).trans hScratch)
      ((hPreparedFrame (by decide) (by decide)).trans hMode)
      (fun _ hi ↦ packedPairWindow_read_left query cert hi)
  simp only [Function.comp_apply, innerWindowLanes] at hDecoded hAfterPos
  have hDecodedOuter : decodePackedPair word = some (query, cert) :=
    decodePackedPair_eq_some_iff.mpr rfl
  have hFrame {r : R} (hPos : r ≠ lanes .position) (hWidth : r ≠ lanes .width)
      (hReq : r ≠ lanes .requestLength) (hCand : r ≠ lanes .candidateLength)
      (hValid : r ≠ lanes .innerValid) (hMode : r ≠ lanes .mode) : after r = v r := by
    exact (hWindowFrame r hPos hWidth hReq hCand hValid hMode).trans
      ((setValue_other hWidth ..).trans (setValue_other hPos ..))
  have hResult : NestedPairRegisterResult lanes word v after := by
    refine ⟨?_, ?_, ?_, ?_, ?_, hAfterWidth, ?_, ?_, hAfterMode, ?_⟩
    · rw [hFrame (r := lanes .outerValid) (by simp [hLane]) (by simp [hLane])
        (by simp [hLane]) (by simp [hLane]) (by simp [hLane]) (by simp [hLane]),
        hOuter, hDecodedOuter]
      rfl
    · rw [hDecodedOuter]
      change after (lanes .innerValid) = (decodePackedPair query).isSome.toNat
      have hBegin : prepared (lanes .innerValid) = 0 :=
        (hPreparedFrame (by decide) (by decide)).trans (hZero _ (by decide) (by decide) (by decide))
      cases hDecodedInner : decodePackedPair query with
      | none =>
        rw [hDecodedInner] at hDecoded
        exact hDecoded.trans hBegin
      | some pair =>
        obtain ⟨req, cand⟩ := pair
        rw [hDecodedInner] at hDecoded
        exact hDecoded.1.trans (congrArg (· + 1) hBegin)
    · intro q c hOuterEq
      rw [hDecodedOuter] at hOuterEq
      cases hOuterEq
      refine ⟨?_, ?_⟩
      · exact (hFrame (r := lanes .queryLength) (by simp [hLane]) (by simp [hLane])
          (by simp [hLane]) (by simp [hLane]) (by simp [hLane]) (by simp [hLane])).trans hQuery
      · exact (hFrame (r := lanes .certificateLength) (by simp [hLane]) (by simp [hLane])
          (by simp [hLane]) (by simp [hLane]) (by simp [hLane]) (by simp [hLane])).trans hCert
    · intro q c req cand hOuterEq hInnerEq
      rw [hDecodedOuter] at hOuterEq
      cases hOuterEq
      rw [hInnerEq] at hDecoded
      have hReq : prepared (lanes .requestLength) = 0 :=
        (hPreparedFrame (by decide) (by decide)).trans (hZero _ (by decide) (by decide) (by decide))
      have hCand : prepared (lanes .candidateLength) = 0 :=
        (hPreparedFrame (by decide) (by decide)).trans (hZero _ (by decide) (by decide) (by decide))
      exact ⟨hDecoded.2.1.trans (by rw [hReq, Nat.zero_add]),
        hDecoded.2.2.trans (by rw [hCand, Nat.zero_add])⟩
    · rw [hDecodedOuter]
      change after (lanes .position) = word.length
      rw [hAfterPos]
      have hWord : word.length = 2 * (query.length + cert.length + 1) := length_packedPair ..
      dsimp [start]
      omega
    · exact (hFrame (r := lanes .lookupIndex) (by simp [hLane]) (by simp [hLane])
        (by simp [hLane]) (by simp [hLane]) (by simp [hLane]) (by simp [hLane])).trans hIndex
    · exact (hFrame (r := lanes .scratch) (by simp [hLane]) (by simp [hLane])
        (by simp [hLane]) (by simp [hLane]) (by simp [hLane]) (by simp [hLane])).trans hScratch
    · intro r hr
      exact hFrame (hr _) (hr _) (hr _) (hr _) (hr _) (hr _)
  let ticks := affineTime 2 2 cert.length + (5 * query.length + 2) + windowTicks
  have hCost :
      ticks + (2 * word.length + 2) + ifEqualTime 0 1 ≤ nestedPairRegisterCost word.length := by
    have hWord : word.length = 2 * (query.length + cert.length + 1) := length_packedPair ..
    have hQueryLe : query.length ≤ word.length := by omega
    have hCost' : packedPairWindowCost word.length query.length 2 ≤
        packedPairWindowCost word.length word.length 2 := by
      unfold packedPairWindowCost
      exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hQueryLe) _
    unfold nestedPairRegisterCost ticks affineTime ifEqualTime
    omega
  exact ⟨ticks, after, (hAffine.seq hCopy).seq hWindow, hResult, hCost⟩

/-- Read the nested framing on every raw input. The flags distinguish malformed
outer input, malformed inner input, and a valid request/candidate/certificate triple. -/
theorem runsValues_scanNestedPairRegister (lanes : NestedPairLane → R)
    (hLanes : Function.Injective lanes) (word : BinaryWord) (before : R → Nat)
    (hZero : ∀ lane, before (lanes lane) = 0) :
    ∃ ticks ≤ nestedPairRegisterCost word.length, ∃ after : R → Nat,
      (scanNestedPairRegister lanes).RunsValues word ticks before after ∧
      NestedPairRegisterResult lanes word before after := by
  have hDiff {a b : NestedPairLane} (h : a ≠ b) : lanes a ≠ lanes b := fun e ↦ h (hLanes e)
  obtain ⟨outerTicks, hOuterCost, mid, hReadOuter, hOuter, hFrame⟩ := runsValues_packedPairScan
    (lanes .queryLength) (lanes .certificateLength) (lanes .outerValid)
    (hDiff (by decide)) (hDiff (by decide)) (hDiff (by decide)) word before
  have hMidZero (k : NestedPairLane) (hq : k ≠ .queryLength) (hc : k ≠ .certificateLength)
      (hv : k ≠ .outerValid) : mid (lanes k) = 0 :=
    (hFrame _ (hDiff hq) (hDiff hc) (hDiff hv)).trans (hZero k)
  have hInitialInner : mid (lanes .innerValid) = 0 := hMidZero _ (by decide) (by decide) (by decide)
  have hPosition : mid (lanes .position) = 0 := hMidZero _ (by decide) (by decide) (by decide)
  have hIndex : mid (lanes .lookupIndex) = 0 := hMidZero _ (by decide) (by decide) (by decide)
  have hScratch : mid (lanes .scratch) = 0 := hMidZero _ (by decide) (by decide) (by decide)
  have link {ticks : Nat} {after : R → Nat}
      (hBranch : (if mid (lanes .innerValid) < mid (lanes .outerValid) then scanNestedInner lanes
        else skip).RunsValues word ticks mid after) :
      (ifLess (lanes .innerValid) (lanes .outerValid) (lanes .position) (lanes .lookupIndex)
        (lanes .scratch) (scanNestedInner lanes) skip).RunsValues word
        (ifEqualTime (mid (lanes .innerValid)) (mid (lanes .outerValid)) + ticks) mid after :=
    runsValues_ifLess (lanes ∘ comparisonLanes) (hLanes.comp comparisonLanes_injective)
      (scanNestedInner lanes) skip word mid hPosition hIndex hScratch hBranch
  cases hDecode : decodePackedPair word with
  | none =>
    rw [hDecode] at hOuter
    have hFlag := hOuter.trans (hZero .outerValid)
    have hBranch : (if mid (lanes .innerValid) < mid (lanes .outerValid) then scanNestedInner lanes
        else skip).RunsValues word 0 mid mid := by
      simpa only [hInitialInner, hFlag, Nat.lt_irrefl, ite_false] using runsValues_skip word mid
    have hCompare := link hBranch
    rw [hInitialInner, hFlag] at hCompare
    refine ⟨outerTicks + (ifEqualTime 0 0 + 0), ?_, mid, hReadOuter.seq hCompare, ?_⟩
    · unfold ifEqualTime nestedPairRegisterCost
      omega
    · exact ⟨by simpa [hDecode] using hFlag, by simpa [hDecode] using hInitialInner,
        by simp [hDecode], by simp [hDecode], by simpa [hDecode] using hPosition,
        hMidZero _ (by decide) (by decide) (by decide), hIndex, hScratch,
        hMidZero _ (by decide) (by decide) (by decide), fun r hr ↦ hFrame r (hr _) (hr _) (hr _)⟩
  | some pair =>
    obtain ⟨query, cert⟩ := pair
    rw [hDecode] at hOuter
    have hFlag : mid (lanes .outerValid) = 1 := by simpa only [hZero, Nat.zero_add] using hOuter.1
    have hQuery : mid (lanes .queryLength) = query.length := by
      simpa only [hZero, Nat.zero_add] using hOuter.2.1
    have hCert : mid (lanes .certificateLength) = cert.length := by
      simpa only [hZero, Nat.zero_add] using hOuter.2.2
    have hWord := decodePackedPair_eq_some_iff.mp hDecode
    obtain ⟨innerTicks, after, hInner, hResult, hCost⟩ :=
      runsValues_scanNestedInner lanes hLanes query cert mid hQuery hCert hFlag hMidZero
    rw [← hWord] at hInner hResult hCost
    have hBranch : (if mid (lanes .innerValid) < mid (lanes .outerValid) then scanNestedInner lanes
        else skip).RunsValues word innerTicks mid after := by
      simpa only [hInitialInner, hFlag, Nat.zero_lt_one, ite_true] using hInner
    have hCompare := link hBranch
    rw [hInitialInner, hFlag] at hCompare
    refine ⟨outerTicks + (ifEqualTime 0 1 + innerTicks), by omega, after,
      hReadOuter.seq hCompare, { hResult with frame := ?_ }⟩
    intro r hr
    exact (hResult.frame r hr).trans (hFrame r (hr _) (hr _) (hr _))

end PvsNP.MCSP
