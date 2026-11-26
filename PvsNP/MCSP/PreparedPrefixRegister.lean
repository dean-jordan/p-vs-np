module

public import PvsNP.MCSP.PrefixRegister
public import PvsNP.TuringMachine.Registers.ReverseWindow

/-! # Calculate and compare the packed request and candidate prefix windows -/

public section

namespace PvsNP.MCSP

open RegisterMachine RegisterMachine.Fragment

/-- Numeric inputs, comparison result, and shared position workspace. -/
inductive PreparedPrefixLane where
  | inputLength | requestPrefixStart | requestLength | prefixLength
  | leftPosition | rightPosition | remaining | order
  | ordinaryBase | unitWidth | widthCopy | address | multiplier | scratch
  deriving DecidableEq

variable {R : Type}

private def prefixSourceLane (right : Bool) : PreparedPrefixLane :=
  if right then .requestLength else .requestPrefixStart

private def prefixPositionLane (right : Bool) : PreparedPrefixLane :=
  if right then .rightPosition else .leftPosition

private def prefixBaseBias (right : Bool) : Nat := if right then 7 else 3

private def prefixOffsetLane (right : Bool) : ReverseWindowLane → PreparedPrefixLane
  | .inputLength => .inputLength
  | .base => .ordinaryBase
  | .width => .unitWidth
  | .position => prefixPositionLane right
  | .widthCopy => .widthCopy
  | .address => .address
  | .multiplier => .multiplier
  | .scratch => .scratch

private theorem prefixOffsetLane_injective (right : Bool) :
    Function.Injective (prefixOffsetLane right) := by
  intro a b h
  cases right <;> cases a <;> cases b <;> simp_all [prefixOffsetLane, prefixPositionLane]

private def prefixCompareLane : Fin 6 → PreparedPrefixLane
  | 0 => .leftPosition
  | 1 => .rightPosition
  | 2 => .remaining
  | 3 => .widthCopy
  | 4 => .scratch
  | _ => .order

private theorem prefixCompareLane_injective : Function.Injective prefixCompareLane := by decide

private def clearPrefixLane (lane : R) : Fragment R where
  Label := Unit
  entry := some ()
  code _ := .dec lane none (some ())

private def preparePrefixPosition (lanes : PreparedPrefixLane → R) (right : Bool) : Fragment R :=
  let physical := accumulateAffine (lanes (prefixSourceLane right)) (lanes .ordinaryBase)
    (lanes .multiplier) (lanes .scratch) 4 (prefixBaseBias right)
  (((physical.seq (incrementBy (lanes .unitWidth) 1)).seq
    (reverseWindowRegister 4 (lanes ∘ prefixOffsetLane right))).seq
      (clearPrefixLane (lanes .ordinaryBase))).seq (clearPrefixLane (lanes .unitWidth))

/-- Derive both reverse positions, compare the two prefix windows, and clear the cursors. -/
def preparedPrefixRegister (lanes : PreparedPrefixLane → R) : Fragment R :=
  let width := add (lanes .prefixLength) (lanes .remaining) (lanes .scratch)
  let compare := stridedCompare 4 4 (lanes ∘ prefixCompareLane)
  (((((preparePrefixPosition lanes false).seq (preparePrefixPosition lanes true)).seq width).seq
    compare).seq (clearPrefixLane (lanes .leftPosition))).seq
      (clearPrefixLane (lanes .rightPosition))

@[expose] def preparedPrefixRegisterCost (length start request width : Nat) : Nat :=
  12 * length + 76 * (start + request) + 5 * width + 372 + stridedCompareTime 4 4 length width

theorem preparedPrefixRegisterCost_polynomiallyBounded {length start request width : Nat → Nat}
    (hLength : PolynomiallyBounded length) (hStart : PolynomiallyBounded start)
    (hRequest : PolynomiallyBounded request) (hWidth : PolynomiallyBounded width) :
    PolynomiallyBounded (fun n ↦ preparedPrefixRegisterCost
      (length n) (start n) (request n) (width n)) :=
  (((((PolynomiallyBounded.const 12).mul hLength).add
    ((PolynomiallyBounded.const 76).mul (hStart.add hRequest))).add
    ((PolynomiallyBounded.const 5).mul hWidth)).add (PolynomiallyBounded.const 372)).add
    (stridedCompareTime_polynomiallyBounded 4 4 hLength hWidth)

variable [DecidableEq R]

private theorem runsValues_clearPrefixLane (lane : R) (word : BinaryWord) (v : R → Nat) :
    (clearPrefixLane lane).RunsValues word (v lane + 1) v (setValue lane 0 v) := by
  intro output
  exact run_clear word (program := (clearPrefixLane lane).close) rfl
    (cfg := (clearPrefixLane lane).enter (⟨none, v, none, output⟩ : Config R Unit)) rfl

private theorem runsValues_preparePrefixPosition (lanes : PreparedPrefixLane → R)
    (hLanes : Function.Injective lanes) (right : Bool) (word : BinaryWord) (before : R → Nat)
    (hLength : before (lanes .inputLength) = word.length)
    (hZero : ∀ lane, lane ≠ .inputLength → lane ≠ .requestPrefixStart → lane ≠ .requestLength →
      lane ≠ .prefixLength → lane ≠ prefixPositionLane (!right) → before (lanes lane) = 0) :
    let source := before (lanes (prefixSourceLane right))
    let bias := prefixBaseBias right
    ∃ ticks ≤ 5 * word.length + 76 * source + 15 * bias + 109,
      (preparePrefixPosition lanes right).RunsValues word ticks before
        (setValue (lanes (prefixPositionLane right)) (word.length - 1 - (4 * source + bias))
          before) := by
  let source := before (lanes (prefixSourceLane right))
  let bias := prefixBaseBias right
  let base := 4 * source + bias
  let position := lanes (prefixPositionLane right)
  let offset := lanes ∘ prefixOffsetLane right
  let based := setValue (lanes .ordinaryBase) base before
  let prepared := setValue (lanes .unitWidth) 1 based
  have hLane (a b : PreparedPrefixLane) : lanes a = lanes b ↔ a = b :=
    ⟨fun h ↦ hLanes h, congrArg lanes⟩
  have hBaseZero : before (lanes .ordinaryBase) = 0 := by
    apply hZero <;> cases right <;> simp [prefixPositionLane]
  have hUnitZero : before (lanes .unitWidth) = 0 := by
    apply hZero <;> cases right <;> simp [prefixPositionLane]
  have hMultiplier : before (lanes .multiplier) = 0 := by
    apply hZero <;> cases right <;> simp [prefixPositionLane]
  have hScratch : before (lanes .scratch) = 0 := by
    apply hZero <;> cases right <;> simp [prefixPositionLane]
  have hAffineLanes : [lanes (prefixSourceLane right), lanes .ordinaryBase,
      lanes .multiplier, lanes .scratch].Nodup := by
    have hRoles : [prefixSourceLane right, .ordinaryBase, .multiplier, .scratch].Nodup := by
      cases right <;> decide
    exact hRoles.map hLanes
  have hBase : (accumulateAffine (lanes (prefixSourceLane right)) (lanes .ordinaryBase)
      (lanes .multiplier) (lanes .scratch) 4 bias).RunsValues word (affineTime 4 bias source)
        before based := by
    simpa only [hBaseZero, Nat.zero_add, based, base, source] using
      runsValues_accumulateAffine (lanes (prefixSourceLane right)) (lanes .ordinaryBase)
        (lanes .multiplier) (lanes .scratch) 4 bias word before hAffineLanes hMultiplier hScratch
  have hBasedUnit : based (lanes .unitWidth) = 0 := by
    simp [based, setValue, hLane, hUnitZero]
  have hUnit : (incrementBy (lanes .unitWidth) 1).RunsValues word 1 based prepared := by
    simpa only [hBasedUnit, Nat.zero_add, prepared] using
      runsValues_incrementBy (lanes .unitWidth) 1 word based
  have hOffsetZero (lane : ReverseWindowLane) (hl : lane ≠ .inputLength)
      (hb : lane ≠ .base) (hw : lane ≠ .width) : prepared (offset lane) = 0 := by
    cases lane <;> cases right <;>
      simp_all [prepared, based, offset, prefixOffsetLane, prefixPositionLane, setValue]
  obtain ⟨revTicks, hRevTicks, hReverse⟩ := runsValues_reverseWindowRegister 4 offset
    (hLanes.comp (prefixOffsetLane_injective right)) word prepared hOffsetZero
  have hOffsetLength : prepared (offset .inputLength) = word.length := by
    simp [prepared, based, offset, prefixOffsetLane, setValue, hLane, hLength]
  have hOffsetBase : prepared (offset .base) = base := by
    simp [prepared, based, offset, prefixOffsetLane, setValue, hLane]
  have hOffsetUnit : prepared (offset .width) = 1 := setValue_same ..
  rw [hOffsetLength, hOffsetBase, hOffsetUnit] at hRevTicks hReverse
  have hFormula : reverseWindowStart word.length base 4 1 = word.length - 1 - base := by
    simp [reverseWindowStart]
  rw [hFormula] at hReverse
  let positioned := setValue position (word.length - 1 - base) prepared
  let cleared := setValue (lanes .ordinaryBase) 0 positioned
  have hPosBase : positioned (lanes .ordinaryBase) = base := by
    cases right <;> simp [positioned, prepared, based, position, prefixPositionLane, setValue,
      hLane]
  have hClearedUnit : cleared (lanes .unitWidth) = 1 := by
    cases right <;> simp [cleared, positioned, prepared, position, prefixPositionLane, setValue,
      hLane]
  have hFinal : setValue (lanes .unitWidth) 0 cleared =
      setValue position (word.length - 1 - base) before := by
    funext r
    by_cases hb : r = lanes .ordinaryBase
    · subst r
      cases right <;> simp [cleared, position, prefixPositionLane, setValue, hLane, hBaseZero]
    by_cases hu : r = lanes .unitWidth
    · subst r
      cases right <;> simp [position, prefixPositionLane, setValue, hLane, hUnitZero]
    simp [cleared, positioned, prepared, based, setValue, hb, hu]
  have hClearBase := runsValues_clearPrefixLane (lanes .ordinaryBase) word positioned
  have hClearUnit := runsValues_clearPrefixLane (lanes .unitWidth) word cleared
  rw [hPosBase] at hClearBase
  rw [hClearedUnit, hFinal] at hClearUnit
  have hRun := (((hBase.seq hUnit).seq hReverse).seq hClearBase).seq hClearUnit
  refine ⟨_, ?_, hRun⟩
  change _ ≤ 5 * word.length + 76 * source + 15 * bias + 109
  unfold reverseWindowRegisterCost at hRevTicks
  unfold affineTime
  dsimp only [base] at hRevTicks ⊢
  omega

/-- Calculate both starting positions and compare the exact requested suffix with the
candidate prefix. The result is zero for equality, and all other registers are restored. -/
theorem runsValues_preparedPrefixRegister (lanes : PreparedPrefixLane → R)
    (hLanes : Function.Injective lanes) {request : BinaryWord} {fields : MergeRequestFields}
    (hFields : readMergeRequestFields request = some fields) (candidate cert : BinaryWord)
    (hCandidate : fields.pref.length ≤ candidate.length) (before : R → Nat)
    (hLength : before (lanes .inputLength) =
      (packedPair (packedPair request candidate) cert).length)
    (hStart : before (lanes .requestPrefixStart) = fields.prefStart)
    (hRequest : before (lanes .requestLength) = request.length)
    (hWidth : before (lanes .prefixLength) = fields.pref.length)
    (hZero : ∀ lane, lane ≠ .inputLength → lane ≠ .requestPrefixStart → lane ≠ .requestLength →
      lane ≠ .prefixLength → before (lanes lane) = 0) :
    let word := packedPair (packedPair request candidate) cert
    ∃ ticks ≤ preparedPrefixRegisterCost word.length fields.prefStart request.length
        fields.pref.length,
      ∃ order, (preparedPrefixRegister lanes).RunsValues word ticks before
        (setValue (lanes .order) order before) ∧
        (order = 0 ↔ candidate.take fields.pref.length = fields.pref) := by
  let word := packedPair (packedPair request candidate) cert
  let left := word.length - 1 - (4 * fields.prefStart + 3)
  let right := word.length - 1 - (4 * request.length + 7)
  let positionedLeft := setValue (lanes .leftPosition) left before
  let positioned := setValue (lanes .rightPosition) right positionedLeft
  let seeded := setValue (lanes .remaining) fields.pref.length positioned
  let cmp := lanes ∘ prefixCompareLane
  have hLane (a b : PreparedPrefixLane) : lanes a = lanes b ↔ a = b :=
    ⟨fun h ↦ hLanes h, congrArg lanes⟩
  obtain ⟨leftTicks, hLeftTime, hLeftRun⟩ := runsValues_preparePrefixPosition lanes hLanes
    false word before hLength (fun lane h₁ h₂ h₃ h₄ _ ↦ hZero lane h₁ h₂ h₃ h₄)
  simp only [prefixSourceLane, Bool.false_eq_true, ite_false, prefixPositionLane,
    prefixBaseBias, hStart] at hLeftTime hLeftRun
  have hAtLeftFrame (lane : PreparedPrefixLane) (h : lane ≠ .leftPosition) :
      positionedLeft (lanes lane) = before (lanes lane) := setValue_other (by simpa [hLane]) ..
  obtain ⟨rightTicks, hRightTime, hRightRun⟩ := runsValues_preparePrefixPosition lanes hLanes
    true word positionedLeft ((hAtLeftFrame .inputLength (by decide)).trans hLength)
    (fun lane h₁ h₂ h₃ h₄ h₅ ↦
      (hAtLeftFrame lane h₅).trans (hZero lane h₁ h₂ h₃ h₄))
  have hAtLeftRequest : positionedLeft (lanes .requestLength) = request.length :=
    (hAtLeftFrame _ (by decide)).trans hRequest
  simp only [prefixSourceLane, ite_true, prefixPositionLane, prefixBaseBias, hAtLeftRequest]
    at hRightTime hRightRun
  have hPositionedFrame (lane : PreparedPrefixLane) (hl : lane ≠ .leftPosition)
      (hr : lane ≠ .rightPosition) : positioned (lanes lane) = before (lanes lane) :=
    (setValue_other (by simpa [hLane]) ..).trans (hAtLeftFrame lane hl)
  have hPositionedWidth : positioned (lanes .prefixLength) = fields.pref.length :=
    (hPositionedFrame _ (by decide) (by decide)).trans hWidth
  have hPositionedRemaining : positioned (lanes .remaining) = 0 :=
    (hPositionedFrame _ (by decide) (by decide)).trans (hZero _ (by decide) (by decide)
      (by decide) (by decide))
  have hPositionedScratch : positioned (lanes .scratch) = 0 :=
    (hPositionedFrame _ (by decide) (by decide)).trans (hZero _ (by decide) (by decide)
      (by decide) (by decide))
  have hCopy : (add (lanes .prefixLength) (lanes .remaining) (lanes .scratch)).RunsValues word
      (5 * fields.pref.length + 2) positioned seeded := by
    simpa only [hPositionedWidth, hPositionedRemaining, Nat.zero_add, seeded] using
      runsValues_add (lanes .prefixLength) (lanes .remaining) (lanes .scratch) word positioned
        (by simp [hLane]) (by simp [hLane]) (by simp [hLane]) hPositionedScratch
  have hCl := hZero .widthCopy (by decide) (by decide) (by decide) (by decide)
  have hOrder := hZero .order (by decide) (by decide) (by decide) (by decide)
  have hSeedLeft : seeded (cmp 0) = left := by
    simp [seeded, positioned, positionedLeft, cmp, prefixCompareLane, setValue, hLane]
  have hSeedRight : seeded (cmp 1) = right := by
    simp [seeded, positioned, cmp, prefixCompareLane, setValue, hLane]
  have hSeedWidth : seeded (cmp 2) = fields.pref.length := setValue_same ..
  have hSeedIndex : seeded (cmp 3) = 0 := by
    simpa [seeded, cmp, prefixCompareLane, setValue, hLane, hCl] using
      hPositionedFrame .widthCopy (by decide) (by decide)
  have hSeedScratch : seeded (cmp 4) = 0 := by
    simp [seeded, cmp, prefixCompareLane, setValue, hLane, hPositionedScratch]
  have hSeedOrder : seeded (cmp 5) = 0 := by
    simpa [seeded, cmp, prefixCompareLane, setValue, hLane, hOrder] using
      hPositionedFrame .order (by decide) (by decide)
  obtain ⟨cmpTicks, hCmpTime, compared, hCmpRun, hCmpWidth, hCmpOrder, hCmpLeft, hCmpRight,
      hCmpFrame⟩ := runsValues_packedRequestPrefix cmp (hLanes.comp prefixCompareLane_injective)
    hFields candidate cert hCandidate seeded hSeedLeft (by
      rw [hSeedRight]
      change word.length - 1 - (4 * request.length + 7) =
        word.length - 1 - (4 * (request.length + 1) + 3)
      rw [show 4 * (request.length + 1) + 3 = 4 * request.length + 7 by omega])
    hSeedWidth hSeedIndex hSeedScratch hSeedOrder
  change compared (lanes .remaining) = 0 at hCmpWidth
  change compared (lanes .order) = 0 ↔ _ at hCmpOrder
  have hLeftBound : compared (lanes .leftPosition) ≤ word.length := by
    change compared (lanes .leftPosition) = seeded (cmp 0) - 4 * fields.pref.length at hCmpLeft
    rw [hCmpLeft, hSeedLeft]
    dsimp [left]
    omega
  have hRightBound : compared (lanes .rightPosition) ≤ word.length := by
    change compared (lanes .rightPosition) = seeded (cmp 1) - 4 * fields.pref.length at hCmpRight
    rw [hCmpRight, hSeedRight]
    dsimp [right]
    omega
  let ready := setValue (lanes .leftPosition) 0 compared
  have hReadyRight : ready (lanes .rightPosition) = compared (lanes .rightPosition) :=
    setValue_other (by simp [hLane]) ..
  have hFinal : setValue (lanes .rightPosition) 0 ready =
      setValue (lanes .order) (compared (lanes .order)) before := by
    funext r
    by_cases hl : r = lanes .leftPosition
    · subst r
      simp [ready, setValue, hLane, hZero]
    by_cases hr : r = lanes .rightPosition
    · subst r
      simp [ready, setValue, hLane, hZero]
    by_cases hw : r = lanes .remaining
    · subst r
      simp [ready, setValue, hLane, hZero, hCmpWidth]
    by_cases ho : r = lanes .order
    · subst r
      simp [ready, setValue, hLane]
    have hRead := hCmpFrame r hl hr hw ho
    simp [ready, seeded, positioned, positionedLeft, setValue, hl, hr, hw, ho, hRead]
  have hClearLeft := runsValues_clearPrefixLane (lanes .leftPosition) word compared
  have hClearRight := runsValues_clearPrefixLane (lanes .rightPosition) word ready
  rw [hReadyRight, hFinal] at hClearRight
  have hRun := ((((hLeftRun.seq hRightRun).seq hCopy).seq hCmpRun).seq hClearLeft).seq hClearRight
  refine ⟨_, ?_, compared (lanes .order), hRun, hCmpOrder⟩
  change _ ≤ preparedPrefixRegisterCost word.length fields.prefStart request.length
    fields.pref.length
  change cmpTicks ≤ stridedCompareTime 4 4 word.length fields.pref.length at hCmpTime
  unfold preparedPrefixRegisterCost
  omega

end PvsNP.MCSP
