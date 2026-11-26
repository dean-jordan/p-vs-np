module

public import PvsNP.MCSP.CheckedDescriptionRegister

import all PvsNP.MCSP.CheckedDescriptionRegister

/-! # Validate the two padded descriptions in a packed merge query -/

public section

namespace PvsNP.MCSP

open Circuits RegisterMachine RegisterMachine.Fragment

/-- The two scans share only their read-only arity and input length. The Boolean
side is true for the old description and false for the candidate. -/
inductive QueryDescriptionsLane where
  | arity
  | inputLength
  | side (old : Bool) (lane : CheckedDescriptionLane)
  | failures
  deriving DecidableEq

@[expose] def queryDescriptionLanes (old : Bool) :
    CheckedDescriptionLane → QueryDescriptionsLane
  | .arity => .arity
  | .inputLength => .inputLength
  | lane => .side old lane

theorem queryDescriptionLanes_injective (old : Bool) :
    Function.Injective (queryDescriptionLanes old) := by
  intro a b h
  cases a <;> cases b <;> simp_all [queryDescriptionLanes]

private theorem queryDescriptionLanes_ne {old other : Bool} (hSide : old ≠ other)
    {a : CheckedDescriptionLane} (ha : a ≠ .arity) (hl : a ≠ .inputLength)
    (b : CheckedDescriptionLane) : queryDescriptionLanes old a ≠ queryDescriptionLanes other b := by
  cases a <;> cases b <;> simp_all [queryDescriptionLanes]

private theorem no_queryDescriptionLanes_failures (old : Bool) (lane : CheckedDescriptionLane) :
    QueryDescriptionsLane.failures ≠ queryDescriptionLanes old lane := by
  cases lane <;> simp [queryDescriptionLanes]

variable {R : Type}

/-- Both layouts supplied by the extent and address computations. -/
structure QueryDescriptionsSeed (lanes : QueryDescriptionsLane → R) (word : BinaryWord)
    (oldBase candidateBase arity cap : Nat) (values : R → Nat) : Prop where
  old : CheckedDescriptionSeed (lanes ∘ queryDescriptionLanes true)
    word oldBase arity (max 1 cap) values
  candidate : CheckedDescriptionSeed (lanes ∘ queryDescriptionLanes false)
    word candidateBase arity cap values

/-- Scan both descriptions and record whether either scan reported a failure. -/
def queryDescriptionsRegister (lanes : QueryDescriptionsLane → R) : Fragment R :=
  let old := checkedDescriptionRegister (lanes ∘ queryDescriptionLanes true)
  let candidate := checkedDescriptionRegister (lanes ∘ queryDescriptionLanes false)
  let checkOld := countNonzero (lanes (.side true .failures)) (lanes .failures)
  let checkCandidate := countNonzero (lanes (.side false .failures)) (lanes .failures)
  (old.seq candidate).seq (checkOld.seq checkCandidate)

@[expose] def queryDescriptionsRegisterCost
    (length oldBase candidateBase arity cap oldCount candidateCount : Nat) : Nat :=
  checkedDescriptionRegisterCost length oldBase arity (max 1 cap) oldCount
    (circuitFieldWidth arity (max 1 cap)) (mergeWitnessLength arity (max 1 cap)) +
  checkedDescriptionRegisterCost length candidateBase arity cap candidateCount
    (circuitFieldWidth arity cap) (mergeWitnessLength arity cap) + 6

theorem queryDescriptionsRegisterCost_polynomiallyBounded
    {length oldBase candidateBase arity cap oldCount candidateCount : Nat → Nat}
    (hLength : PolynomiallyBounded length) (hOldBase : PolynomiallyBounded oldBase)
    (hCandidateBase : PolynomiallyBounded candidateBase) (hArity : PolynomiallyBounded arity)
    (hCap : PolynomiallyBounded cap) (hOldCount : PolynomiallyBounded oldCount)
    (hCandidateCount : PolynomiallyBounded candidateCount) :
    PolynomiallyBounded (fun n ↦ queryDescriptionsRegisterCost
      (length n) (oldBase n) (candidateBase n) (arity n) (cap n)
      (oldCount n) (candidateCount n)) := by
  let lit := PolynomiallyBounded.const
  have layoutCost {base budget count : Nat → Nat} (hBase : PolynomiallyBounded base)
      (hBudget : PolynomiallyBounded budget) (hCount : PolynomiallyBounded count) :
      PolynomiallyBounded (fun n ↦ checkedDescriptionRegisterCost (length n) (base n)
        (arity n) (budget n) (count n) (circuitFieldWidth (arity n) (budget n))
        (mergeWitnessLength (arity n) (budget n))) := by
    have hWidth : PolynomiallyBounded (fun n ↦ circuitFieldWidth (arity n) (budget n)) :=
      ((hArity.add hBudget).add (lit 1)).mono fun _ ↦
        Nat.add_le_add_right (Nat.log2_le_self _) 1
    have hPadded : PolynomiallyBounded (fun n ↦ mergeWitnessLength (arity n) (budget n)) :=
      ((lit 2).mul hWidth).add (hBudget.mul ((lit 3).add ((lit 2).mul hWidth)))
    exact checkedDescriptionRegisterCost_polynomiallyBounded hLength hBase hArity
      hBudget hCount hWidth hPadded
  have hOldCap : PolynomiallyBounded (fun n ↦ max 1 (cap n)) :=
    (hCap.add (lit 1)).mono fun _ ↦ Nat.max_le.mpr ⟨by omega, by omega⟩
  exact ((layoutCost hOldBase hOldCap hOldCount).add
    (layoutCost hCandidateBase hCap hCandidateCount)).add (lit 6)

private theorem queryDescriptions_other_frame (lanes : QueryDescriptionsLane → R)
    (hLanes : Function.Injective lanes) {old other : Bool} (hSide : other ≠ old)
    {before after : R → Nat}
    (hInput : ∀ lane ∈ checkedDescriptionInputLanes,
      after (lanes (queryDescriptionLanes old lane)) =
        before (lanes (queryDescriptionLanes old lane)))
    (hFrame : ∀ r, (∀ lane, r ≠ lanes (queryDescriptionLanes old lane)) →
      after r = before r)
    (lane : CheckedDescriptionLane) :
    after (lanes (queryDescriptionLanes other lane)) =
      before (lanes (queryDescriptionLanes other lane)) := by
  by_cases ha : lane = .arity
  · subst lane
    exact hInput .arity (by simp [checkedDescriptionInputLanes])
  by_cases hl : lane = .inputLength
  · subst lane
    exact hInput .inputLength (by simp [checkedDescriptionInputLanes])
  exact hFrame _ (fun k e ↦ queryDescriptionLanes_ne hSide ha hl k (hLanes e))

variable [DecidableEq R]

private theorem runsValues_countQueryDescriptionFailures (lanes : QueryDescriptionsLane → R)
    (hLanes : Function.Injective lanes) (word : BinaryWord) (before : R → Nat)
    (hZero : before (lanes .failures) = 0) :
    let badOld := (decide (before (lanes (.side true .failures)) ≠ 0)).toNat
    let badCandidate := (decide (before (lanes (.side false .failures)) ≠ 0)).toNat
    ∃ ticks ≤ 6,
      ((countNonzero (lanes (.side true .failures)) (lanes .failures)).seq
        (countNonzero (lanes (.side false .failures)) (lanes .failures))).RunsValues word ticks
        before (setValue (lanes .failures) (badOld + badCandidate) before) := by
  let old := lanes (.side true .failures)
  let candidate := lanes (.side false .failures)
  let failures := lanes .failures
  let badOld := (decide (before old ≠ 0)).toNat
  let badCandidate := (decide (before candidate ≠ 0)).toNat
  let mid := setValue failures badOld before
  have hMid : (countNonzero old failures).RunsValues word (1 + 2 * badOld) before mid := by
    simpa only [hZero, Nat.zero_add, old, failures, badOld, mid] using
      runsValues_countNonzero old failures word before
  have hCandidate : mid candidate = before candidate :=
    setValue_other (fun e ↦ by cases hLanes e) ..
  have hEnd : (countNonzero candidate failures).RunsValues word (1 + 2 * badCandidate) mid
      (setValue failures (badOld + badCandidate) before) := by
    simpa only [hCandidate, mid, setValue_same, setValue_replace, badCandidate] using
      runsValues_countNonzero candidate failures word mid
  have small (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide
  have hOld : badOld ≤ 1 := small _
  have hNew : badCandidate ≤ 1 := small _
  exact ⟨_, by omega, hMid.seq hEnd⟩

/-- The prepared packed query yields the two decoded counts. The accumulated
failure register is zero exactly when both padded descriptions are valid. -/
theorem runsValues_queryDescriptionsRegister (lanes : QueryDescriptionsLane → R)
    (hLanes : Function.Injective lanes) {request candidate cert : BinaryWord}
    {fields : MergeRequestFields} (hFields : readMergeRequestFields request = some fields)
    (hLength : candidate.length = mergeWitnessLength fields.arity fields.cap) (before : R → Nat)
    (hSeed : QueryDescriptionsSeed lanes (packedPair (packedPair request candidate) cert)
      (4 * fields.oldStart + 3) (4 * (request.length + 1) + 3) fields.arity fields.cap before)
    (hZero : ∀ old lane, lane ∉ checkedDescriptionInputLanes →
      before (lanes (queryDescriptionLanes old lane)) = 0)
    (hFailures : before (lanes .failures) = 0) :
    let word := packedPair (packedPair request candidate) cert
    let oldCount := circuitDescriptionCount fields.arity (max 1 fields.cap) fields.oldCode
    let candidateCount := circuitDescriptionCount fields.arity fields.cap candidate
    ∃ ticks ≤ queryDescriptionsRegisterCost word.length (4 * fields.oldStart + 3)
        (4 * (request.length + 1) + 3) fields.arity fields.cap oldCount candidateCount,
      ∃ after, (queryDescriptionsRegister lanes).RunsValues word ticks before after ∧
        after (lanes (.side true .count)) = oldCount ∧
        after (lanes (.side false .count)) = candidateCount ∧
        (after (lanes .failures) = 0 ↔
          PaddedCircuitDescriptionValid fields.arity (max 1 fields.cap) fields.oldCode ∧
          PaddedCircuitDescriptionValid fields.arity fields.cap candidate) ∧
        (∀ old lane, lane ∈ checkedDescriptionInputLanes →
          after (lanes (queryDescriptionLanes old lane)) =
            before (lanes (queryDescriptionLanes old lane))) ∧
        ∀ r, (∀ lane, r ≠ lanes lane) → after r = before r := by
  let word := packedPair (packedPair request candidate) cert
  let oldLanes := lanes ∘ queryDescriptionLanes true
  let newLanes := lanes ∘ queryDescriptionLanes false
  have hOldWindow := paddedDescriptionWindow_old hFields candidate cert
  have hNewWindow := paddedDescriptionWindow_candidate hFields candidate cert hLength
  obtain ⟨oldTicks, hOldCost, withOld, hOldRun, hOldCount, hOldValidity, hOldInput, hOldFrame⟩ :=
    runsValues_checkedDescriptionRegister oldLanes
      (hLanes.comp (queryDescriptionLanes_injective true)) hOldWindow before hSeed.old (hZero true)
  have hNewUnchanged (lane : CheckedDescriptionLane) : withOld (newLanes lane) =
      before (newLanes lane) :=
    queryDescriptions_other_frame lanes hLanes (by decide : false ≠ true)
      hOldInput hOldFrame lane
  have hNewSeed : CheckedDescriptionSeed newLanes word (4 * (request.length + 1) + 3)
      fields.arity fields.cap withOld := ⟨
    (hNewUnchanged _).trans hSeed.candidate.arityValue,
    (hNewUnchanged _).trans hSeed.candidate.capValue,
    (hNewUnchanged _).trans hSeed.candidate.width,
    (hNewUnchanged _).trans hSeed.candidate.span,
    (hNewUnchanged _).trans hSeed.candidate.paddedLength,
    (hNewUnchanged _).trans hSeed.candidate.inputLength,
    (hNewUnchanged _).trans hSeed.candidate.base⟩
  obtain ⟨newTicks, hNewCost, both, hNewRun, hNewCount, hNewValidity, hNewInput, hNewFrame⟩ :=
    runsValues_checkedDescriptionRegister newLanes
      (hLanes.comp (queryDescriptionLanes_injective false)) hNewWindow withOld hNewSeed
        (fun lane h ↦ (hNewUnchanged lane).trans (hZero false lane h))
  have hOldUnchanged (lane : CheckedDescriptionLane) : both (oldLanes lane) =
      withOld (oldLanes lane) :=
    queryDescriptions_other_frame lanes hLanes (by decide : true ≠ false)
      hNewInput hNewFrame lane
  have hOutside (r : R) (hOld : ∀ lane, r ≠ oldLanes lane)
      (hNew : ∀ lane, r ≠ newLanes lane) : both r = before r :=
    (hNewFrame r hNew).trans (hOldFrame r hOld)
  have hFailureSide (old : Bool) (lane : CheckedDescriptionLane) :
      lanes .failures ≠ lanes (queryDescriptionLanes old lane) :=
    fun e ↦ no_queryDescriptionLanes_failures old lane (hLanes e)
  have hBothFailures : both (lanes .failures) = 0 :=
    (hOutside _ (hFailureSide true) (hFailureSide false)).trans hFailures
  obtain ⟨endTicks, hEndCost, hEndRun⟩ :=
    runsValues_countQueryDescriptionFailures lanes hLanes word both hBothFailures
  let badOld := (decide (both (oldLanes .failures) ≠ 0)).toNat
  let badNew := (decide (both (newLanes .failures) ≠ 0)).toNat
  let after := setValue (lanes .failures) (badOld + badNew) both
  have hEndFrame (r : R) (h : r ≠ lanes .failures) : after r = both r :=
    setValue_other h ..
  refine ⟨oldTicks + newTicks + endTicks, ?_, after, (hOldRun.seq hNewRun).seq hEndRun,
    ?_, ?_, ?_, ?_, ?_⟩
  · unfold queryDescriptionsRegisterCost
    rw [hOldWindow.length] at hOldCost
    rw [hLength] at hNewCost
    exact Nat.add_le_add (Nat.add_le_add hOldCost hNewCost) hEndCost
  · exact (hEndFrame _ (hFailureSide true .count).symm).trans
      ((hOldUnchanged .count).trans hOldCount)
  · exact (hEndFrame _ (hFailureSide false .count).symm).trans hNewCount
  · rw [show after (lanes .failures) = badOld + badNew from setValue_same ..]
    simp [badOld, badNew, Nat.add_eq_zero_iff, hOldUnchanged .failures, hOldValidity, hNewValidity]
  · intro old lane hl
    rw [hEndFrame _ (hFailureSide old lane).symm]
    cases old
    · exact (hNewInput lane hl).trans (hNewUnchanged lane)
    · exact (hOldUnchanged lane).trans (hOldInput lane hl)
  · intro r h
    exact (hEndFrame r (h .failures)).trans (hOutside r (fun lane ↦ h _) (fun lane ↦ h _))

end PvsNP.MCSP
