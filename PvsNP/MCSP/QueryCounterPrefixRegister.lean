module

public import PvsNP.MCSP.PreparedPrefixRegister
public import PvsNP.MCSP.PreparedSeenRegister

/-! # Check the counter range and required prefix of a packed query -/

public section

namespace PvsNP.MCSP

open RegisterMachine RegisterMachine.Fragment

/-- Persistent inputs and results, with shared workspace for both checks. -/
inductive QueryCounterPrefixLane where
  | inputLength | counterStart | requestLength | requestPrefixStart | arity | prefixLength
  | high | lowerOnes | order
  | leftPosition | rightPosition | remaining
  | ordinaryBase | unitWidth | widthCopy | address | multiplier | scratch
  deriving DecidableEq

private def querySeenOffsetLane : ReverseWindowLane → QueryCounterPrefixLane
  | .inputLength => .inputLength
  | .base => .counterStart
  | .width => .unitWidth
  | .position => .leftPosition
  | .widthCopy => .widthCopy
  | .address => .address
  | .multiplier => .multiplier
  | .scratch => .scratch

private def querySeenLane : PreparedSeenLane → QueryCounterPrefixLane
  | .offset lane => querySeenOffsetLane lane
  | .arity => .arity
  | .high => .high
  | .lowerOnes => .lowerOnes

private theorem querySeenLane_injective : Function.Injective querySeenLane := by
  intro a b h
  cases a with
  | offset a =>
    cases b with
    | offset b => cases a <;> cases b <;> simp_all [querySeenLane, querySeenOffsetLane]
    | arity | high | lowerOnes => cases a <;> simp_all [querySeenLane, querySeenOffsetLane]
  | arity | high | lowerOnes =>
    cases b with
    | offset b => cases b <;> simp_all [querySeenLane, querySeenOffsetLane]
    | arity | high | lowerOnes => simp_all [querySeenLane]

private def queryPrefixLane : PreparedPrefixLane → QueryCounterPrefixLane
  | .inputLength => .inputLength
  | .requestPrefixStart => .requestPrefixStart
  | .requestLength => .requestLength
  | .prefixLength => .prefixLength
  | .leftPosition => .leftPosition
  | .rightPosition => .rightPosition
  | .remaining => .remaining
  | .order => .order
  | .ordinaryBase => .ordinaryBase
  | .unitWidth => .unitWidth
  | .widthCopy => .widthCopy
  | .address => .address
  | .multiplier => .multiplier
  | .scratch => .scratch

private theorem queryPrefixLane_injective : Function.Injective queryPrefixLane := by
  intro a b h
  cases a <;> cases b <;> simp_all [queryPrefixLane]

variable {R : Type}

/-- Check the counter first and reuse its cleared workspace for the prefix. -/
def queryCounterPrefixRegister (lanes : QueryCounterPrefixLane → R) : Fragment R :=
  (preparedSeenRegister (lanes ∘ querySeenLane)).seq
    (preparedPrefixRegister (lanes ∘ queryPrefixLane))

@[expose] def queryCounterPrefixRegisterCost (length counterStart requestLength
    prefixStart arity prefixLength : Nat) : Nat :=
  preparedSeenRegisterCost length counterStart arity +
    preparedPrefixRegisterCost length prefixStart requestLength prefixLength

theorem queryCounterPrefixRegisterCost_polynomiallyBounded
    {length counterStart requestLength prefixStart arity prefixLength : Nat → Nat}
    (hLength : PolynomiallyBounded length) (hCounter : PolynomiallyBounded counterStart)
    (hRequest : PolynomiallyBounded requestLength) (hPrefix : PolynomiallyBounded prefixStart)
    (hArity : PolynomiallyBounded arity) (hWidth : PolynomiallyBounded prefixLength) :
    PolynomiallyBounded (fun n ↦ queryCounterPrefixRegisterCost (length n) (counterStart n)
      (requestLength n) (prefixStart n) (arity n) (prefixLength n)) :=
  (preparedSeenRegisterCost_polynomiallyBounded hLength hCounter hArity).add
    (preparedPrefixRegisterCost_polynomiallyBounded hLength hPrefix hRequest hWidth)

/-- The six seeds describe the packed windows. Every scoped work and result register is empty. -/
structure QueryCounterPrefixReady (lanes : QueryCounterPrefixLane → R)
    (word request : BinaryWord) (fields : MergeRequestFields) (values : R → Nat) : Prop where
  inputLength : values (lanes .inputLength) = word.length
  counterStart : values (lanes .counterStart) = 4 * fields.counterStart + 3
  requestLength : values (lanes .requestLength) = request.length
  requestPrefixStart : values (lanes .requestPrefixStart) = fields.prefStart
  arity : values (lanes .arity) = fields.arity
  prefixLength : values (lanes .prefixLength) = fields.pref.length
  empty : ∀ lane, lane ∉ [.inputLength, .counterStart, .requestLength, .requestPrefixStart,
    .arity, .prefixLength] → values (lanes lane) = 0

/-- The counter can reach the exclusive row bound only with all its low bits zero. -/
@[expose] def queryCounterPrefixPass (lanes : QueryCounterPrefixLane → R)
    (values : R → Nat) : Prop :=
  (values (lanes .high) = 0 ∨ values (lanes .lowerOnes) = 0) ∧ values (lanes .order) = 0

/-- Exact counter values, the two independent answers, and the register frame. -/
structure QueryCounterPrefixResult (lanes : QueryCounterPrefixLane → R)
    (fields : MergeRequestFields) (candidate : BinaryWord) (before after : R → Nat) : Prop where
  highBit : after (lanes .high) = (fields.counter.getLastD false).toNat
  lowerOnes : after (lanes .lowerOnes) = fields.counter.dropLast.count true
  counterInRange : (after (lanes .high) = 0 ∨ after (lanes .lowerOnes) = 0) ↔
    mergeSeenFieldInRange fields.counter = true
  prefixMatches : after (lanes .order) = 0 ↔ candidate.take fields.pref.length = fields.pref
  frame : ∀ r, r ≠ lanes .high → r ≠ lanes .lowerOnes → r ≠ lanes .order → after r = before r

theorem QueryCounterPrefixResult.pass {lanes : QueryCounterPrefixLane → R}
    {fields : MergeRequestFields} {candidate : BinaryWord} {before after : R → Nat}
    (hResult : QueryCounterPrefixResult lanes fields candidate before after) :
    queryCounterPrefixPass lanes after ↔ mergeSeenFieldInRange fields.counter = true ∧
      candidate.take fields.pref.length = fields.pref :=
  and_congr hResult.counterInRange hResult.prefixMatches

variable [DecidableEq R]

/-- The two checks use only the parsed field layout and the bound on prefix length. -/
theorem runsValues_queryCounterPrefixRegister (lanes : QueryCounterPrefixLane → R)
    (hLanes : Function.Injective lanes) {request : BinaryWord} {fields : MergeRequestFields}
    (hFields : readMergeRequestFields request = some fields) (candidate cert : BinaryWord)
    (hCandidate : fields.pref.length ≤ candidate.length) (before : R → Nat)
    (hReady : QueryCounterPrefixReady lanes (packedPair (packedPair request candidate) cert)
      request fields before) :
    let word := packedPair (packedPair request candidate) cert
    ∃ ticks ≤ queryCounterPrefixRegisterCost word.length (4 * fields.counterStart + 3)
      request.length fields.prefStart fields.arity fields.pref.length,
      ∃ after : R → Nat, (queryCounterPrefixRegister lanes).RunsValues word ticks before after ∧
        QueryCounterPrefixResult lanes fields candidate before after := by
  let word := packedPair (packedPair request candidate) cert
  let seenLanes := lanes ∘ querySeenLane
  let prefixLanes := lanes ∘ queryPrefixLane
  have hLane (a b : QueryCounterPrefixLane) : lanes a = lanes b ↔ a = b :=
    ⟨fun h ↦ hLanes h, congrArg lanes⟩
  have hSeenEmpty (lane : PreparedSeenLane) (hLength : lane ≠ .offset .inputLength)
      (hCounter : lane ≠ .offset .base) (hArity : lane ≠ .arity) : before (seenLanes lane) = 0 := by
    apply hReady.empty
    cases lane with
    | offset lane => cases lane <;> simp_all [querySeenLane, querySeenOffsetLane]
    | arity => contradiction
    | high | lowerOnes => simp [querySeenLane]
  obtain ⟨seenTicks, hSeenTime, seen, hSeenRun, hHigh, hLower, hRange, hSeenFrame⟩ :=
    runsValues_preparedSeenRegister seenLanes (hLanes.comp querySeenLane_injective)
      hFields candidate cert before hReady.inputLength hReady.counterStart hReady.arity hSeenEmpty
  have hKeep (lane : PreparedPrefixLane) : seen (prefixLanes lane) = before (prefixLanes lane) :=
    hSeenFrame _ (by cases lane <;> simp [prefixLanes, queryPrefixLane, seenLanes, querySeenLane,
      hLane]) (by cases lane <;> simp [prefixLanes, queryPrefixLane, seenLanes, querySeenLane,
      hLane])
  have hPrefixEmpty (lane : PreparedPrefixLane) (hLength : lane ≠ .inputLength)
      (hStart : lane ≠ .requestPrefixStart) (hRequest : lane ≠ .requestLength)
      (hWidth : lane ≠ .prefixLength) : seen (prefixLanes lane) = 0 := by
    rw [hKeep]
    apply hReady.empty
    cases lane <;> simp_all [queryPrefixLane]
  obtain ⟨prefixTicks, hPrefixTime, order, hPrefixRun, hOrder⟩ :=
    runsValues_preparedPrefixRegister prefixLanes (hLanes.comp queryPrefixLane_injective)
      hFields candidate cert hCandidate seen ((hKeep .inputLength).trans hReady.inputLength)
      ((hKeep .requestPrefixStart).trans hReady.requestPrefixStart)
      ((hKeep .requestLength).trans hReady.requestLength)
      ((hKeep .prefixLength).trans hReady.prefixLength) hPrefixEmpty
  let after := setValue (lanes .order) order seen
  have hAfterHigh : after (lanes .high) = seen (seenLanes .high) :=
    setValue_other (by simp [hLane]) ..
  have hAfterLower : after (lanes .lowerOnes) = seen (seenLanes .lowerOnes) :=
    setValue_other (by simp [hLane]) ..
  have hAfterOrder : after (lanes .order) = order := setValue_same ..
  have hResult : QueryCounterPrefixResult lanes fields candidate before after := by
    refine ⟨hAfterHigh.trans hHigh, hAfterLower.trans hLower, ?_, ?_, ?_⟩
    · simpa only [hAfterHigh, hAfterLower] using hRange
    · simpa only [hAfterOrder] using hOrder
    · intro r hh hl ho
      exact (setValue_other ho order seen).trans (hSeenFrame r hh hl)
  exact ⟨seenTicks + prefixTicks, Nat.add_le_add hSeenTime hPrefixTime, after,
    hSeenRun.seq hPrefixRun, hResult⟩

end PvsNP.MCSP
