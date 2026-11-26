module

public import PvsNP.Complexity.UniformBounds
public import PvsNP.MCSP.QueryCounterPrefixRegister
public import PvsNP.MCSP.QueryDescriptionsRegister
public import PvsNP.MCSP.TraceExtentLink
public import PvsNP.MCSP.TraceQueryLayout

/-! # Counted structural validity of the sized trace query -/

public section

namespace PvsNP.MCSP

open Circuits RegisterMachine RegisterMachine.Fragment

variable {R : Type}

/-- The three stages can share a register when it passes an address or an input. -/
structure QueryStructureRegisters (R : Type) where
  bases : TraceQueryBaseLane → R
  counterPrefix : QueryCounterPrefixLane → R
  descriptions : QueryDescriptionsLane → R

/-- The three results of the counter and prefix scan survive both circuit scans. -/
structure QueryStructureWiring (regs : QueryStructureRegisters R) : Prop where
  bases : Function.Injective regs.bases
  counterPrefix : Function.Injective regs.counterPrefix
  descriptions : Function.Injective regs.descriptions
  high : ∀ lane, regs.counterPrefix .high ≠ regs.descriptions lane
  lower : ∀ lane, regs.counterPrefix .lowerOnes ≠ regs.descriptions lane
  order : ∀ lane, regs.counterPrefix .order ≠ regs.descriptions lane

/-- Compute the three addresses, then run all four structural checks. -/
def queryStructureRegister (regs : QueryStructureRegisters R) : Fragment R :=
  (traceQueryBaseRegister regs.bases).seq
    ((queryCounterPrefixRegister regs.counterPrefix).seq
      (queryDescriptionsRegister regs.descriptions))

@[expose] def queryStructurePass (regs : QueryStructureRegisters R) (values : R → Nat) : Prop :=
  values (regs.descriptions .failures) = 0 ∧ queryCounterPrefixPass regs.counterPrefix values

private theorem headerPosition_eq_counterStart {request : BinaryWord} {fields : MergeRequestFields}
    (hFields : readMergeRequestFields request = some fields) :
    3 + 4 * (requestHeaderProgress request).consumed = 4 * fields.counterStart + 3 := by
  obtain ⟨hn, hc, _⟩ := readMergeRequestFields_header_progress hFields
  have hFlags := (readMergeRequestFields_isSome_iff request).mp (by simp [hFields])
  simp only [RequestHeaderProgress.consumed, hFlags.1, hFlags.2.1, Bool.toNat_true,
    hn, hc, MergeRequestFields.counterStart]
  omega

/-- The initialized address values, with the original data and other registers preserved. -/
@[expose] def queryStructureAddressValues [DecidableEq R] (regs : QueryStructureRegisters R)
    (request : BinaryWord) (fields : MergeRequestFields) (before : R → Nat) : R → Nat :=
  setValue (regs.bases .prefixStart) fields.prefStart
    (setValue (regs.bases .candidateBase) (4 * (request.length + 1) + 3)
      (setValue (regs.bases .oldBase) (4 * fields.oldStart + 3) before))

/-- Enter with measured dimensions. The scan seeds use the addresses produced by the first stage. -/
structure QueryStructureReady [DecidableEq R] (regs : QueryStructureRegisters R)
    (word request : BinaryWord) (fields : MergeRequestFields) (values : R → Nat) : Prop where
  baseArity : values (regs.bases .arity) = fields.arity
  baseHeader : values (regs.bases .header) = 4 * fields.counterStart + 3
  baseRequest : values (regs.bases .requestLength) = request.length
  basePrefix : values (regs.bases .prefixLength) = fields.pref.length
  baseZero : ∀ lane, lane ≠ .arity → lane ≠ .header → lane ≠ .requestLength →
    lane ≠ .prefixLength → values (regs.bases lane) = 0
  counterPrefix : QueryCounterPrefixReady regs.counterPrefix word request fields
    (queryStructureAddressValues regs request fields values)
  descriptions : QueryDescriptionsSeed regs.descriptions word (4 * fields.oldStart + 3)
    (4 * (request.length + 1) + 3) fields.arity fields.cap
    (queryStructureAddressValues regs request fields values)
  descriptionZero : ∀ old lane, lane ∉ checkedDescriptionInputLanes →
    queryStructureAddressValues regs request fields values
      (regs.descriptions (queryDescriptionLanes old lane)) = 0
  failuresZero : queryStructureAddressValues regs request fields values
    (regs.descriptions .failures) = 0

/-- The independent numeric arguments in the instruction bound. -/
inductive QueryStructureMeasure where
  | arity | cap | requestLength | prefixLength | counterStart | prefixStart
  | oldBase | candidateBase | oldCount | candidateCount
  deriving DecidableEq

instance instFintypeQueryStructureMeasure : Fintype QueryStructureMeasure where
  elems := {.arity, .cap, .requestLength, .prefixLength, .counterStart, .prefixStart,
    .oldBase, .candidateBase, .oldCount, .candidateCount}
  complete measure := by cases measure <;> simp

@[expose] def queryStructureMeasures (request candidate : BinaryWord)
    (fields : MergeRequestFields) : QueryStructureMeasure → Nat
  | .arity => fields.arity
  | .cap => fields.cap
  | .requestLength => request.length
  | .prefixLength => fields.pref.length
  | .counterStart => 4 * fields.counterStart + 3
  | .prefixStart => fields.prefStart
  | .oldBase => 4 * fields.oldStart + 3
  | .candidateBase => 4 * (request.length + 1) + 3
  | .oldCount => circuitDescriptionCount fields.arity (max 1 fields.cap) fields.oldCode
  | .candidateCount => circuitDescriptionCount fields.arity fields.cap candidate

@[expose] def queryStructureRegisterCost (length : Nat) (m : QueryStructureMeasure → Nat) : Nat :=
  traceQueryBaseRegisterCost (m .arity) (m .counterStart) (m .requestLength) (m .prefixLength) +
    (queryCounterPrefixRegisterCost length (m .counterStart) (m .requestLength)
      (m .prefixStart) (m .arity) (m .prefixLength) +
      queryDescriptionsRegisterCost length (m .oldBase) (m .candidateBase) (m .arity) (m .cap)
        (m .oldCount) (m .candidateCount))

/-- The clock proof does not require the cost functions to be monotone in
the claimed counts or in padding width. -/
theorem exists_queryStructureRegisterClock :
    ∃ clock : Nat → Nat, PolynomiallyBounded clock ∧
      ∀ length m, (∀ k, m k ≤ length) → queryStructureRegisterCost length m ≤ clock length := by
  apply PolynomiallyBounded.exists_uniform _ _ PolynomiallyBounded.id
  intro m hm
  have hAddress := traceQueryBaseRegisterCost_polynomiallyBounded (hm .arity)
    (hm .counterStart) (hm .requestLength) (hm .prefixLength)
  have hCounter := queryCounterPrefixRegisterCost_polynomiallyBounded PolynomiallyBounded.id
    (hm .counterStart) (hm .requestLength) (hm .prefixStart) (hm .arity) (hm .prefixLength)
  have hDescriptions := queryDescriptionsRegisterCost_polynomiallyBounded PolynomiallyBounded.id
    (hm .oldBase) (hm .candidateBase) (hm .arity) (hm .cap) (hm .oldCount) (hm .candidateCount)
  exact hAddress.add (hCounter.add hDescriptions)

private theorem requestLength_eq_prefStart_add {request : BinaryWord} {fields : MergeRequestFields}
    (hFields : readMergeRequestFields request = some fields) :
    request.length = fields.prefStart + fields.pref.length := by
  obtain ⟨hFit, hWord⟩ := readMergeRequestFields_eq_some_iff.mp hFields
  rw [hWord]
  simp only [MergeRequestFields.word, MergeRequestFields.body, MergeRequestFields.prefStart,
    MergeRequestFields.oldStart, MergeRequestFields.counterStart, unaryField, hFit.counter,
    List.length_append, List.length_cons, List.length_nil, List.length_replicate]
  omega

private theorem paddedDescriptionBase_lt_length {word code : BinaryWord}
    {base arity cap : Nat} (hWindow : PaddedDescriptionWindow word code base arity cap) :
    base < word.length := by
  have hPositive : 0 < code.length := by
    rw [hWindow.length, mergeWitnessLength]
    have hWidth : 1 ≤ circuitFieldWidth arity cap := Nat.succ_le_succ (Nat.zero_le _)
    omega
  have hFirst := hWindow.read 0 hPositive
  simp only [Nat.mul_zero, Nat.add_zero, List.getElem?_eq_getElem hPositive] at hFirst
  exact (List.getElem?_eq_some_iff.mp hFirst).choose

/-- All measured inputs to the clock fit in the raw input length, including
claimed counts that will be rejected by a circuit scan. -/
theorem queryStructureMeasures_le_length {request candidate cert : BinaryWord}
    {fields : MergeRequestFields}
    (hFields : readMergeRequestFields request = some fields)
    (hLength : candidate.length = mergeWitnessLength fields.arity fields.cap) :
    ∀ k, queryStructureMeasures request candidate fields k ≤
      (packedPair (packedPair request candidate) cert).length := by
  let word := packedPair (packedPair request candidate) cert
  have hWord : request.length ≤ word.length := by
    simp only [word, length_packedPair]
    omega
  have hRequest := requestLength_eq_prefStart_add hFields
  have hOld := paddedDescriptionWindow_old hFields candidate cert
  have hNew := paddedDescriptionWindow_candidate hFields candidate cert hLength
  have hOldBase := (paddedDescriptionBase_lt_length hOld).le
  have hNewBase := (paddedDescriptionBase_lt_length hNew).le
  intro k
  cases k
  · simp only [queryStructureMeasures]
    unfold MergeRequestFields.prefStart MergeRequestFields.oldStart
      MergeRequestFields.counterStart at hRequest
    omega
  · simp only [queryStructureMeasures]
    unfold MergeRequestFields.prefStart MergeRequestFields.oldStart
      MergeRequestFields.counterStart at hRequest
    omega
  · exact hWord
  · change fields.pref.length ≤ word.length
    omega
  · change 4 * fields.counterStart + 3 ≤ word.length
    change 4 * fields.oldStart + 3 ≤ word.length at hOldBase
    unfold MergeRequestFields.oldStart at hOldBase
    omega
  · change fields.prefStart ≤ word.length
    omega
  · exact hOldBase
  · exact hNewBase
  · exact circuitDescriptionCount_le_wordLength hOld
  · exact circuitDescriptionCount_le_wordLength hNew

variable [DecidableEq R]

/-- Structural validity and both decoded counts for the subsequent certificate checks. -/
structure QueryStructureRegisterResult (regs : QueryStructureRegisters R)
    (request candidate cert : BinaryWord) (fields : MergeRequestFields) (before after : R → Nat) :
    Prop where
  oldCount : after (regs.descriptions (.side true .count)) =
    circuitDescriptionCount fields.arity (max 1 fields.cap) fields.oldCode
  candidateCount : after (regs.descriptions (.side false .count)) =
    circuitDescriptionCount fields.arity fields.cap candidate
  descriptionSeeds : QueryDescriptionsSeed regs.descriptions
    (packedPair (packedPair request candidate) cert) (4 * fields.oldStart + 3)
    (4 * (request.length + 1) + 3) fields.arity fields.cap after
  pass : queryStructurePass regs after ↔ MergeTraceQueryFieldsValid request candidate
  external : ∀ r, (∀ lane, r ≠ regs.bases lane) → (∀ lane, r ≠ regs.counterPrefix lane) →
    (∀ lane, r ≠ regs.descriptions lane) → after r = before r

omit [DecidableEq R] in
private theorem checkedDescriptionSeed_of_unchanged {lanes : CheckedDescriptionLane → R}
    {word : BinaryWord} {start arity cap : Nat} {before after : R → Nat}
    (hSeed : CheckedDescriptionSeed lanes word start arity cap before)
    (hSame : ∀ lane, lane ∈ checkedDescriptionInputLanes →
      after (lanes lane) = before (lanes lane)) :
    CheckedDescriptionSeed lanes word start arity cap after := by
  have keep {lane : CheckedDescriptionLane} (h : lane ∈ checkedDescriptionInputLanes)
      {expected : Nat} (hValue : before (lanes lane) = expected) : after (lanes lane) = expected :=
    (hSame lane h).trans hValue
  constructor <;> apply keep <;> first
    | simp [checkedDescriptionInputLanes]
    | exact hSeed.arityValue
    | exact hSeed.capValue
    | exact hSeed.width
    | exact hSeed.span
    | exact hSeed.paddedLength
    | exact hSeed.inputLength
    | exact hSeed.base

/-- After checking the framing and extents, run the whole structural validator
on the original packed word. No part of the certificate is needed. -/
theorem runsValues_queryStructureRegister (regs : QueryStructureRegisters R)
    (hWiring : QueryStructureWiring regs) {request candidate cert : BinaryWord}
    {fields : MergeRequestFields} (hFields : readMergeRequestFields request = some fields)
    (hLength : candidate.length = mergeWitnessLength fields.arity fields.cap) (before : R → Nat)
    (hReady : QueryStructureReady regs (packedPair (packedPair request candidate) cert)
      request fields before) :
    let word := packedPair (packedPair request candidate) cert
    ∃ ticks ≤ queryStructureRegisterCost word.length
      (queryStructureMeasures request candidate fields),
      ∃ after, (queryStructureRegister regs).RunsValues word ticks before after ∧
        QueryStructureRegisterResult regs request candidate cert fields before after := by
  let word := packedPair (packedPair request candidate) cert
  let bases := regs.bases
  let checks := regs.counterPrefix
  let descriptions := regs.descriptions
  let seeded := queryStructureAddressValues regs request fields before
  have hHeader : before (bases .header) = 3 + 4 * (requestHeaderProgress request).consumed :=
    hReady.baseHeader.trans (headerPosition_eq_counterStart hFields).symm
  obtain ⟨addressed, hAddressRun, hAddress, hOld, hNew, hPrefix⟩ :=
    runsValues_traceQueryBaseRegister_of_fields bases hWiring.bases hFields candidate cert before
      hReady.baseArity hHeader hReady.baseRequest hReady.basePrefix hReady.baseZero
  have hAddressed : addressed = seeded := by
    have distinct (a b : TraceQueryBaseLane) (h : a ≠ b) : bases a ≠ bases b :=
      fun e ↦ h (hWiring.bases e)
    funext r
    by_cases hp : r = bases .prefixStart
    · subst r
      exact hPrefix.trans (setValue_same ..).symm
    by_cases hn : r = bases .candidateBase
    · subst r
      rw [hNew]
      have hne : regs.bases .candidateBase ≠ regs.bases .prefixStart := hp
      simp [seeded, queryStructureAddressValues, bases, setValue, hne]
    by_cases ho : r = bases .oldBase
    · subst r
      rw [hOld]
      have hp' : regs.bases .oldBase ≠ regs.bases .prefixStart := hp
      have hn' : regs.bases .oldBase ≠ regs.bases .candidateBase := hn
      simp [seeded, queryStructureAddressValues, bases, setValue, hp', hn']
    rw [hAddress.frame r ho hn hp]
    change r ≠ regs.bases .prefixStart at hp
    change r ≠ regs.bases .candidateBase at hn
    change r ≠ regs.bases .oldBase at ho
    simp [seeded, queryStructureAddressValues, setValue, ho, hn, hp]
  subst addressed
  have hPrefBound := (readMergeRequestFields_eq_some_iff.mp hFields).1.pref
  rw [← hLength] at hPrefBound
  obtain ⟨counterTicks, hCounterCost, checked, hCounterRun, hCounter⟩ :=
    runsValues_queryCounterPrefixRegister checks hWiring.counterPrefix hFields candidate cert
      hPrefBound seeded hReady.counterPrefix
  have hSame (lane : QueryDescriptionsLane) : checked (descriptions lane) =
      seeded (descriptions lane) :=
    hCounter.frame _ (hWiring.high lane).symm (hWiring.lower lane).symm (hWiring.order lane).symm
  have hDescriptionSeed : QueryDescriptionsSeed descriptions word (4 * fields.oldStart + 3)
      (4 * (request.length + 1) + 3) fields.arity fields.cap checked :=
    ⟨checkedDescriptionSeed_of_unchanged hReady.descriptions.old (fun _ _ ↦ hSame _),
      checkedDescriptionSeed_of_unchanged hReady.descriptions.candidate (fun _ _ ↦ hSame _)⟩
  obtain ⟨descTicks, hDescCost, after, hDescRun, hOldCount, hCandidateCount, hDesc, hDescInputs,
    hDescFrame⟩ := runsValues_queryDescriptionsRegister descriptions hWiring.descriptions hFields
      hLength checked hDescriptionSeed (fun old k hk ↦
        (hSame _).trans (hReady.descriptionZero old k hk))
      ((hSame .failures).trans hReady.failuresZero)
  have hPass : queryCounterPrefixPass checks after ↔ mergeSeenFieldInRange fields.counter = true ∧
      candidate.take fields.pref.length = fields.pref := by
    unfold queryCounterPrefixPass
    rw [hDescFrame _ hWiring.high, hDescFrame _ hWiring.lower, hDescFrame _ hWiring.order]
    exact hCounter.pass
  have hAll : queryStructurePass regs after ↔ MergeTraceQueryFieldsValid request candidate := by
    rw [queryStructurePass, hDesc, hPass, mergeTraceQueryFieldsValid_iff_padded]
    constructor
    · rintro ⟨⟨ho, hn⟩, hs, hp⟩
      exact ⟨fields, hFields, hs, ho, hn, hp⟩
    · rintro ⟨other, hOther, hs, ho, hn, hp⟩
      have hEqual := Option.some.inj (hOther.symm.trans hFields)
      subst other
      exact ⟨⟨ho, hn⟩, hs, hp⟩
  rw [hReady.baseArity, hReady.baseHeader, hReady.baseRequest, hReady.basePrefix] at hAddressRun
  have hSeeds : QueryDescriptionsSeed descriptions word (4 * fields.oldStart + 3)
      (4 * (request.length + 1) + 3) fields.arity fields.cap after :=
    ⟨checkedDescriptionSeed_of_unchanged hDescriptionSeed.old (hDescInputs true),
      checkedDescriptionSeed_of_unchanged hDescriptionSeed.candidate (hDescInputs false)⟩
  refine ⟨_, Nat.add_le_add (Nat.le_refl _) (Nat.add_le_add hCounterCost hDescCost),
    after, hAddressRun.seq (hCounterRun.seq hDescRun), hOldCount, hCandidateCount, hSeeds, hAll, ?_⟩
  intro r hb hc hd
  exact (hDescFrame r hd).trans
    ((hCounter.frame r (hc _) (hc _) (hc _)).trans (hAddress.frame r (hb _) (hb _) (hb _)))

end PvsNP.MCSP
