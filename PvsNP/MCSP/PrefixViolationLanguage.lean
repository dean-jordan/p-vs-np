module

public import PvsNP.Complexity.Complement
public import PvsNP.Complexity.PackedPairs
public import PvsNP.MCSP.MergeWitness
public import PvsNP.MCSP.Request

/-! # Bounded row violations for merge prefix queries -/

public section

namespace PvsNP.MCSP

/-- A query pairs a canonical request with a candidate of the required padded length. -/
@[expose] def PackedMergePrefixQuery (query : BinaryWord) (r : MergeRequest)
    (candidate : BinaryWord) : Prop :=
  query = packedPair (encodeMergeRequest r) candidate ∧
    candidate.length = mergeWitnessLength r.arity r.cap

/-- A malformed query has the empty row as a counterexample. A well-framed query
has a counterexample exactly when its candidate fails on the specified row. -/
@[expose] def MergePrefixViolation (query row : BinaryWord) : Prop :=
  (row = [] ∧ ¬ ∃ r candidate, PackedMergePrefixQuery query r candidate) ∨
    ∃ (r : MergeRequest) (candidate : BinaryWord) (x : Fin r.arity → Bool),
      PackedMergePrefixQuery query r candidate ∧ row = List.ofFn x ∧
        checkMergePrefixRow r.cap r.old r.seen r.bit r.pref candidate x = false

@[expose] def MergePrefixViolationLanguage : BinaryLanguage :=
  {query | ∃ row, MergePrefixViolation query row}

theorem mergePrefixViolation_row_length_le {query row : BinaryWord}
    (h : MergePrefixViolation query row) : row.length ≤ query.length := by
  rcases h with ⟨rfl, _⟩ | ⟨r, candidate, x, ⟨rfl, _⟩, rfl, _⟩
  · exact Nat.zero_le _
  · have hArity := arity_add_cap_le_length_encodeMergeRequest r
    rw [List.length_ofFn, length_packedPair]
    omega

private theorem packedMergePrefixQuery_unique {query : BinaryWord} {r s : MergeRequest}
    {candidate other : BinaryWord} (h : PackedMergePrefixQuery query r candidate)
    (h' : PackedMergePrefixQuery query s other) : r = s ∧ candidate = other := by
  have hPair : (encodeMergeRequest r, candidate) = (encodeMergeRequest s, other) :=
    packedPair_injective (h.1.symm.trans h'.1)
  have hRequest := congrArg decodeMergeRequest (congrArg Prod.fst hPair)
  simp only [decodeMergeRequest_encodeMergeRequest, Option.some.injEq] at hRequest
  exact ⟨hRequest, congrArg Prod.snd hPair⟩

theorem not_mem_mergePrefixViolationLanguage_iff (query : BinaryWord) :
    query ∉ MergePrefixViolationLanguage ↔
      ∃ (r : MergeRequest) (candidate : BinaryWord), PackedMergePrefixQuery query r candidate ∧
        ∀ x, checkMergePrefixRow r.cap r.old r.seen r.bit r.pref candidate x = true := by
  constructor
  · intro hNoViolation
    classical
    by_cases hQuery : ∃ r candidate, PackedMergePrefixQuery query r candidate
    · obtain ⟨r, candidate, hPacked⟩ := hQuery
      refine ⟨r, candidate, hPacked, fun x ↦ ?_⟩
      cases hCheck : checkMergePrefixRow r.cap r.old r.seen r.bit r.pref candidate x with
      | true => rfl
      | false =>
        exact False.elim (hNoViolation
          ⟨List.ofFn x, Or.inr ⟨r, candidate, x, hPacked, rfl, hCheck⟩⟩)
    · exact False.elim (hNoViolation ⟨[], Or.inl ⟨rfl, hQuery⟩⟩)
  · rintro ⟨r, candidate, hPacked, hAll⟩ ⟨row, hViolation⟩
    rcases hViolation with ⟨_, hMalformed⟩ | ⟨s, other, x, hOther, _, hCheck⟩
    · exact hMalformed ⟨r, candidate, hPacked⟩
    · obtain ⟨rfl, rfl⟩ := packedMergePrefixQuery_unique hPacked hOther
      rw [hAll x] at hCheck
      contradiction

/-- The outer checker accepts a request and candidate when their packed query
has no counterexample. -/
@[expose] def MergePrefixCandidatePasses (request candidate : BinaryWord) : Prop :=
  packedPair request candidate ∉ MergePrefixViolationLanguage

theorem mergePrefixCandidatePasses_iff (request candidate : BinaryWord) :
    MergePrefixCandidatePasses request candidate ↔
      ∃ r, decodeMergeRequest request = some r ∧
        candidate.length = mergeWitnessLength r.arity r.cap ∧
        ∀ x, checkMergePrefixRow r.cap r.old r.seen r.bit r.pref candidate x = true := by
  rw [MergePrefixCandidatePasses, not_mem_mergePrefixViolationLanguage_iff]
  constructor
  · rintro ⟨r, other, ⟨hPacked, hLength⟩, hCheck⟩
    have hPair : (request, candidate) = (encodeMergeRequest r, other) :=
      packedPair_injective hPacked
    simp only [Prod.mk.injEq] at hPair
    obtain ⟨rfl, rfl⟩ := hPair
    exact ⟨r, decodeMergeRequest_encodeMergeRequest r, hLength, hCheck⟩
  · rintro ⟨r, hRequest, hLength, hCheck⟩
    obtain rfl := decodeMergeRequest_eq_some_iff.mp hRequest
    exact ⟨r, candidate, ⟨rfl, hLength⟩, hCheck⟩

theorem packedCheckingLanguage_mergePrefixCandidatePasses_eq :
    packedCheckingLanguage MergePrefixCandidatePasses = MergePrefixViolationLanguageᶜ := by
  ext query
  constructor
  · rintro ⟨request, candidate, rfl, hCheck⟩
    exact hCheck
  · intro hNoViolation
    obtain ⟨r, candidate, ⟨rfl, _⟩, _⟩ :=
      (not_mem_mergePrefixViolationLanguage_iff query).mp hNoViolation
    exact (packedPair_mem_packedCheckingLanguage_iff MergePrefixCandidatePasses _ _).mpr
      hNoViolation

private theorem mergeWitnessLength_le_pow_of_decode {request : BinaryWord} {r : MergeRequest}
    (h : decodeMergeRequest request = some r) :
    mergeWitnessLength r.arity r.cap ≤ request.length ^ 9 := by
  have hLength : 2 ≤ request.length := by
    rw [← decodeMergeRequest_eq_some_iff.mp h, length_encodeMergeRequest]
    omega
  have hScale : request.length + 1 ≤ 2 * request.length := by omega
  have hCoefficient : 44 ≤ request.length ^ 7 :=
    Nat.le_trans (by decide : 44 ≤ 2 ^ 7) (Nat.pow_le_pow_left hLength _)
  calc
    _ ≤ 11 * (request.length + 1) ^ 2 := mergeWitnessLength_le_of_decodeMergeRequest h
    _ ≤ 11 * (2 * request.length) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hScale _)
    _ = 44 * request.length ^ 2 := by rw [Nat.mul_pow, ← Nat.mul_assoc]
    _ ≤ request.length ^ 7 * request.length ^ 2 := Nat.mul_le_mul_right _ hCoefficient
    _ = request.length ^ 9 := by rw [← Nat.pow_add]

theorem mergePrefixLanguage_iff_exists_nonviolation (request : BinaryWord) :
    request ∈ MergePrefixLanguage ↔
      ∃ candidate : BinaryWord,
        candidate.length ≤ request.length ^ 9 ∧ MergePrefixCandidatePasses request candidate := by
  constructor
  · rintro ⟨r, hRequest, hFeasible⟩
    obtain ⟨candidate, hLength, hCheck⟩ :=
      (mergePrefixFeasible_iff_checked_rows r.cap r.old r.seen r.bit r.pref).mp hFeasible
    exact ⟨candidate, hLength.symm ▸ mergeWitnessLength_le_pow_of_decode hRequest,
      (mergePrefixCandidatePasses_iff request candidate).mpr ⟨r, hRequest, hLength, hCheck⟩⟩
  · rintro ⟨candidate, _, hPasses⟩
    obtain ⟨r, hRequest, hLength, hCheck⟩ :=
      (mergePrefixCandidatePasses_iff request candidate).mp hPasses
    exact ⟨r, hRequest, (mergePrefixFeasible_iff_checked_rows r.cap r.old r.seen r.bit r.pref).mpr
      ⟨candidate, hLength, hCheck⟩⟩

/-- Read a canonical request paired with a candidate of the required padded length. -/
def decodeMergePrefixQuery (query : BinaryWord) : Option (MergeRequest × BinaryWord) := do
  let (request, candidate) ← decodePackedPair query
  let r ← decodeMergeRequest request
  if candidate.length = mergeWitnessLength r.arity r.cap then some (r, candidate) else none

theorem decodeMergePrefixQuery_eq_some_iff {query : BinaryWord} {r : MergeRequest}
    {candidate : BinaryWord} :
    decodeMergePrefixQuery query = some (r, candidate) ↔
      PackedMergePrefixQuery query r candidate := by
  constructor
  · intro h
    obtain ⟨⟨request, code⟩, hPacked, hRest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨decoded, hRequest, hRest⟩ := Option.bind_eq_some_iff.mp hRest
    split at hRest
    next hLength =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hRest
      obtain ⟨rfl, rfl⟩ := hRest
      rw [decodePackedPair_eq_some_iff.mp hPacked, ← decodeMergeRequest_eq_some_iff.mp hRequest]
      exact ⟨rfl, hLength⟩
    next => contradiction
  · rintro ⟨rfl, hLength⟩
    have hPacked := decodePackedPair_eq_some_iff.mpr
      (rfl : packedPair (encodeMergeRequest r) candidate = _)
    simp only [decodeMergePrefixQuery, Option.bind_eq_bind, hPacked, Option.bind_some,
      decodeMergeRequest_encodeMergeRequest, hLength, ite_true]

private def rowInput {n : Nat} (row : BinaryWord) (h : row.length = n) (i : Fin n) : Bool :=
  row[i.val]'(h.symm ▸ i.isLt)

private theorem ofFn_rowInput {n : Nat} (row : BinaryWord) (h : row.length = n) :
    List.ofFn (rowInput row h) = row := by
  subst n
  exact List.ofFn_getElem

/-- Check the framing and evaluate a single proposed counterexample row. -/
def checkMergePrefixViolation (query row : BinaryWord) : Bool :=
  match decodeMergePrefixQuery query with
  | none => row.isEmpty
  | some (r, candidate) =>
    if h : row.length = r.arity then
      !checkMergePrefixRow r.cap r.old r.seen r.bit r.pref candidate (rowInput row h)
    else false

theorem checkMergePrefixViolation_eq_true_iff (query row : BinaryWord) :
    checkMergePrefixViolation query row = true ↔ MergePrefixViolation query row := by
  cases hParsed : decodeMergePrefixQuery query with
  | none =>
    have hMalformed : ¬ ∃ r candidate, PackedMergePrefixQuery query r candidate := by
      rintro ⟨r, candidate, hPacked⟩
      rw [decodeMergePrefixQuery_eq_some_iff.mpr hPacked] at hParsed
      contradiction
    simp only [checkMergePrefixViolation, hParsed, List.isEmpty_iff]
    constructor
    · exact fun hEmpty ↦ Or.inl ⟨hEmpty, hMalformed⟩
    · rintro (⟨hEmpty, _⟩ | ⟨r, candidate, _, hPacked, _, _⟩)
      · exact hEmpty
      · exact (hMalformed ⟨r, candidate, hPacked⟩).elim
  | some result =>
    obtain ⟨r, candidate⟩ := result
    have hPacked := decodeMergePrefixQuery_eq_some_iff.mp hParsed
    simp only [checkMergePrefixViolation, hParsed]
    constructor
    · split
      next hLength =>
        intro hCheck
        exact Or.inr ⟨r, candidate, rowInput row hLength, hPacked,
          (ofFn_rowInput row hLength).symm, by simpa only [Bool.not_eq_true'] using hCheck⟩
      next => simp
    · rintro (⟨_, hMalformed⟩ | ⟨s, other, x, hOther, rfl, hCheck⟩)
      · exact (hMalformed ⟨r, candidate, hPacked⟩).elim
      · obtain ⟨rfl, rfl⟩ := packedMergePrefixQuery_unique hPacked hOther
        have hLength : (List.ofFn x).length = r.arity := List.length_ofFn
        have hInput : rowInput (List.ofFn x) hLength = x := by
          funext i
          simp [rowInput]
        simp only [dite_eq_left hLength, hInput, hCheck, Bool.not_false]

/-- Check a packed pair consisting of the inner query and its proposed counterexample row. -/
@[expose] def checkPackedMergePrefixViolation (word : BinaryWord) : Bool :=
  match decodePackedPair word with
  | none => false
  | some (query, row) => checkMergePrefixViolation query row

theorem checkPackedMergePrefixViolation_eq_true_iff (word : BinaryWord) :
    checkPackedMergePrefixViolation word = true ↔
      word ∈ packedCheckingLanguage MergePrefixViolation := by
  cases hParsed : decodePackedPair word with
  | none =>
    simp only [checkPackedMergePrefixViolation, hParsed, Bool.false_eq_true, false_iff]
    rintro ⟨query, row, hPacked, _⟩
    rw [decodePackedPair_eq_some_iff.mpr hPacked] at hParsed
    contradiction
  | some result =>
    obtain ⟨query, row⟩ := result
    have hLanguage : word ∈ packedCheckingLanguage MergePrefixViolation ↔
        MergePrefixViolation query row := by
      rw [decodePackedPair_eq_some_iff.mp hParsed, packedPair_mem_packedCheckingLanguage_iff]
    rw [hLanguage, checkPackedMergePrefixViolation, hParsed, checkMergePrefixViolation_eq_true_iff]

/-- The universal row check is in `P` under the collapse if its violation checker is in `P`. -/
theorem packedCheckingLanguage_mergePrefixCandidatePasses_mem_P_of_p_eq_np
    (hCollapse : P = NP) (hChecker : packedCheckingLanguage MergePrefixViolation ∈ P) :
    packedCheckingLanguage MergePrefixCandidatePasses ∈ P := by
  have hBad : MergePrefixViolationLanguage ∈ NP :=
    mem_NP_of_packedCheckingLanguage_mem_P hChecker 1 (fun query ↦ by
      change (∃ row, MergePrefixViolation query row) ↔ _
      simp only [Nat.pow_one]
      exact ⟨fun ⟨row, h⟩ ↦ ⟨row, mergePrefixViolation_row_length_le h, h⟩,
        fun ⟨row, _, h⟩ ↦ ⟨row, h⟩⟩)
  rw [← hCollapse] at hBad
  rw [packedCheckingLanguage_mergePrefixCandidatePasses_eq]
  exact mem_POver_compl hBad

/-- After the universal row check, the same collapse handles the bounded candidate search. -/
theorem mergePrefixLanguage_mem_P_of_p_eq_np (hCollapse : P = NP)
    (hChecker : packedCheckingLanguage MergePrefixViolation ∈ P) : MergePrefixLanguage ∈ P := by
  rw [hCollapse]
  exact mem_NP_of_packedCheckingLanguage_mem_P
    (packedCheckingLanguage_mergePrefixCandidatePasses_mem_P_of_p_eq_np hCollapse hChecker)
    9 mergePrefixLanguage_iff_exists_nonviolation

end PvsNP.MCSP
