module

public import PvsNP.Circuits.DescriptionValidation
public import PvsNP.MCSP.RequestHeaderRegister
public import PvsNP.MCSP.RequestShapeRegister
public import PvsNP.MCSP.TraceViolation

import PvsNP.TuringMachine.Registers.BinaryField

/-! # Structural fields of a binary merge request -/

public section

namespace PvsNP.MCSP

open Circuits

/-- Keep the row counter in binary and the old circuit unparsed. -/
structure MergeRequestFields where
  arity : Nat
  cap : Nat
  counter : BinaryWord
  bit : Bool
  oldCode : BinaryWord
  pref : BinaryWord

/-- Conditions on field lengths, independent of the values of the counter and gate fields. -/
structure MergeRequestFields.Fits (fields : MergeRequestFields) : Prop where
  counter : fields.counter.length = fields.arity + 1
  oldCode : fields.oldCode.length = mergeWitnessLength fields.arity (max 1 fields.cap)
  pref : fields.pref.length ≤ mergeWitnessLength fields.arity fields.cap

@[expose] def MergeRequestFields.body (fields : MergeRequestFields) : BinaryWord :=
  fields.counter ++ fields.bit :: (fields.oldCode ++ fields.pref)

@[expose] def MergeRequestFields.word (fields : MergeRequestFields) : BinaryWord :=
  unaryField fields.arity ++ (unaryField fields.cap ++ fields.body)

private def readMergeRequestBody (n cap : Nat) (suffix : BinaryWord) :
    Option MergeRequestFields :=
  let oldWidth := mergeWitnessLength n (max 1 cap)
  match suffix.drop (n + 1) with
  | [] => none
  | bit :: rest =>
    let pref := rest.drop oldWidth
    if oldWidth ≤ rest.length ∧ pref.length ≤ mergeWitnessLength n cap then
      some ⟨n, cap, suffix.take (n + 1), bit, rest.take oldWidth, pref⟩
    else none

private theorem readMergeRequestBody_eq_some_iff {n cap : Nat} {suffix : BinaryWord}
    {fields : MergeRequestFields} :
    readMergeRequestBody n cap suffix = some fields ↔
      fields.arity = n ∧ fields.cap = cap ∧ fields.Fits ∧ suffix = fields.body := by
  constructor
  · intro h
    cases hDrop : suffix.drop (n + 1) with
    | nil => simp [readMergeRequestBody, hDrop] at h
    | cons bit rest =>
      have hFit : n + 1 ≤ suffix.length := by
        have hLength := congrArg List.length hDrop
        simp only [List.length_drop, List.length_cons] at hLength
        omega
      simp only [readMergeRequestBody, hDrop] at h
      split at h
      next hBounds =>
        cases Option.some.inj h
        refine ⟨rfl, rfl, ⟨?_, ?_, hBounds.2⟩, ?_⟩
        · simp [List.length_take, Nat.min_eq_left hFit]
        · simp [List.length_take, Nat.min_eq_left hBounds.1]
        · simp only [MergeRequestFields.body, List.take_append_drop, ← hDrop]
      next => contradiction
  · rintro ⟨hArity, hCap, hFit, rfl⟩
    cases fields with
    | mk arity bound counter bit oldCode pref =>
      change arity = n at hArity
      change bound = cap at hCap
      subst arity bound
      have hOld : oldCode.length = mergeWitnessLength n (max 1 cap) := hFit.oldCode
      have hCounter : counter.length = n + 1 := hFit.counter
      have hPrefix : pref.length ≤ mergeWitnessLength n cap := hFit.pref
      have hBounds : mergeWitnessLength n (max 1 cap) ≤ oldCode.length + pref.length := by omega
      simp only [readMergeRequestBody, MergeRequestFields.body,
        List.drop_left' hCounter, List.take_left' hCounter,
        List.drop_left' hOld, List.take_left' hOld, List.length_append, hBounds, hPrefix,
        and_self, ite_true]

/-- Split the two unary headers and the bounded fields of the rest of the request. -/
def readMergeRequestFields (word : BinaryWord) : Option MergeRequestFields := do
  let (n, rest) ← readUnaryField word
  let (cap, suffix) ← readUnaryField rest
  readMergeRequestBody n cap suffix

/-- The counter, new bit, and old circuit consume a fixed part of the body. -/
@[expose] def mergeRequestBodyMinLength (arity cap : Nat) : Nat :=
  arity + 2 + mergeWitnessLength arity (max 1 cap)

private theorem readMergeRequestBody_isSome_iff (n cap : Nat) (suffix : BinaryWord) :
    (readMergeRequestBody n cap suffix).isSome ↔
      mergeRequestBodyMinLength n cap ≤ suffix.length ∧
      suffix.length ≤ mergeRequestBodyMinLength n cap + mergeWitnessLength n cap := by
  constructor
  · intro h
    obtain ⟨fields, hFields⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨hArity, hCap, hFit, hWord⟩ := readMergeRequestBody_eq_some_iff.mp hFields
    have hLength : suffix.length = mergeRequestBodyMinLength n cap + fields.pref.length := by
      rw [hWord]
      simp only [MergeRequestFields.body, List.length_append, List.length_cons,
        hFit.counter, hFit.oldCode, hArity, hCap, mergeRequestBodyMinLength]
      omega
    have hPref := hFit.pref
    rw [hArity, hCap] at hPref
    rw [hLength]
    exact ⟨Nat.le_add_right .., Nat.add_le_add_left hPref _⟩
  · rintro ⟨hMin, hMax⟩
    unfold mergeRequestBodyMinLength at hMin hMax
    cases hDrop : suffix.drop (n + 1) with
    | nil =>
      have hLen := congrArg List.length hDrop
      simp only [List.length_drop, List.length_nil] at hLen
      omega
    | cons bit rest =>
      let oldLength := mergeWitnessLength n (max 1 cap)
      have hRest := congrArg List.length hDrop
      simp only [List.length_drop, List.length_cons] at hRest
      have hOld : oldLength ≤ rest.length := by change _ + oldLength ≤ _ at hMin; omega
      have hPref : (rest.drop oldLength).length ≤ mergeWitnessLength n cap := by
        rw [List.length_drop]
        change _ ≤ _ + oldLength + _ at hMax
        omega
      simp only [readMergeRequestBody, hDrop, show mergeWitnessLength n (max 1 cap) =
        oldLength from rfl, hOld, hPref, and_self, ite_true, Option.isSome_some]

/-- Test the shape using just the header flags and body length. The bounds can
be computed from the two unary counts before any circuit or counter checks. -/
theorem readMergeRequestFields_isSome_iff (word : BinaryWord) :
    (readMergeRequestFields word).isSome ↔
      let headers := requestHeaderProgress word
      let bodyLength := (word.drop headers.consumed).length
      headers.arityValid = true ∧ headers.capValid = true ∧
        mergeRequestBodyMinLength headers.arity headers.cap ≤ bodyLength ∧
        bodyLength ≤ mergeRequestBodyMinLength headers.arity headers.cap +
          mergeWitnessLength headers.arity headers.cap := by
  let parsed : Option (Nat × Nat × BinaryWord) := do
    let (n, rest) ← readUnaryField word
    let (cap, suffix) ← readUnaryField rest
    pure (n, cap, suffix)
  have hDecomp : readMergeRequestFields word = parsed.bind (fun (n, cap, body) ↦
      readMergeRequestBody n cap body) := by
    simp only [readMergeRequestFields, parsed, Option.bind_eq_bind, Option.bind_assoc,
      Option.pure_def, Option.bind_some]
  have hParsed := readUnaryFields_eq_requestHeaderProgress word
  change parsed = _ at hParsed
  rw [hDecomp, hParsed]
  cases hArity : (requestHeaderProgress word).arityValid <;>
    cases hCap : (requestHeaderProgress word).capValid <;>
    simp [hArity, hCap, readMergeRequestBody_isSome_iff]

/-- With both header terminators present, zero extent failures means the
request splits and the candidate length matches its budget. -/
theorem RequestShapeRegisterResult.valid_iff_request_fields {R : Type}
    {lanes : RequestShapeLane → R} {before after : R → Nat}
    (hResult : RequestShapeRegisterResult lanes before after) (request candidate : BinaryWord)
    (hArityValid : (requestHeaderProgress request).arityValid = true)
    (hCapValid : (requestHeaderProgress request).capValid = true)
    (hArity : before (lanes .arity) = (requestHeaderProgress request).arity)
    (hBody : before (lanes .bodyLength) =
      (request.drop (requestHeaderProgress request).consumed).length)
    (hOld : before (lanes .oldLength) = mergeWitnessLength (requestHeaderProgress request).arity
      (max 1 (requestHeaderProgress request).cap))
    (hNew : before (lanes .candidateWidth) =
      mergeWitnessLength (requestHeaderProgress request).arity (requestHeaderProgress request).cap)
    (hCandidate : before (lanes .candidateLength) = candidate.length) :
    after (lanes .failures) = 0 ↔
      (readMergeRequestFields request).isSome ∧ candidate.length =
        mergeWitnessLength (requestHeaderProgress request).arity
          (requestHeaderProgress request).cap := by
  rw [hResult.valid, hResult.maximum, hResult.minimum, hBody, hArity, hOld, hNew, hCandidate,
    readMergeRequestFields_isSome_iff]
  simp only [hArityValid, hCapValid, true_and, mergeRequestBodyMinLength, and_assoc]

theorem readMergeRequestFields_eq_some_iff {word : BinaryWord} {fields : MergeRequestFields} :
    readMergeRequestFields word = some fields ↔ fields.Fits ∧ word = fields.word := by
  constructor
  · intro h
    obtain ⟨⟨n, rest⟩, hArity, hRest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨cap, suffix⟩, hCap, hBody⟩ := Option.bind_eq_some_iff.mp hRest
    obtain ⟨rfl, rfl, hFit, rfl⟩ := readMergeRequestBody_eq_some_iff.mp hBody
    rw [readUnaryField_eq_some_iff.mp hArity, readUnaryField_eq_some_iff.mp hCap]
    exact ⟨hFit, rfl⟩
  · rintro ⟨hFit, rfl⟩
    simp only [readMergeRequestFields, MergeRequestFields.word, readUnaryField_append,
      Option.bind_eq_bind, Option.bind_some]
    exact readMergeRequestBody_eq_some_iff.mpr ⟨rfl, rfl, hFit, rfl⟩

/-- The canonical fields of a fully decoded request. -/
@[expose] def MergeRequest.fields (r : MergeRequest) : MergeRequestFields where
  arity := r.arity
  cap := r.cap
  counter := fieldBits (r.arity + 1) r.seen
  bit := r.bit
  oldCode := encodeMergeWitness (max 1 r.cap) r.old
  pref := r.pref

theorem MergeRequest.fields_fits (r : MergeRequest) : r.fields.Fits :=
  ⟨length_fieldBits .., length_encodeMergeWitness _ _ r.old_size_le, r.pref_length_le⟩

theorem MergeRequest.fields_word (r : MergeRequest) : r.fields.word = encodeMergeRequest r := rfl

theorem decodeMergeRequest_eq_some_iff_readFields {word : BinaryWord} {r : MergeRequest} :
    decodeMergeRequest word = some r ↔ readMergeRequestFields word = some r.fields := by
  rw [decodeMergeRequest_eq_some_iff, readMergeRequestFields_eq_some_iff, r.fields_word]
  exact ⟨fun h ↦ ⟨r.fields_fits, h.symm⟩, fun h ↦ h.2.symm⟩

theorem fieldValue_eq_iff_of_length {left right : BinaryWord}
    (hLength : left.length = right.length) :
    fieldValue left = fieldValue right ↔ left = right := by
  constructor
  · intro hValue
    calc
      left = fieldBits left.length (fieldValue left) := (fieldBits_length_fieldValue left).symm
      _ = fieldBits right.length (fieldValue right) := by rw [hValue, hLength]
      _ = right := fieldBits_length_fieldValue right
  · exact congrArg fieldValue

private theorem fieldValue_eq_zero_iff (bits : BinaryWord) :
    fieldValue bits = 0 ↔ bits.all (!·) = true := by
  induction bits with
  | nil => simp [fieldValue]
  | cons b bits ih =>
    cases b <;> simp [fieldValue, ← ih, Nat.mul_eq_zero]

/-- A counter of width `arity + 1` is valid when its most significant bit is
clear, or when that bit is set and every less significant bit is zero. -/
@[expose] def mergeSeenFieldInRange (bits : BinaryWord) : Bool :=
  match bits.getLast? with
  | none => false
  | some high => !high || bits.dropLast.all (!·)

theorem mergeSeenFieldInRange_append (low : BinaryWord) (high : Bool) :
    mergeSeenFieldInRange (low ++ [high]) = (!high || low.all (!·)) := by
  simp [mergeSeenFieldInRange]

theorem mergeSeenFieldInRange_eq_true_iff {bits : BinaryWord} {arity : Nat}
    (hLength : bits.length = arity + 1) :
    mergeSeenFieldInRange bits = true ↔ fieldValue bits ≤ 2 ^ arity := by
  have hNonempty : bits ≠ [] := by rintro rfl; simp at hLength
  have hLowLength : bits.dropLast.length = arity := by rw [List.length_dropLast, hLength]; omega
  have hBound := RegisterMachine.Fragment.fieldValue_lt_pow_length bits.dropLast
  rw [hLowLength] at hBound
  have hSplit := List.dropLast_concat_getLast hNonempty
  calc
    mergeSeenFieldInRange bits = true ↔
        mergeSeenFieldInRange (bits.dropLast ++ [bits.getLast hNonempty]) = true := by rw [hSplit]
    _ ↔ fieldValue (bits.dropLast ++ [bits.getLast hNonempty]) ≤ 2 ^ arity := by
      rw [mergeSeenFieldInRange_append, fieldValue_append_bit, hLowLength]
      cases bits.getLast hNonempty
      · simp [hBound.le]
      · simp only [Bool.not_true, Bool.false_or, Bool.toNat_true, Nat.mul_one,
          ← fieldValue_eq_zero_iff]
        omega
    _ ↔ fieldValue bits ≤ 2 ^ arity := by rw [hSplit]

/-- Recover the exact request from bounded fields and a canonical old circuit. -/
theorem readMergeRequestFields_decodes {word : BinaryWord} {fields : MergeRequestFields}
    (hFields : readMergeRequestFields word = some fields)
    (hCounter : mergeSeenFieldInRange fields.counter = true) {old : BooleanCircuit fields.arity}
    (hSize : old.size ≤ max 1 fields.cap)
    (hOld : fields.oldCode = encodeMergeWitness (max 1 fields.cap) old) :
    ∃ r, decodeMergeRequest word = some r ∧ r.fields = fields := by
  obtain ⟨hFit, _⟩ := readMergeRequestFields_eq_some_iff.mp hFields
  let r : MergeRequest := ⟨fields.arity, fields.cap, old, fieldValue fields.counter, fields.bit,
    fields.pref, (mergeSeenFieldInRange_eq_true_iff hFit.counter).mp hCounter, hSize, hFit.pref⟩
  have hCounter' : fieldBits (fields.arity + 1) (fieldValue fields.counter) = fields.counter := by
    rw [← hFit.counter, fieldBits_length_fieldValue]
  have hEq : r.fields = fields := by
    dsimp only [r, MergeRequest.fields]
    rw [hCounter', ← hOld]
  exact ⟨r, decodeMergeRequest_eq_some_iff_readFields.mpr (hEq ▸ hFields), hEq⟩

end PvsNP.MCSP
