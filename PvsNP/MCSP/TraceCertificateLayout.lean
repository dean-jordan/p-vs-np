module

public import PvsNP.MCSP.TraceChecker
public import PvsNP.MCSP.TraceLayout

import all PvsNP.MCSP.TraceChecker

/-! # Exact row, wire-trace, and claim fields of a merge certificate -/

public section

namespace PvsNP.MCSP

open Circuits

/-- The old wire trace starts after the row's extra high bit. -/
@[expose] def mergeTraceCertificateOldOffset (n : Nat) : Nat := n + 1

/-- There is one old trace bit per input and old gate. -/
@[expose] def mergeTraceCertificateNewOffset (n oldCount : Nat) : Nat :=
  mergeTraceCertificateOldOffset n + (n + oldCount)

/-- Two output claims follow the new wire trace. -/
@[expose] def mergeTraceCertificateClaimOffset (n oldCount newCount : Nat) : Nat :=
  mergeTraceCertificateNewOffset n oldCount + (n + newCount)

@[expose] def mergeTraceCertificateLength (n oldCount newCount : Nat) : Nat :=
  mergeTraceCertificateClaimOffset n oldCount newCount + 2

/-- The lower row bits in the input-wire order used by the two traces. -/
@[expose] def mergeTraceCertificateInputBits (n : Nat) (cert : BinaryWord) : BinaryWord :=
  (cert.take n).reverse

@[expose] def mergeTraceCertificateRow {n : Nat} (cert : BinaryWord) (i : Fin n) : Bool :=
  ((mergeTraceCertificateInputBits n cert)[i.val]?).getD false

@[expose] def mergeTraceCertificateRowValue (n : Nat) (cert : BinaryWord) : Nat :=
  fieldValue (cert.take (n + 1))

@[expose] def mergeTraceCertificateOldTrace (n oldCount : Nat) (cert : BinaryWord) : BinaryWord :=
  (cert.drop (mergeTraceCertificateOldOffset n)).take (n + oldCount)

@[expose] def mergeTraceCertificateNewTrace (n oldCount newCount : Nat) (cert : BinaryWord) :
    BinaryWord :=
  (cert.drop (mergeTraceCertificateNewOffset n oldCount)).take (n + newCount)

@[expose] def mergeTraceCertificateOldClaim (n oldCount newCount : Nat) (cert : BinaryWord) :
    Option Bool :=
  cert[mergeTraceCertificateClaimOffset n oldCount newCount]?

@[expose] def mergeTraceCertificateNewClaim (n oldCount newCount : Nat) (cert : BinaryWord) :
    Option Bool :=
  cert[mergeTraceCertificateClaimOffset n oldCount newCount + 1]?

/-- Exact framing requires the full two traces and two claims, and a clear row high bit. -/
structure MergeTraceCertificateLayout (n oldCount newCount : Nat) (cert : BinaryWord) : Prop where
  length_eq : cert.length = mergeTraceCertificateLength n oldCount newCount
  high_clear : cert[n]? = some false

/-- Every in-bounds input index reads the reverse-oriented low row bit. -/
theorem mergeTraceCertificateInputBits_getElem? {n oldCount newCount : Nat} {cert : BinaryWord}
    (h : MergeTraceCertificateLayout n oldCount newCount cert) {i : Nat} (hi : i < n) :
    (mergeTraceCertificateInputBits n cert)[i]? = cert[n - 1 - i]? := by
  have hN := (List.getElem?_eq_some_iff.mp h.high_clear).choose
  have hLen : (cert.take n).length = n := List.length_take_of_le hN.le
  have hIdx : i + (n - 1 - i) + 1 = (cert.take n).length := by omega
  rw [mergeTraceCertificateInputBits, List.getElem?_reverse' hIdx,
    List.getElem?_take_of_lt (by omega : n - 1 - i < n)]

/-- Prefix equality is precisely pointwise agreement between input wires and the
low row bits addressed in reverse order. -/
theorem mergeTraceCertificateInputs_iff {n oldCount newCount : Nat} {cert trace : BinaryWord}
    (h : MergeTraceCertificateLayout n oldCount newCount cert) :
    trace.take n = mergeTraceCertificateInputBits n cert ↔
      ∀ i, i < n → (trace)[i]? = cert[n - 1 - i]? := by
  have hN := (List.getElem?_eq_some_iff.mp h.high_clear).choose
  have hLen : (mergeTraceCertificateInputBits n cert).length = n := by
    rw [mergeTraceCertificateInputBits, List.length_reverse, List.length_take_of_le hN.le]
  constructor
  · intro heq i hi
    have hRead := congrArg (fun word : BinaryWord ↦ word[i]?) heq
    simpa only [List.getElem?_take_of_lt hi, mergeTraceCertificateInputBits_getElem? h hi]
      using hRead
  · intro hReads
    apply List.ext_getElem?
    intro i
    by_cases hi : i < n
    · rw [List.getElem?_take_of_lt hi, mergeTraceCertificateInputBits_getElem? h hi]
      exact hReads i hi
    · have hTake := List.length_take_le n trace
      rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- The low field, put into wire order, is exactly the reconstructed row. -/
theorem MergeTraceCertificateLayout.inputBits_eq_ofFn {n oldCount newCount : Nat}
    {cert : BinaryWord} (h : MergeTraceCertificateLayout n oldCount newCount cert) :
    mergeTraceCertificateInputBits n cert = List.ofFn (mergeTraceCertificateRow (n := n) cert) := by
  have hN := (List.getElem?_eq_some_iff.mp h.high_clear).choose
  have hLen : (mergeTraceCertificateInputBits n cert).length = n := by
    rw [mergeTraceCertificateInputBits, List.length_reverse, List.length_take_of_le hN.le]
  apply List.ext_getElem?
  intro i
  by_cases hi : i < n
  · have hIdx : i < (mergeTraceCertificateInputBits n cert).length := by rwa [hLen]
    rw [List.getElem?_ofFn, dite_eq_left hi]
    simp only [mergeTraceCertificateRow, List.getElem?_eq_getElem hIdx, Option.getD_some]
  · rw [List.getElem?_ofFn, dite_eq_right hi, List.getElem?_eq_none (by omega)]

private theorem rowField_of_layout {n oldCount newCount : Nat} {cert : BinaryWord}
    (h : MergeTraceCertificateLayout n oldCount newCount cert) :
    cert.take (n + 1) = mergeRowField (mergeTraceCertificateRow (n := n) cert) := by
  have hIndex := (List.getElem?_eq_some_iff.mp h.high_clear).choose
  have hBit : cert[n] = false := by
    have hClear := h.high_clear
    rwa [List.getElem?_eq_getElem hIndex, Option.some.injEq] at hClear
  have hOfFn := congrArg List.reverse h.inputBits_eq_ofFn
  simp only [mergeTraceCertificateInputBits, List.reverse_reverse] at hOfFn
  rw [List.take_succ_eq_append_getElem hIndex, hBit, hOfFn, mergeRowField]

/-- The numeric row field is the truth-table rank of the reconstructed input. -/
theorem MergeTraceCertificateLayout.rowValue_eq_rank {n oldCount newCount : Nat}
    {cert : BinaryWord} (h : MergeTraceCertificateLayout n oldCount newCount cert) :
    mergeTraceCertificateRowValue n cert = rank (mergeTraceCertificateRow (n := n) cert) := by
  rw [mergeTraceCertificateRowValue, rowField_of_layout h, mergeRowField,
    fieldValue_append_bit, fieldValue_reverse_row, Bool.toNat_false, Nat.mul_zero, Nat.add_zero]

/-- The row and request counter can be compared at their common field width. -/
theorem MergeTraceCertificateLayout.compare_rowCounter {n oldCount newCount : Nat}
    {cert : BinaryWord} (h : MergeTraceCertificateLayout n oldCount newCount cert)
    {seen : Nat} (hSeen : seen ≤ 2 ^ n) :
    compare (mergeTraceCertificateRowValue n cert) (fieldValue (fieldBits (n + 1) seen)) =
      compare (rank (mergeTraceCertificateRow (n := n) cert)) seen := by
  rw [mergeTraceCertificateRowValue, rowField_of_layout h]
  exact compare_mergeRowField _ hSeen

/-- The exact length fixes the two trace slices and the final two claims, so a
well-framed certificate is the canonical encoding of its own fields. -/
theorem MergeTraceCertificateLayout.split {n oldCount newCount : Nat} {cert : BinaryWord}
    (h : MergeTraceCertificateLayout n oldCount newCount cert) :
    let oldTrace := mergeTraceCertificateOldTrace n oldCount cert
    let newTrace := mergeTraceCertificateNewTrace n oldCount newCount cert
    let oldClaim := (mergeTraceCertificateOldClaim n oldCount newCount cert).getD false
    let newClaim := (mergeTraceCertificateNewClaim n oldCount newCount cert).getD false
    cert = encodeMergeTraceCertificate (mergeTraceCertificateRow (n := n) cert)
      oldTrace newTrace oldClaim newClaim ∧
      oldTrace.length = n + oldCount ∧ newTrace.length = n + newCount := by
  intro oldTrace newTrace oldClaim newClaim
  let oldWidth := n + oldCount
  let newWidth := n + newCount
  let start := n + 1
  let body := cert.drop start
  let tail := body.drop oldWidth
  let claims := tail.drop newWidth
  have hTotal : cert.length = start + oldWidth + newWidth + 2 := h.length_eq
  have hTail : tail = cert.drop (mergeTraceCertificateNewOffset n oldCount) := by
    simp only [tail, body, List.drop_drop, mergeTraceCertificateNewOffset,
      mergeTraceCertificateOldOffset, start, oldWidth]
  have hClaims : claims = cert.drop (mergeTraceCertificateClaimOffset n oldCount newCount) := by
    simp only [claims, hTail, List.drop_drop, mergeTraceCertificateClaimOffset, newWidth]
  have hOldLen : oldTrace.length = oldWidth := by
    change (body.take oldWidth).length = oldWidth
    apply List.length_take_of_le
    simp only [body, List.length_drop]
    omega
  have hNewLen : newTrace.length = newWidth := by
    change ((cert.drop (mergeTraceCertificateNewOffset n oldCount)).take newWidth).length = _
    rw [← hTail]
    apply List.length_take_of_le
    simp only [tail, body, List.length_drop]
    omega
  have hClaimsLength : claims.length = 2 := by
    simp only [claims, tail, body, List.length_drop]
    omega
  obtain ⟨a, b, hPair⟩ := List.length_eq_two.mp hClaimsLength
  have hRead (i : Nat) :
      claims[i]? = cert[mergeTraceCertificateClaimOffset n oldCount newCount + i]? := by
    rw [hClaims, List.getElem?_drop]
  have hA : oldClaim = a := by
    have hZero := hRead 0
    simp only [hPair, List.getElem?_cons_zero, Nat.add_zero] at hZero
    simp only [oldClaim, mergeTraceCertificateOldClaim, ← hZero, Option.getD_some]
  have hB : newClaim = b := by
    have hOne := hRead 1
    simp only [hPair, List.getElem?_cons_succ, List.getElem?_cons_zero] at hOne
    simp only [newClaim, mergeTraceCertificateNewClaim, ← hOne, Option.getD_some]
  have hParts : oldTrace ++ (newTrace ++ claims) = body := by
    change body.take oldWidth ++
      ((cert.drop (mergeTraceCertificateNewOffset n oldCount)).take newWidth ++ claims) = body
    rw [← hTail]
    simp only [claims, List.take_append_drop, tail]
  refine ⟨?_, hOldLen, hNewLen⟩
  rw [encodeMergeTraceCertificate, hA, hB, ← hPair, List.append_assoc, List.append_assoc,
    hParts, ← rowField_of_layout h, List.take_append_drop]

/-- An old trace read in the outer packed word agrees with the count-bounded raw slice. -/
theorem getElem?_packedMergeTrace_old_of_slice (query cert : BinaryWord)
    (n oldCount : Nat) {i : Nat} (hi : i < n + oldCount) :
    (packedPair query cert)[mergeOldTraceStart query n + 2 * i]? =
      (mergeTraceCertificateOldTrace n oldCount cert)[i]? := by
  have hIndex : mergeOldTraceStart query n + 2 * i =
      2 * (query.length + 1) + 2 * (mergeTraceCertificateOldOffset n + i) + 1 := by
    unfold mergeOldTraceStart mergeTraceCertificateOldOffset
    omega
  rw [hIndex, getElem?_packedPair_right, mergeTraceCertificateOldTrace,
    List.getElem?_take_of_lt hi, List.getElem?_drop]

/-- A new trace read in the outer packed word agrees with the count-bounded raw slice. -/
theorem getElem?_packedMergeTrace_new_of_slice (query cert : BinaryWord)
    (n oldCount newCount : Nat) {i : Nat} (hi : i < n + newCount) :
    (packedPair query cert)[mergeNewTraceStart query n (n + oldCount) + 2 * i]? =
      (mergeTraceCertificateNewTrace n oldCount newCount cert)[i]? := by
  have hIndex : mergeNewTraceStart query n (n + oldCount) + 2 * i =
      2 * (query.length + 1) + 2 * (mergeTraceCertificateNewOffset n oldCount + i) + 1 := by
    unfold mergeNewTraceStart mergeOldTraceStart
      mergeTraceCertificateNewOffset mergeTraceCertificateOldOffset
    omega
  rw [hIndex, getElem?_packedPair_right, mergeTraceCertificateNewTrace,
    List.getElem?_take_of_lt hi, List.getElem?_drop]

/-- The comparison result selects which two bits can witness a violation. -/
@[expose] def mergeTraceViolationFromOrder (bit oldClaim newClaim : Bool) : Ordering → Bool
  | .lt => newClaim != oldClaim
  | .eq => newClaim != bit
  | .gt => false

/-- The two semantic comparison cases are equivalent to a single order test. -/
theorem mergeTraceViolationFromOrder_compare (row seen : Nat) (bit oldClaim newClaim : Bool) :
    mergeTraceViolationFromOrder bit oldClaim newClaim (compare row seen) =
      ((decide (row < seen) && (newClaim != oldClaim)) ||
        (decide (row = seen) && (newClaim != bit))) := by
  rcases lt_trichotomy row seen with h | rfl | h
  · simp [Nat.compare_eq_lt.mpr h, mergeTraceViolationFromOrder, h, ne_of_lt h]
  · simp [mergeTraceViolationFromOrder]
  · simp [Nat.compare_eq_gt.mpr h, mergeTraceViolationFromOrder, Nat.not_lt.mpr h.le, ne_of_gt h]

/-- The separate conditions checked by the row, gate, and answer branches. -/
structure MergeTraceCertificateChecks (r : MergeRequest) (candidate : BooleanCircuit r.arity)
    (cert : BinaryWord) : Prop where
  layout : MergeTraceCertificateLayout r.arity r.old.size candidate.size cert
  oldInputs : (mergeTraceCertificateOldTrace r.arity r.old.size cert).take r.arity =
    mergeTraceCertificateInputBits r.arity cert
  newInputs : (mergeTraceCertificateNewTrace r.arity r.old.size candidate.size cert).take r.arity =
    mergeTraceCertificateInputBits r.arity cert
  oldGates : checkWireTraceFrom r.arity r.old.network.traceInstructions
    (mergeTraceCertificateOldTrace r.arity r.old.size cert) = true
  newGates : checkWireTraceFrom r.arity candidate.network.traceInstructions
    (mergeTraceCertificateNewTrace r.arity r.old.size candidate.size cert) = true
  oldOutput : (mergeTraceCertificateOldTrace r.arity r.old.size cert)[r.old.output.val]? =
    mergeTraceCertificateOldClaim r.arity r.old.size candidate.size cert
  newOutput : (mergeTraceCertificateNewTrace r.arity r.old.size candidate.size
    cert)[candidate.output.val]? =
    mergeTraceCertificateNewClaim r.arity r.old.size candidate.size cert
  violation : mergeTraceViolationFromOrder r.bit
    ((mergeTraceCertificateOldClaim r.arity r.old.size candidate.size cert).getD false)
    ((mergeTraceCertificateNewClaim r.arity r.old.size candidate.size cert).getD false)
    (compare (mergeTraceCertificateRowValue r.arity cert) r.seen) = true

/-- Exact framing guarantees both separately addressed claims are present. -/
theorem MergeTraceCertificateLayout.claims_present {n oldCount newCount : Nat} {cert : BinaryWord}
    (h : MergeTraceCertificateLayout n oldCount newCount cert) :
    let a := mergeTraceCertificateOldClaim n oldCount newCount cert
    let b := mergeTraceCertificateNewClaim n oldCount newCount cert
    a = some (a.getD false) ∧ b = some (b.getD false) := by
  intro a b
  have hLen : cert.length = mergeTraceCertificateClaimOffset n oldCount newCount + 2 := h.length_eq
  have hA : mergeTraceCertificateClaimOffset n oldCount newCount < cert.length := by omega
  have hB : mergeTraceCertificateClaimOffset n oldCount newCount + 1 < cert.length := by omega
  simp only [a, b, mergeTraceCertificateOldClaim, mergeTraceCertificateNewClaim,
    List.getElem?_eq_getElem hA, List.getElem?_eq_getElem hB, Option.getD_some, and_self]

private theorem checks_of_encoded (r : MergeRequest) (candidate : BooleanCircuit r.arity)
    (x : Fin r.arity → Bool) (oldTrace newTrace : BinaryWord) (oldClaim newClaim : Bool)
    (hCheck : checkMergeTraceViolation r.old r.seen r.bit candidate x oldTrace newTrace
      oldClaim newClaim = true) :
    MergeTraceCertificateChecks r candidate
      (encodeMergeTraceCertificate x oldTrace newTrace oldClaim newClaim) := by
  let cert := encodeMergeTraceCertificate x oldTrace newTrace oldClaim newClaim
  let n := r.arity
  have hLengths := mergeTraceLengths r candidate x oldTrace newTrace oldClaim newClaim hCheck
  have hLen : cert.length = mergeTraceCertificateLength n r.old.size candidate.size := by
    simp only [cert, n, encodeMergeTraceCertificate, List.length_append, length_mergeRowField,
      List.length_cons, List.length_nil, mergeTraceCertificateLength,
      mergeTraceCertificateClaimOffset, mergeTraceCertificateNewOffset,
      mergeTraceCertificateOldOffset, hLengths]
  have hRowLen : (List.ofFn x).reverse.length = n := by simp [n]
  have hLower : cert.take n = (List.ofFn x).reverse := by
    simp only [cert, encodeMergeTraceCertificate, mergeRowField, List.append_assoc,
      List.take_left' hRowLen]
  have hClear : cert[n]? = some false := by
    simp only [cert, encodeMergeTraceCertificate, mergeRowField, List.append_assoc,
      List.getElem?_append_right (Nat.le_of_eq hRowLen), hRowLen, Nat.sub_self,
      List.cons_append, List.getElem?_cons_zero]
  have hFirstDrop : cert.drop (n + 1) = oldTrace ++ (newTrace ++ [oldClaim, newClaim]) := by
    change cert.drop (r.arity + 1) = _
    simp only [cert, encodeMergeTraceCertificate, List.append_assoc,
      List.drop_left' (length_mergeRowField x)]
  have hOld : mergeTraceCertificateOldTrace n r.old.size cert = oldTrace := by
    rw [mergeTraceCertificateOldTrace, mergeTraceCertificateOldOffset, hFirstDrop]
    exact List.take_left' hLengths.1
  have hSecondDrop : cert.drop (mergeTraceCertificateNewOffset n r.old.size) =
      newTrace ++ [oldClaim, newClaim] := by
    rw [mergeTraceCertificateNewOffset, mergeTraceCertificateOldOffset, ← List.drop_drop,
      hFirstDrop]
    exact List.drop_left' hLengths.1
  have hNew : mergeTraceCertificateNewTrace n r.old.size candidate.size cert = newTrace := by
    rw [mergeTraceCertificateNewTrace, hSecondDrop]
    exact List.take_left' hLengths.2
  have hClaims : cert.drop (mergeTraceCertificateClaimOffset n r.old.size candidate.size) =
      [oldClaim, newClaim] := by
    rw [mergeTraceCertificateClaimOffset, ← List.drop_drop, hSecondDrop]
    exact List.drop_left' hLengths.2
  have hA : mergeTraceCertificateOldClaim n r.old.size candidate.size cert = some oldClaim := by
    have hRead := congrArg (fun word : BinaryWord ↦ word[0]?) hClaims
    change (cert.drop (mergeTraceCertificateClaimOffset n r.old.size candidate.size))[0]? =
      [oldClaim, newClaim][0]? at hRead
    rwa [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] at hRead
  have hB : mergeTraceCertificateNewClaim n r.old.size candidate.size cert = some newClaim := by
    have hRead := congrArg (fun word : BinaryWord ↦ word[1]?) hClaims
    change (cert.drop (mergeTraceCertificateClaimOffset n r.old.size candidate.size))[1]? =
      [oldClaim, newClaim][1]? at hRead
    rwa [List.getElem?_drop, List.getElem?_cons_succ, List.getElem?_cons_zero] at hRead
  have hRow : mergeTraceCertificateRow (n := n) cert = x := by
    change rowFromLittleEndian (cert.take n) = x
    rw [hLower, rowFromLittleEndian_ofFn]
  have hLayout : MergeTraceCertificateLayout n r.old.size candidate.size cert := ⟨hLen, hClear⟩
  have hRank := hLayout.rowValue_eq_rank
  rw [hRow] at hRank
  have hInputs : mergeTraceCertificateInputBits n cert = List.ofFn x := by
    rw [hLayout.inputBits_eq_ofFn, hRow]
  simp only [checkMergeTraceViolation, BooleanCircuit.checkWireTrace, Bool.and_eq_true,
    beq_iff_eq] at hCheck
  refine ⟨hLayout, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hOld, hInputs]; exact hCheck.1.1.1
  · rw [hNew, hInputs]; exact hCheck.1.2.1
  · rw [hOld]; exact hCheck.1.1.2.1
  · rw [hNew]; exact hCheck.1.2.2.1
  · rw [hOld, hA]; exact hCheck.1.1.2.2
  · rw [hNew, hB]; exact hCheck.1.2.2.2
  · rw [hRank, hA, hB, Option.getD_some, Option.getD_some, mergeTraceViolationFromOrder_compare]
    exact hCheck.2

/-- On an exactly framed certificate, the raw slices need only the two trace
checks and the ordering condition. -/
theorem checkMergeTraceViolation_eq_true_iff_certificateChecks (r : MergeRequest)
    (candidate : BooleanCircuit r.arity) (cert : BinaryWord)
    (hLayout : MergeTraceCertificateLayout r.arity r.old.size candidate.size cert) :
    let n := r.arity
    let oldCount := r.old.size
    let newCount := candidate.size
    checkMergeTraceViolation r.old r.seen r.bit candidate (mergeTraceCertificateRow cert)
      (mergeTraceCertificateOldTrace n oldCount cert)
      (mergeTraceCertificateNewTrace n oldCount newCount cert)
      ((mergeTraceCertificateOldClaim n oldCount newCount cert).getD false)
      ((mergeTraceCertificateNewClaim n oldCount newCount cert).getD false) = true ↔
      MergeTraceCertificateChecks r candidate cert := by
  intro n oldCount newCount
  constructor
  · intro h
    obtain ⟨hCert, _, _⟩ := hLayout.split
    exact hCert ▸ checks_of_encoded r candidate _ _ _ _ _ h
  · intro h
    obtain ⟨hA, hB⟩ := h.layout.claims_present
    have hInputs := h.layout.inputBits_eq_ofFn
    have hRank := h.layout.rowValue_eq_rank
    simp only [checkMergeTraceViolation, BooleanCircuit.checkWireTrace, Bool.and_eq_true,
      beq_iff_eq]
    refine ⟨⟨⟨h.oldInputs.trans hInputs, h.oldGates, h.oldOutput.trans hA⟩,
      ⟨h.newInputs.trans hInputs, h.newGates, h.newOutput.trans hB⟩⟩, ?_⟩
    have hViolation := h.violation
    rwa [hRank, mergeTraceViolationFromOrder_compare] at hViolation

private theorem checks_iff_exact_fields (r : MergeRequest) (candidate : BooleanCircuit r.arity)
    (cert : BinaryWord) : checkTraceFields r candidate cert = true ↔
      MergeTraceCertificateChecks r candidate cert := by
  rw [checkTraceFields_eq_true_iff]
  constructor
  · rintro ⟨x, oldTrace, newTrace, oldClaim, newClaim, rfl, _, hCheck⟩
    exact checks_of_encoded r candidate x oldTrace newTrace oldClaim newClaim hCheck
  · intro h
    obtain ⟨hCert, hOldLen, hNewLen⟩ := h.layout.split
    refine ⟨_, _, _, _, _, hCert, by omega, ?_⟩
    exact (checkMergeTraceViolation_eq_true_iff_certificateChecks r candidate cert h.layout).mpr h

/-- With a valid canonical query, the packed checker is exactly the local
certificate layout, two trace checks, and final ordering condition. -/
theorem checkPackedMergePrefixTraceViolation_eq_true_iff_certificateChecks
    {query code : BinaryWord} {r : MergeRequest} {candidate : BooleanCircuit r.arity}
    (hValid : ValidMergePrefixTraceQuery query r code candidate) (cert : BinaryWord) :
    checkPackedMergePrefixTraceViolation (packedPair query cert) = true ↔
      MergeTraceCertificateChecks r candidate cert := by
  have hPair : decodePackedPair (packedPair query cert) = some (query, cert) :=
    decodePackedPair_eq_some_iff.mpr rfl
  have hTrace := decodeTraceQuery_eq_some_iff.mpr hValid
  rw [checkPackedMergePrefixTraceViolation, hPair]
  change checkMergePrefixTraceViolation query cert = true ↔ _
  rw [checkMergePrefixTraceViolation, hTrace]
  exact checks_iff_exact_fields r candidate cert

end PvsNP.MCSP
