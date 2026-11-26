module

public import PvsNP.MCSP.TraceHeaderRegister
public import PvsNP.MCSP.TraceChecker

import PvsNP.CookLevin.Generator.AcceptingBlock
import PvsNP.MCSP.RequestLayout

/-! # Resolve framing and unary-header failures in the trace verifier -/

public section

namespace PvsNP.MCSP

open RegisterMachine RegisterMachine.Fragment

variable {R : Type}

private abbrev testHeaderLane (lanes : TraceHeaderLane → R) (lane : TraceHeaderLane)
    (positive zero : Fragment R) : Fragment R :=
  ifLess (lanes .zero) (lanes lane) (lanes .leftCopy) (lanes .rightCopy) (lanes .scratch)
    positive zero

/-- Emit true exactly when the scanned certificate length is zero. -/
def emitEmptyCertificate (lanes : TraceHeaderLane → R) : Fragment R :=
  testHeaderLane lanes (.pair .certificateLength) (emitBit false) (emitBit true)

/-- Dispatch using the scanner's flags. Only the successful framing and header path
enters the next checker stage. -/
def traceHeaderDispatch (lanes : TraceHeaderLane → R) (continuation : Fragment R) : Fragment R :=
  let malformed := emitEmptyCertificate lanes
  let cap := testHeaderLane lanes (.header .capValid) continuation malformed
  let arity := testHeaderLane lanes (.header .arityValid) cap malformed
  let inner := testHeaderLane lanes (.pair .innerValid) arity malformed
  testHeaderLane lanes (.pair .outerValid) inner (emitBit false)

@[expose] def traceHeaderDispatchCost (length bound : Nat) : Nat := bound + 6 * length + 55

theorem traceHeaderDispatchCost_polynomiallyBounded {length bound : Nat → Nat}
    (hLength : PolynomiallyBounded length) (hBound : PolynomiallyBounded bound) :
    PolynomiallyBounded (fun n ↦ traceHeaderDispatchCost (length n) (bound n)) :=
  (hBound.add ((PolynomiallyBounded.const 6).mul hLength)).add (PolynomiallyBounded.const 55)

variable [DecidableEq R]

/-- The continuation must compute the checker result when both packed frames and both
unary headers have been read successfully. -/
@[expose] def TraceHeaderContinuation (continuation : Fragment R) (word : BinaryWord)
    (initialized : R → Nat) (suffix : BinaryWord) (bound : Nat) : Prop :=
  ∀ query cert request candidate,
    decodePackedPair word = some (query, cert) →
    decodePackedPair query = some (request, candidate) →
    (requestHeaderProgress request).arityValid = true →
    (requestHeaderProgress request).capValid = true →
    ∃ ticks ≤ bound, ∃ after,
      continuation.RunsOutput word ticks initialized after suffix
        (checkPackedMergePrefixTraceViolation word :: suffix)

private theorem runsOutput_testHeaderLane (lanes : TraceHeaderLane → R)
    (hLanes : Function.Injective lanes) (lane : TraceHeaderLane)
    (hLane : lane ≠ .leftCopy ∧ lane ≠ .rightCopy ∧ lane ≠ .scratch)
    (word : BinaryWord) (before : R → Nat) (suffix output : BinaryWord)
    (positive zero : Fragment R) (limit bound : Nat)
    (hZero : before (lanes .zero) = 0)
    (hScratch : before (lanes .leftCopy) = 0 ∧ before (lanes .rightCopy) = 0 ∧
      before (lanes .scratch) = 0) (hLimit : before (lanes lane) ≤ limit)
    (hPositive : 0 < before (lanes lane) → ∃ ticks ≤ bound, ∃ after,
      positive.RunsOutput word ticks before after suffix output)
    (hAbsent : ¬ 0 < before (lanes lane) → ∃ ticks ≤ bound, ∃ after,
      zero.RunsOutput word ticks before after suffix output) :
    ∃ ticks ≤ bound + 6 * limit + 6, ∃ after,
      (testHeaderLane lanes lane positive zero).RunsOutput word ticks before after suffix
        output := by
  have hLeft := List.Nodup.map hLanes
    (show ([.zero, .leftCopy, .rightCopy, .scratch] : List TraceHeaderLane).Nodup by simp)
  have hRight := List.Nodup.map hLanes
    (show ([lane, .leftCopy, .rightCopy, .scratch] : List TraceHeaderLane).Nodup by
      simp [hLane])
  have hSelect (after : R → Nat)
      (hPos : 0 < before (lanes lane) → ∃ ticks ≤ bound,
        positive.RunsOutput word ticks before after suffix output)
      (hNo : ¬ 0 < before (lanes lane) → ∃ ticks ≤ bound,
        zero.RunsOutput word ticks before after suffix output) :
      ∃ ticks ≤ bound + 6 * limit + 6,
        (testHeaderLane lanes lane positive zero).RunsOutput word ticks before after suffix
          output := by
    obtain ⟨ticks, hTicks, hRun⟩ := runsOutput_ifLess word before after suffix output bound
      hLeft hRight hScratch.1 hScratch.2.1 hScratch.2.2
      (by simpa only [hZero] using hPos) (by simpa only [hZero] using hNo)
    rw [hZero, ifEqualTime] at hTicks
    exact ⟨ticks, by omega, hRun⟩
  by_cases hPos : 0 < before (lanes lane)
  · obtain ⟨ticks, hTicks, after, hRun⟩ := hPositive hPos
    obtain ⟨total, hTotal, hRun⟩ := hSelect after (fun _ ↦ ⟨ticks, hTicks, hRun⟩)
      (fun hFalse ↦ (hFalse hPos).elim)
    exact ⟨total, hTotal, after, hRun⟩
  · obtain ⟨ticks, hTicks, after, hRun⟩ := hAbsent hPos
    obtain ⟨total, hTotal, hRun⟩ := hSelect after (fun hTrue ↦ (hPos hTrue).elim)
      (fun _ ↦ ⟨ticks, hTicks, hRun⟩)
    exact ⟨total, hTotal, after, hRun⟩

private theorem runsOutput_dispatchBit (word : BinaryWord) (before : R → Nat)
    (suffix : BinaryWord) (bit : Bool) :
    (emitBit bit).RunsOutput word 1 before before suffix (bit :: suffix) :=
  run_emitBit bit word (⟨none, before, none, suffix⟩ : Config R Unit) rfl

theorem checker_of_invalid_query {word query cert : BinaryWord}
    (hOuter : decodePackedPair word = some (query, cert))
    (hInvalid : ¬ ∃ r code c, ValidMergePrefixTraceQuery query r code c) :
    checkPackedMergePrefixTraceViolation word = cert.isEmpty := by
  apply Bool.eq_iff_iff.mpr
  rw [checkPackedMergePrefixTraceViolation_eq_true_iff, decodePackedPair_eq_some_iff.mp hOuter,
    packedPair_mem_packedCheckingLanguage_iff, List.isEmpty_iff]
  constructor
  · rintro (⟨hEmpty, _⟩ | ⟨r, code, c, _, _, _, _, _, hValid, _⟩)
    · exact hEmpty
    · exact (hInvalid ⟨r, code, c, hValid⟩).elim
  · exact fun hEmpty ↦ Or.inl ⟨hEmpty, hInvalid⟩

private theorem invalidQuery_of_missing_inner {query : BinaryWord}
    (hInner : decodePackedPair query = none) :
    ¬ ∃ r code c, ValidMergePrefixTraceQuery query r code c := by
  rintro ⟨r, code, c, hValid⟩
  have hDecoded := decodePackedPair_eq_some_iff.mpr hValid.packed.1
  rw [hInner] at hDecoded
  contradiction

private theorem invalidQuery_of_bad_header {query request candidate : BinaryWord}
    (hInner : decodePackedPair query = some (request, candidate))
    (hFlags : ¬ ((requestHeaderProgress request).arityValid = true ∧
      (requestHeaderProgress request).capValid = true)) :
    ¬ ∃ r code c, ValidMergePrefixTraceQuery query r code c := by
  rintro ⟨r, code, c, hValid⟩
  have hDecoded := decodePackedPair_eq_some_iff.mpr hValid.packed.1
  rw [hInner, Option.some.injEq, Prod.mk.injEq] at hDecoded
  have hRequest := decodeMergeRequest_eq_some_iff_readFields.mp
    (decodeMergeRequest_eq_some_iff.mpr hDecoded.1.symm)
  have hFits := (readMergeRequestFields_isSome_iff request).mp (by simp [hRequest])
  exact hFlags ⟨hFits.1, hFits.2.1⟩

theorem runsOutput_emitEmptyCertificate_of_count (lanes : TraceHeaderLane → R)
    (hLanes : Function.Injective lanes) {word query cert : BinaryWord}
    {initialized : R → Nat}
    (hCert : initialized (lanes (.pair .certificateLength)) = cert.length)
    (hZero : initialized (lanes .zero) = 0)
    (hScratch : initialized (lanes .leftCopy) = 0 ∧ initialized (lanes .rightCopy) = 0 ∧
      initialized (lanes .scratch) = 0)
    (hOuter : decodePackedPair word = some (query, cert))
    (hInvalid : ¬ ∃ r code c, ValidMergePrefixTraceQuery query r code c) (suffix : BinaryWord) :
    ∃ ticks ≤ 6 * word.length + 7, ∃ after,
      (emitEmptyCertificate lanes).RunsOutput word ticks initialized after suffix
        (checkPackedMergePrefixTraceViolation word :: suffix) := by
  have hLimit : initialized (lanes (.pair .certificateLength)) ≤ word.length := by
    rw [hCert, decodePackedPair_eq_some_iff.mp hOuter, length_packedPair]
    omega
  have hCheck := checker_of_invalid_query hOuter hInvalid
  obtain ⟨ticks, hTicks, after, hRun⟩ := runsOutput_testHeaderLane lanes hLanes
    (.pair .certificateLength) (by simp) word initialized suffix
    (checkPackedMergePrefixTraceViolation word :: suffix) (emitBit false) (emitBit true)
    word.length 1 hZero hScratch hLimit (by
      rw [hCert, hCheck]
      cases cert with
      | nil => simp
      | cons b rest =>
        exact fun _ ↦ ⟨1, Nat.le_refl _, initialized, runsOutput_dispatchBit word _ suffix false⟩)
    (by
      rw [hCert, hCheck]
      cases cert with
      | nil =>
        exact fun _ ↦ ⟨1, Nat.le_refl _, initialized, runsOutput_dispatchBit word _ suffix true⟩
      | cons b rest => simp)
  exact ⟨ticks, by omega, after, hRun⟩

theorem runsOutput_emitEmptyCertificate (lanes : TraceHeaderLane → R)
    (hLanes : Function.Injective lanes) {word query cert : BinaryWord}
    {before initialized : R → Nat}
    (hHeader : TraceHeaderRegisterResult lanes word before initialized)
    (hOuter : decodePackedPair word = some (query, cert))
    (hInvalid : ¬ ∃ r code c, ValidMergePrefixTraceQuery query r code c) (suffix : BinaryWord) :
    ∃ ticks ≤ 6 * word.length + 7, ∃ after,
      (emitEmptyCertificate lanes).RunsOutput word ticks initialized after suffix
        (checkPackedMergePrefixTraceViolation word :: suffix) :=
  runsOutput_emitEmptyCertificate_of_count lanes hLanes
    (hHeader.outerLengths query cert hOuter).2 hHeader.branchZero hHeader.branchScratch
    hOuter hInvalid suffix

private theorem positive_flag (b : Bool) : 0 < b.toNat ↔ b = true := by cases b <;> decide

/-- Dispatch on any input with its exact scanner result. The three malformed cases
end at the current valuation and report the specified checker answer. -/
theorem runsOutput_traceHeaderDispatch (lanes : TraceHeaderLane → R)
    (hLanes : Function.Injective lanes) (continuation : Fragment R) (word : BinaryWord)
    {before initialized : R → Nat}
    (hHeader : TraceHeaderRegisterResult lanes word before initialized)
    (suffix : BinaryWord) (bound : Nat)
    (hNext : TraceHeaderContinuation continuation word initialized suffix bound) :
    ∃ ticks ≤ traceHeaderDispatchCost word.length bound, ∃ after,
      (traceHeaderDispatch lanes continuation).RunsOutput word ticks initialized after suffix
        (checkPackedMergePrefixTraceViolation word :: suffix) := by
  let output := checkPackedMergePrefixTraceViolation word :: suffix
  let malformed := emitEmptyCertificate lanes
  let cap := testHeaderLane lanes (.header .capValid) continuation malformed
  let arity := testHeaderLane lanes (.header .arityValid) cap malformed
  let inner := testHeaderLane lanes (.pair .innerValid) arity malformed
  have choose (lane : TraceHeaderLane) (hLane : lane ≠ .leftCopy ∧ lane ≠ .rightCopy ∧
      lane ≠ .scratch) (hFlag : initialized (lanes lane) ≤ 1) (yes no : Fragment R) (budget : Nat)
      (hPositive : 0 < initialized (lanes lane) → ∃ ticks ≤ budget, ∃ after,
        yes.RunsOutput word ticks initialized after suffix output)
      (hAbsent : ¬ 0 < initialized (lanes lane) → ∃ ticks ≤ budget, ∃ after,
        no.RunsOutput word ticks initialized after suffix output) :
      ∃ ticks ≤ budget + 12, ∃ after,
        (testHeaderLane lanes lane yes no).RunsOutput word ticks initialized after suffix
          output := by
    simpa only [show ∀ n : Nat, n + 6 * 1 + 6 = n + 12 by intro n; omega] using
      runsOutput_testHeaderLane lanes hLanes lane hLane word initialized suffix output yes no
        1 budget hHeader.branchZero hHeader.branchScratch hFlag hPositive hAbsent
  have hOuterFlag := hHeader.outerValid
  have hMalformed {query cert : BinaryWord} (hOuter : decodePackedPair word = some (query, cert))
      (hInvalid : ¬ ∃ r code c, ValidMergePrefixTraceQuery query r code c)
      {budget : Nat} (hBudget : 6 * word.length + 7 ≤ budget) :
      ∃ ticks ≤ budget, ∃ after,
        malformed.RunsOutput word ticks initialized after suffix output := by
    obtain ⟨ticks, hTicks, after, hRun⟩ :=
      runsOutput_emitEmptyCertificate lanes hLanes hHeader hOuter hInvalid suffix
    exact ⟨ticks, hTicks.trans hBudget, after, hRun⟩
  have hArity {query cert request candidate : BinaryWord}
      (hOuter : decodePackedPair word = some (query, cert))
      (hInner : decodePackedPair query = some (request, candidate)) :
      ∃ ticks ≤ bound + 6 * word.length + 31, ∃ after,
        arity.RunsOutput word ticks initialized after suffix output := by
    obtain ⟨seeded, hHeaders⟩ := hHeader.headers query cert request candidate hOuter hInner
    have hA : initialized (lanes (.header .arityValid)) =
        (requestHeaderProgress request).arityValid.toNat := hHeaders.arityValid
    have hC : initialized (lanes (.header .capValid)) =
        (requestHeaderProgress request).capValid.toNat := hHeaders.capValid
    obtain ⟨ticks, hTicks, after, hRun⟩ := choose (.header .arityValid) (by simp)
      (hA ▸ Bool.toNat_le _) cap malformed (bound + 6 * word.length + 19) (by
        intro hPositive
        have hArityTrue := (positive_flag _).mp (hA ▸ hPositive)
        obtain ⟨capTicks, hCapTicks, after, hCapRun⟩ := choose (.header .capValid) (by simp)
          (hC ▸ Bool.toNat_le _) continuation malformed (bound + 6 * word.length + 7) (by
            intro hPositive
            obtain ⟨ticks, hTicks, after, hRun⟩ :=
              hNext query cert request candidate hOuter hInner hArityTrue
                ((positive_flag _).mp (hC ▸ hPositive))
            exact ⟨ticks, by omega, after, hRun⟩)
          (by
            intro hAbsent
            exact hMalformed hOuter (invalidQuery_of_bad_header hInner fun h ↦
              hAbsent (hC ▸ (positive_flag _).mpr h.2)) (by omega))
        exact ⟨capTicks, by omega, after, hCapRun⟩)
      (by
        intro hAbsent
        exact hMalformed hOuter (invalidQuery_of_bad_header hInner fun h ↦
          hAbsent (hA ▸ (positive_flag _).mpr h.1)) (by omega))
    exact ⟨ticks, by omega, after, hRun⟩
  have hInner {query cert : BinaryWord} (hOuter : decodePackedPair word = some (query, cert)) :
      ∃ ticks ≤ bound + 6 * word.length + 43, ∃ after,
        inner.RunsOutput word ticks initialized after suffix output := by
    have hFlag : initialized (lanes (.pair .innerValid)) = (decodePackedPair query).isSome.toNat :=
      by simpa only [hOuter, Option.bind_some] using hHeader.innerValid
    obtain ⟨ticks, hTicks, after, hRun⟩ := choose (.pair .innerValid) (by simp)
      (hFlag ▸ Bool.toNat_le _) arity malformed (bound + 6 * word.length + 31) (by
        intro hPositive
        cases hDecoded : decodePackedPair query with
        | none => simp [hFlag, hDecoded] at hPositive
        | some pair =>
          obtain ⟨request, candidate⟩ := pair
          exact hArity hOuter hDecoded)
      (by
        intro hAbsent
        cases hDecoded : decodePackedPair query with
        | none => exact hMalformed hOuter (invalidQuery_of_missing_inner hDecoded) (by omega)
        | some pair => simp [hFlag, hDecoded] at hAbsent)
    exact ⟨ticks, by omega, after, hRun⟩
  obtain ⟨ticks, hTicks, after, hRun⟩ := choose (.pair .outerValid) (by simp)
    (hOuterFlag ▸ Bool.toNat_le _) inner (emitBit false) (bound + 6 * word.length + 43) (by
      intro hPositive
      cases hDecoded : decodePackedPair word with
      | none => simp [hOuterFlag, hDecoded] at hPositive
      | some pair =>
        obtain ⟨query, cert⟩ := pair
        exact hInner hDecoded)
    (by
      intro hAbsent
      cases hDecoded : decodePackedPair word with
      | none =>
        have hCheck : checkPackedMergePrefixTraceViolation word = false := by
          apply Bool.eq_iff_iff.mpr
          rw [checkPackedMergePrefixTraceViolation_eq_true_iff]
          simp only [Bool.false_eq_true, iff_false]
          rintro ⟨query, cert, hPacked, _⟩
          have hPair := decodePackedPair_eq_some_iff.mpr hPacked
          simp [hDecoded] at hPair
        rw [show output = false :: suffix by simp [output, hCheck]]
        exact ⟨1, by omega, initialized, runsOutput_dispatchBit word initialized suffix false⟩
      | some pair => simp [hOuterFlag, hDecoded] at hAbsent)
  exact ⟨ticks, by unfold traceHeaderDispatchCost; omega, after, hRun⟩

/-- Scan and dispatch from the raw input. The callback is needed only for a successfully
framed input whose two unary header delimiters were found. -/
theorem runsOutput_traceHeaderRegister_dispatch (lanes : TraceHeaderLane → R)
    (hLanes : Function.Injective lanes) (continuation : Fragment R) (word : BinaryWord)
    (before : R → Nat) (hZero : ∀ lane, before (lanes lane) = 0)
    (suffix : BinaryWord) (bound : Nat)
    (hNext : ∀ initialized, TraceHeaderRegisterResult lanes word before initialized →
      TraceHeaderContinuation continuation word initialized suffix bound) :
    ∃ ticks ≤ traceHeaderRegisterCost word.length + traceHeaderDispatchCost word.length bound,
      ∃ after, ((traceHeaderRegister lanes).seq (traceHeaderDispatch lanes continuation)).RunsOutput
        word ticks before after suffix (checkPackedMergePrefixTraceViolation word :: suffix) := by
  obtain ⟨scanTicks, hScanTicks, initialized, hScanRun, hHeader⟩ :=
    runsValues_traceHeaderRegister lanes hLanes word before hZero
  obtain ⟨checkTicks, hCheckTicks, after, hCheckRun⟩ :=
    runsOutput_traceHeaderDispatch lanes hLanes continuation word hHeader suffix bound
      (hNext initialized hHeader)
  exact ⟨_, Nat.add_le_add hScanTicks hCheckTicks, after,
    (hScanRun.withOutput suffix).seq hCheckRun⟩

end PvsNP.MCSP
