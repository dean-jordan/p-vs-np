module

public import PvsNP.MCSP.QueryStructureRegister
public import PvsNP.MCSP.TraceExtentDispatch
public import PvsNP.TuringMachine.Registers.PositiveBranch

/-! # Dispatch after deciding the structural checks -/

public section

namespace PvsNP.MCSP

open RegisterMachine RegisterMachine.Fragment

variable {R : Type}

/-- A nonzero codec or prefix flag rejects the query. The counter is out
of range exactly when both of its scans found a one. -/
def queryStructureBranch (regs : QueryStructureRegisters R) (malformed continuation : Fragment R) :
    Fragment R :=
  let lower := ifRegisterPositive (regs.counterPrefix .lowerOnes) malformed continuation
  let counter := ifRegisterPositive (regs.counterPrefix .high) lower continuation
  let prefixTest := ifRegisterPositive (regs.counterPrefix .order) malformed counter
  ifRegisterPositive (regs.descriptions .failures) malformed prefixTest

/-- Check the query and enter the trace checker only for a valid pair. -/
def queryStructureDispatch (regs : QueryStructureRegisters R) (headers : TraceHeaderLane → R)
    (continuation : Fragment R) : Fragment R :=
  (queryStructureRegister regs).seq
    (queryStructureBranch regs (emitEmptyCertificate headers) continuation)

variable [DecidableEq R]

private theorem runsOutput_queryStructureBranch (regs : QueryStructureRegisters R)
    (malformed continuation : Fragment R) (word : BinaryWord) (values : R → Nat)
    (suffix output : BinaryWord) (bound : Nat)
    (hMalformed : ¬ queryStructurePass regs values → ∃ ticks ≤ bound, ∃ after,
      malformed.RunsOutput word ticks values after suffix output)
    (hValid : queryStructurePass regs values → ∃ ticks ≤ bound, ∃ after,
      continuation.RunsOutput word ticks values after suffix output) :
    ∃ ticks ≤ bound + 8, ∃ after,
      (queryStructureBranch regs malformed continuation).RunsOutput word ticks values after
        suffix output := by
  have select (r : R) (yes no : Fragment R) (budget : Nat)
      (hRun : ∃ ticks ≤ budget, ∃ after,
        (if 0 < values r then yes else no).RunsOutput word ticks values after suffix output) :
      ∃ ticks ≤ budget + 2, ∃ after,
        (ifRegisterPositive r yes no).RunsOutput word ticks values after suffix output := by
    obtain ⟨ticks, hTicks, after, hRun⟩ := hRun
    have hTime := ifRegisterPositiveTime_le (values r)
    exact ⟨_, by omega, after, runsOutput_ifRegisterPositive r yes no word values hRun⟩
  let lower := ifRegisterPositive (regs.counterPrefix .lowerOnes) malformed continuation
  let counter := ifRegisterPositive (regs.counterPrefix .high) lower continuation
  let prefixTest := ifRegisterPositive (regs.counterPrefix .order) malformed counter
  have hBad {budget : Nat} (hBudget : bound ≤ budget) (hFail : ¬ queryStructurePass regs values) :
      ∃ ticks ≤ budget, ∃ after, malformed.RunsOutput word ticks values after suffix output := by
    obtain ⟨ticks, hTicks, after, hRun⟩ := hMalformed hFail
    exact ⟨ticks, hTicks.trans hBudget, after, hRun⟩
  have hGood {budget : Nat} (hBudget : bound ≤ budget) (hPass : queryStructurePass regs values) :
      ∃ ticks ≤ budget, ∃ after, continuation.RunsOutput word ticks values after suffix output := by
    obtain ⟨ticks, hTicks, after, hRun⟩ := hValid hPass
    exact ⟨ticks, hTicks.trans hBudget, after, hRun⟩
  have hOuter := select (regs.descriptions .failures) malformed prefixTest (bound + 6) (by
    split
    · rename_i hFail
      exact hBad (Nat.le_add_right ..) (fun h ↦ (Nat.ne_of_gt hFail) h.1)
    · rename_i hCodec
      have hc := Nat.eq_zero_of_not_pos hCodec
      have hPrefix := select (regs.counterPrefix .order) malformed counter (bound + 4) (by
        split
        · rename_i hOrder
          exact hBad (Nat.le_add_right ..) (fun h ↦ (Nat.ne_of_gt hOrder) h.2.2)
        · rename_i hNoOrder
          have ho := Nat.eq_zero_of_not_pos hNoOrder
          have hCounter := select (regs.counterPrefix .high) lower continuation (bound + 2) (by
            split
            · rename_i hHigh
              exact select (regs.counterPrefix .lowerOnes) malformed continuation bound (by
                split
                · rename_i hLower
                  exact hBad (Nat.le_refl _) (fun h ↦ h.2.1.elim
                    (Nat.ne_of_gt hHigh) (Nat.ne_of_gt hLower))
                · rename_i hLower
                  exact hGood (Nat.le_refl _) ⟨hc, Or.inr (Nat.eq_zero_of_not_pos hLower), ho⟩)
            · rename_i hHigh
              exact hGood (Nat.le_add_right ..) ⟨hc, Or.inl (Nat.eq_zero_of_not_pos hHigh), ho⟩)
          exact hCounter)
      exact hPrefix)
  exact hOuter

/-- The continuation receives the measured register contents and a decoded valid query. -/
@[expose] def QueryStructureContinuation (regs : QueryStructureRegisters R)
    (continuation : Fragment R) (request candidate cert : BinaryWord) (fields : MergeRequestFields)
    (before : R → Nat) (suffix : BinaryWord) (bound : Nat) : Prop :=
  let query := packedPair request candidate
  let word := packedPair query cert
  ∀ after, QueryStructureRegisterResult regs request candidate cert fields before after →
    ∀ r code c, ValidMergePrefixTraceQuery query r code c →
      ∃ ticks ≤ bound, ∃ final,
        continuation.RunsOutput word ticks after final suffix
          (checkPackedMergePrefixTraceViolation word :: suffix)

/-- On a sized query, the dispatch consumes a raw-input polynomial clock.
Malformed queries use the empty-certificate rule. -/
theorem runsOutput_queryStructureDispatch (regs : QueryStructureRegisters R)
    (hWiring : QueryStructureWiring regs) (headers : TraceHeaderLane → R)
    (hHeaders : Function.Injective headers)
    (hSeparate : ∀ lane ∈ extentDispatchHeaderLanes,
      (∀ k, headers lane ≠ regs.bases k) ∧ (∀ k, headers lane ≠ regs.counterPrefix k) ∧
        (∀ k, headers lane ≠ regs.descriptions k))
    (continuation : Fragment R) {request candidate cert : BinaryWord} {fields : MergeRequestFields}
    (hFields : readMergeRequestFields request = some fields)
    (hLength : candidate.length = mergeWitnessLength fields.arity fields.cap)
    (before : R → Nat)
    (hReady : QueryStructureReady regs (packedPair (packedPair request candidate) cert)
      request fields before)
    (hCert : before (headers (.pair .certificateLength)) = cert.length)
    (hZero : before (headers .zero) = 0)
    (hScratch : before (headers .leftCopy) = 0 ∧ before (headers .rightCopy) = 0 ∧
      before (headers .scratch) = 0)
    (suffix : BinaryWord) (bound : Nat)
    (hNext : QueryStructureContinuation regs continuation request candidate cert fields before
      suffix bound) :
    let word := packedPair (packedPair request candidate) cert
    ∃ ticks ≤ queryStructureRegisterCost word.length
        (queryStructureMeasures request candidate fields) +
        (bound + 6 * word.length + 15), ∃ after,
      (queryStructureDispatch regs headers continuation).RunsOutput word ticks before after suffix
        (checkPackedMergePrefixTraceViolation word :: suffix) := by
  let query := packedPair request candidate
  let word := packedPair query cert
  let output := checkPackedMergePrefixTraceViolation word :: suffix
  obtain ⟨scanTicks, hScanTime, measured, hScan, hResult⟩ :=
    runsValues_queryStructureRegister regs hWiring hFields hLength before hReady
  have hKeep (lane : TraceHeaderLane) (h : lane ∈ extentDispatchHeaderLanes) :
      measured (headers lane) = before (headers lane) := by
    obtain ⟨hb, hc, hd⟩ := hSeparate lane h
    exact hResult.external _ hb hc hd
  have hBranch := runsOutput_queryStructureBranch regs (emitEmptyCertificate headers) continuation
    word measured suffix output (bound + 6 * word.length + 7) (by
      intro hFailure
      have hInvalid : ¬ ∃ r code c, ValidMergePrefixTraceQuery query r code c :=
        fun h ↦ hFailure (hResult.pass.mpr ((mergeTraceQueryFieldsValid_iff _ _).mpr h))
      obtain ⟨ticks, hTicks, final, hRun⟩ := runsOutput_emitEmptyCertificate_of_count
        headers hHeaders
        ((hKeep _ (by simp [extentDispatchHeaderLanes])).trans hCert)
        ((hKeep _ (by simp [extentDispatchHeaderLanes])).trans hZero)
        ⟨(hKeep _ (by simp [extentDispatchHeaderLanes])).trans hScratch.1,
          (hKeep _ (by simp [extentDispatchHeaderLanes])).trans hScratch.2.1,
          (hKeep _ (by simp [extentDispatchHeaderLanes])).trans hScratch.2.2⟩
        (decodePackedPair_eq_some_iff.mpr rfl) hInvalid suffix
      exact ⟨ticks, hTicks.trans (by dsimp only [word]; omega), final, hRun⟩) (by
      intro hPass
      obtain ⟨r, code, c, hValid⟩ := (mergeTraceQueryFieldsValid_iff _ _).mp
        (hResult.pass.mp hPass)
      obtain ⟨ticks, hTicks, final, hRun⟩ := hNext measured hResult r code c hValid
      exact ⟨ticks, by omega, final, hRun⟩)
  obtain ⟨branchTicks, hBranchTime, after, hRun⟩ := hBranch
  exact ⟨_, Nat.add_le_add hScanTime hBranchTime, after, (hScan.withOutput suffix).seq hRun⟩

end PvsNP.MCSP
