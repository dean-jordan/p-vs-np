module

public import PvsNP.MCSP.TraceInputPositionRegister
public import PvsNP.TuringMachine.Registers.PositiveBranch

import PvsNP.CookLevin.Generator.AcceptingBlock
import all PvsNP.MCSP.TraceInputRegister
import Mathlib.Tactic.GCongr

/-! # Reject traces whose input bits disagree with the certified row -/

public section

namespace PvsNP.MCSP

open Circuits RegisterMachine RegisterMachine.Fragment

variable {R : Type}

/-- Compute the three addresses and compare the two traces with the row. -/
def traceInputDispatch (positions : TraceInputPositionLane → R) (scan : TraceInputLane → R)
    (continuation : Fragment R) : Fragment R :=
  (traceInputPositionRegister positions).seq ((traceInputRegister scan).seq
    (ifRegisterPositive (scan .failures) (emitBit false) continuation))

/-- The ready state contains the four measured dimensions and empty scratch lanes. -/
structure TraceInputDispatchReady (positions : TraceInputPositionLane → R)
    (scan : TraceInputLane → R) (cert : BinaryWord) (arity oldCount newCount : Nat)
    (before : R → Nat) : Prop where
  arityValue : before (positions .arity) = arity
  oldCountValue : before (positions .oldCount) = oldCount
  newCountValue : before (positions .newCount) = newCount
  certificateLength : before (positions .certificateLength) = cert.length
  positionZero : ∀ k, k ∉ [.arity, .oldCount, .newCount, .certificateLength] →
    before (positions k) = 0
  scanZero : ∀ old i, before (scan (traceInputScanLanes old i)) = 0
  failuresZero : before (scan .failures) = 0

/-- On success, the continuation can use both input equalities and the unchanged registers. -/
structure TraceInputDispatchResult (positions : TraceInputPositionLane → R)
    (scan : TraceInputLane → R) (r : MergeRequest) (candidate : BooleanCircuit r.arity)
    (cert : BinaryWord) (before after : R → Nat) : Prop where
  oldInputs : (mergeTraceCertificateOldTrace r.arity r.old.size cert).take r.arity =
    mergeTraceCertificateInputBits r.arity cert
  newInputs : (mergeTraceCertificateNewTrace r.arity r.old.size candidate.size cert).take r.arity =
    mergeTraceCertificateInputBits r.arity cert
  frame : ∀ k, k ≠ positions .rowPosition → (∀ side, k ≠ positions (.tracePosition side)) →
    (∀ side i, k ≠ scan (traceInputScanLanes side i)) → k ≠ scan .failures → after k = before k

@[expose] def traceInputDispatchCost (length bound : Nat) : Nat :=
  (89 * length + 70) + (traceInputRegisterCost length length + (bound + 3))

theorem traceInputDispatchCost_polynomiallyBounded {bound : Nat → Nat}
    (hBound : PolynomiallyBounded bound) :
    PolynomiallyBounded (fun n ↦ traceInputDispatchCost n (bound n)) :=
  (((PolynomiallyBounded.const 89).mul PolynomiallyBounded.id).add
    (PolynomiallyBounded.const 70)).add
    ((traceInputRegisterCost_polynomiallyBounded PolynomiallyBounded.id
      PolynomiallyBounded.id).add (hBound.add (PolynomiallyBounded.const 3)))

variable [DecidableEq R]

/-- On a valid query and a well-shaped certificate, this stage handles all
input-wire disagreements and otherwise supplies the two verified prefixes. -/
theorem runsOutput_traceInputDispatch (positions : TraceInputPositionLane → R)
    (scan : TraceInputLane → R) (hPositions : Function.Injective positions)
    (hScan : Function.Injective scan) (hLink : TraceInputPositionWiring positions scan)
    (continuation : Fragment R) {query code cert : BinaryWord}
    {r : MergeRequest} {c : BooleanCircuit r.arity}
    (hValid : ValidMergePrefixTraceQuery query r code c)
    (hLayout : MergeTraceCertificateLayout r.arity r.old.size c.size cert)
    (before : R → Nat) (hReady : TraceInputDispatchReady positions scan cert r.arity
      r.old.size c.size before) (suffix : BinaryWord) (bound : Nat)
    (hNext : ∀ after, TraceInputDispatchResult positions scan r c cert before after →
      ∃ ticks ≤ bound, ∃ final,
        continuation.RunsOutput (packedPair query cert) ticks after final suffix
          (checkPackedMergePrefixTraceViolation (packedPair query cert) :: suffix)) :
    let word := packedPair query cert
    ∃ ticks ≤ traceInputDispatchCost word.length bound, ∃ final,
      (traceInputDispatch positions scan continuation).RunsOutput word ticks before final
        suffix (checkPackedMergePrefixTraceViolation word :: suffix) := by
  let word := packedPair query cert
  let output := checkPackedMergePrefixTraceViolation word :: suffix
  obtain ⟨positionTicks, hPositionTime, addressed, hAddressRun, hAddress⟩ :=
    runsValues_traceInputPositionRegister positions hPositions word before hReady.positionZero
  have hSeed := hAddress.traceInputSeed hPositions hLink hLayout hReady.arityValue
    hReady.oldCountValue hReady.newCountValue hReady.certificateLength
  have hScanLanes : ∀ (side : Bool) (i : Fin 6),
      traceInputScanLanes side i ≠ .rowPosition ∧
      ∀ other : Bool, traceInputScanLanes side i ≠ .tracePosition other :=
    fun side i ↦ ⟨(traceInputSeed_ne_scan side i).2.1.symm,
      fun other ↦ ((traceInputSeed_ne_scan side i).2.2.1 other).symm⟩
  have hFailureLane : TraceInputLane.failures ≠ .rowPosition ∧
      ∀ side : Bool, TraceInputLane.failures ≠ .tracePosition side :=
    ⟨fun h ↦ by cases h, fun _ h ↦ by cases h⟩
  have hKeep {k : TraceInputLane} (hr : k ≠ .rowPosition)
      (ht : ∀ side, k ≠ .tracePosition side) : addressed (scan k) = before (scan k) :=
    hAddress.frame _ (fun e ↦ hr (hScan (e.trans hLink.rowPosition.symm)))
      (fun side e ↦ ht side (hScan (e.trans (hLink.tracePosition side).symm)))
  obtain ⟨scanTicks, hScanTime, checked, hScanRun, _, _, hPass, hFrame⟩ :=
    runsValues_traceInputRegister scan hScan query hLayout addressed hSeed
      (fun side i ↦ (hKeep (hScanLanes side i).1 (hScanLanes side i).2).trans
        (hReady.scanZero side i))
      ((hKeep hFailureLane.1 hFailureLane.2).trans hReady.failuresZero)
  have hBranch : ∃ ticks ≤ bound + 1, ∃ final,
      (if 0 < checked (scan .failures) then emitBit false else continuation).RunsOutput
        word ticks checked final suffix output := by
    split
    · rename_i hPositive
      have hReject : checkPackedMergePrefixTraceViolation word = false := by
        apply Bool.eq_false_iff.mpr
        intro hAccept
        have hChecks := (checkPackedMergePrefixTraceViolation_eq_true_iff_certificateChecks
          hValid cert).mp hAccept
        exact (Nat.ne_of_gt hPositive) (hPass.mpr ⟨hChecks.oldInputs, hChecks.newInputs⟩)
      refine ⟨1, by omega, checked, ?_⟩
      rw [show output = false :: suffix by simp only [output, hReject]]
      exact run_emitBit false word (⟨none, checked, none, suffix⟩ : Config R Unit) rfl
    · rename_i hAbsent
      obtain ⟨hOld, hNew⟩ := hPass.mp (Nat.eq_zero_of_not_pos hAbsent)
      obtain ⟨ticks, hTicks, final, hRun⟩ := hNext checked
        ⟨hOld, hNew, fun k hr ht hs hf ↦ (hFrame k hs hf).trans (hAddress.frame k hr ht)⟩
      exact ⟨ticks, by omega, final, hRun⟩
  obtain ⟨branchTicks, hBranchTime, final, hBranchRun⟩ := hBranch
  have hRun := (hAddressRun.withOutput suffix).seq ((hScanRun.withOutput suffix).seq
    (runsOutput_ifRegisterPositive (scan .failures) (emitBit false) continuation
      word checked hBranchRun))
  rw [hReady.certificateLength, hReady.arityValue, hReady.oldCountValue, hReady.newCountValue]
    at hPositionTime
  have hCert : cert.length ≤ word.length := by
    dsimp only [word]
    rw [length_packedPair]
    omega
  have hArity : r.arity ≤ word.length := by
    have hLength := hLayout.length_eq
    unfold mergeTraceCertificateLength mergeTraceCertificateClaimOffset
      mergeTraceCertificateNewOffset mergeTraceCertificateOldOffset at hLength
    omega
  have hPositionBound : positionTicks ≤ 89 * word.length + 70 :=
    (hPositionTime.trans (traceInputPositionRegisterCost_le_of_layout hLayout)).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left 89 hCert) 70)
  have hScanBound : scanTicks ≤ traceInputRegisterCost word.length word.length :=
    hScanTime.trans (by
      change traceInputRegisterCost word.length r.arity ≤ _
      unfold traceInputRegisterCost
      gcongr)
  have hTest := ifRegisterPositiveTime_le (checked (scan .failures))
  refine ⟨_, Nat.add_le_add hPositionBound (Nat.add_le_add hScanBound ?_), final, hRun⟩
  omega

end PvsNP.MCSP
