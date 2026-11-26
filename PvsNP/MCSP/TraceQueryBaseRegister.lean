module

public import PvsNP.TuringMachine.Registers.Affine
public import PvsNP.TuringMachine.Registers.Subtract

/-! # Register addresses for the merge trace query -/

public section

namespace PvsNP.MCSP

open RegisterMachine RegisterMachine.Fragment

/-- The four inputs, three computed addresses and two work registers. -/
inductive TraceQueryBaseLane where
  | arity | header | requestLength | prefixLength
  | oldBase | candidateBase | prefixStart | work | scratch
  deriving DecidableEq

variable {R : Type}

/-- Locate the old and candidate descriptions and the logical prefix within the request. -/
@[expose] def traceQueryBaseRegister (lanes : TraceQueryBaseLane → R) : Fragment R :=
  let header := add (lanes .header) (lanes .oldBase) (lanes .scratch)
  let oldBase := accumulateAffine (lanes .arity) (lanes .oldBase)
    (lanes .work) (lanes .scratch) 4 8
  let candidateBase := accumulateAffine (lanes .requestLength) (lanes .candidateBase)
    (lanes .work) (lanes .scratch) 4 7
  let copyRequest := add (lanes .requestLength) (lanes .prefixStart) (lanes .scratch)
  let prefixStart := subtract (lanes .prefixLength) (lanes .prefixStart)
    (lanes .work) (lanes .scratch)
  (((header.seq oldBase).seq candidateBase).seq copyRequest).seq prefixStart

/-- The exact instruction count on prepared registers. -/
@[expose] def traceQueryBaseRegisterCost (arity header requestLength prefixLength : Nat) : Nat :=
  20 * arity + 5 * header + 25 * requestLength + 7 * prefixLength + 56

theorem traceQueryBaseRegisterCost_polynomiallyBounded
    {arity header requestLength prefixLength : Nat → Nat}
    (hArity : PolynomiallyBounded arity) (hHeader : PolynomiallyBounded header)
    (hRequest : PolynomiallyBounded requestLength) (hPrefix : PolynomiallyBounded prefixLength) :
    PolynomiallyBounded (fun n ↦
      traceQueryBaseRegisterCost (arity n) (header n) (requestLength n) (prefixLength n)) := by
  let lit := PolynomiallyBounded.const
  exact (((((lit 20).mul hArity).add ((lit 5).mul hHeader)).add
    ((lit 25).mul hRequest)).add ((lit 7).mul hPrefix)).add (lit 56)

/-- Only the three result registers may change. -/
structure TraceQueryBaseRegisterResult (lanes : TraceQueryBaseLane → R)
    (before after : R → Nat) : Prop where
  oldBase : after (lanes .oldBase) = before (lanes .header) + 4 * before (lanes .arity) + 8
  candidateBase : after (lanes .candidateBase) = 4 * before (lanes .requestLength) + 7
  prefixStart : after (lanes .prefixStart) = before (lanes .requestLength) -
    before (lanes .prefixLength)
  frame : ∀ r, r ≠ lanes .oldBase → r ≠ lanes .candidateBase → r ≠ lanes .prefixStart →
    after r = before r

variable [DecidableEq R]

/-- The calculation preserves its inputs and restores both work registers. -/
theorem runsValues_traceQueryBaseRegister (lanes : TraceQueryBaseLane → R)
    (hLanes : Function.Injective lanes) (x : BinaryWord) (before : R → Nat)
    (hZero : ∀ lane, lane ≠ .arity → lane ≠ .header → lane ≠ .requestLength →
      lane ≠ .prefixLength → before (lanes lane) = 0) :
    ∃ after : R → Nat, (traceQueryBaseRegister lanes).RunsValues x
      (traceQueryBaseRegisterCost (before (lanes .arity)) (before (lanes .header))
        (before (lanes .requestLength)) (before (lanes .prefixLength))) before after ∧
      TraceQueryBaseRegisterResult lanes before after := by
  let arity := before (lanes .arity)
  let header := before (lanes .header)
  let request := before (lanes .requestLength)
  let prefixCount := before (lanes .prefixLength)
  have hNe {a b : TraceQueryBaseLane} (h : a ≠ b) : lanes a ≠ lanes b :=
    fun hEq ↦ h (hLanes hEq)
  have hLane (a b : TraceQueryBaseLane) : lanes a = lanes b ↔ a = b :=
    ⟨fun h ↦ hLanes h, congrArg lanes⟩
  have hOldZero := hZero .oldBase (by decide) (by decide) (by decide) (by decide)
  have hCandidateZero := hZero .candidateBase (by decide) (by decide) (by decide) (by decide)
  have hPrefixZero := hZero .prefixStart (by decide) (by decide) (by decide) (by decide)
  have hWorkZero := hZero .work (by decide) (by decide) (by decide) (by decide)
  have hScratchZero := hZero .scratch (by decide) (by decide) (by decide) (by decide)
  let copiedHeader := setValue (lanes .oldBase) header before
  have hCopyHeader : (add (lanes .header) (lanes .oldBase) (lanes .scratch)).RunsValues
      x (5 * header + 2) before copiedHeader := by
    simpa only [hOldZero, Nat.zero_add, copiedHeader, header] using
      runsValues_add (lanes .header) (lanes .oldBase) (lanes .scratch) x before
        (hNe (by decide)) (hNe (by decide)) (hNe (by decide)) hScratchZero
  let withOld := setValue (lanes .oldBase) (header + 4 * arity + 8) before
  have hOldLanes : [lanes .arity, lanes .oldBase, lanes .work, lanes .scratch].Nodup :=
    ((by decide : ([.arity, .oldBase, .work, .scratch] : List TraceQueryBaseLane).Nodup)).map hLanes
  have hOld : (accumulateAffine (lanes .arity) (lanes .oldBase) (lanes .work)
      (lanes .scratch) 4 8).RunsValues x (affineTime 4 8 arity) copiedHeader withOld := by
    have hRun := runsValues_accumulateAffine (lanes .arity) (lanes .oldBase) (lanes .work)
      (lanes .scratch) 4 8 x copiedHeader hOldLanes
      (by simp [copiedHeader, setValue, hLane, hWorkZero])
      (by simp [copiedHeader, setValue, hLane, hScratchZero])
    simpa only [show copiedHeader (lanes .arity) = arity from setValue_other (hNe (by decide)) ..,
      show copiedHeader (lanes .oldBase) = header from setValue_same .., copiedHeader,
      setValue_replace, withOld] using hRun
  let withCandidate := setValue (lanes .candidateBase) (4 * request + 7) withOld
  have hCandidateLanes : [lanes .requestLength, lanes .candidateBase, lanes .work,
      lanes .scratch].Nodup :=
    ((by decide : ([.requestLength, .candidateBase, .work, .scratch] :
      List TraceQueryBaseLane).Nodup)).map hLanes
  have hCandidate : (accumulateAffine (lanes .requestLength) (lanes .candidateBase)
      (lanes .work) (lanes .scratch) 4 7).RunsValues
      x (affineTime 4 7 request) withOld withCandidate := by
    have hRun := runsValues_accumulateAffine (lanes .requestLength) (lanes .candidateBase)
      (lanes .work) (lanes .scratch) 4 7 x withOld hCandidateLanes
      (by simp [withOld, setValue, hLane, hWorkZero])
      (by simp [withOld, setValue, hLane, hScratchZero])
    have hVal : withOld (lanes .candidateBase) = 0 := by
      simp [withOld, setValue, hLane, hCandidateZero]
    simpa only [show withOld (lanes .requestLength) = request from
      setValue_other (hNe (by decide)) .., hVal, Nat.zero_add, withCandidate] using hRun
  have hRequest : withCandidate (lanes .requestLength) = request := by
    simp [withCandidate, withOld, setValue, hLane, request]
  let copiedRequest := setValue (lanes .prefixStart) request withCandidate
  have hCopyRequest : (add (lanes .requestLength) (lanes .prefixStart) (lanes .scratch)).RunsValues
      x (5 * request + 2) withCandidate copiedRequest := by
    have hRun := runsValues_add (lanes .requestLength) (lanes .prefixStart) (lanes .scratch)
      x withCandidate (hNe (by decide)) (hNe (by decide)) (hNe (by decide))
      (by simp [withCandidate, withOld, setValue, hLane, hScratchZero])
    have hVal : withCandidate (lanes .prefixStart) = 0 := by
      simp [withCandidate, withOld, setValue, hLane, hPrefixZero]
    simpa only [hVal, Nat.zero_add, hRequest, copiedRequest] using hRun
  let after := setValue (lanes .prefixStart) (request - prefixCount) withCandidate
  have hPrefix : (subtract (lanes .prefixLength) (lanes .prefixStart) (lanes .work)
      (lanes .scratch)).RunsValues x (7 * prefixCount + 3) copiedRequest after := by
    have hRun := runsValues_subtract (lanes .prefixLength) (lanes .prefixStart) (lanes .work)
      (lanes .scratch) x copiedRequest (hNe (by decide)) (hNe (by decide)) (hNe (by decide))
      (hNe (by decide))
      (by simp [copiedRequest, withCandidate, withOld, setValue, hLane, hWorkZero])
      (by simp [copiedRequest, withCandidate, withOld, setValue, hLane, hScratchZero])
    have hLength : copiedRequest (lanes .prefixLength) = prefixCount := by
      simp [copiedRequest, withCandidate, withOld, setValue, hLane, prefixCount]
    simpa only [hLength, show copiedRequest (lanes .prefixStart) = request from setValue_same ..,
      copiedRequest, setValue_replace, after] using hRun
  have hCost : traceQueryBaseRegisterCost arity header request prefixCount =
      (5 * header + 2) + affineTime 4 8 arity + affineTime 4 7 request +
        (5 * request + 2) + (7 * prefixCount + 3) := by
    unfold traceQueryBaseRegisterCost affineTime
    omega
  refine ⟨after, ?_, ⟨?_, ?_, ?_, ?_⟩⟩
  · change (traceQueryBaseRegister lanes).RunsValues x
      (traceQueryBaseRegisterCost arity header request prefixCount) before after
    rw [hCost]
    exact (((hCopyHeader.seq hOld).seq hCandidate).seq hCopyRequest).seq hPrefix
  · simp [after, withCandidate, withOld, setValue, hLane, header, arity]
  · simp [after, withCandidate, setValue, hLane, request]
  · simp [after, request, prefixCount]
  · intro r hOld hCandidate hPrefix
    simp [after, withCandidate, withOld, setValue, hOld, hCandidate, hPrefix]

end PvsNP.MCSP
