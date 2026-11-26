module

public import PvsNP.MCSP.CircuitLayoutRegister
public import PvsNP.MCSP.RequestLayout

/-! # Compute and check both padded circuit extents -/

public section

namespace PvsNP.MCSP

open Circuits RegisterMachine RegisterMachine.Fragment

/-- The arity, cap, and measured lengths form the inputs to this stage. -/
inductive TraceExtentLane where
  | arity | cap | bodyLength | candidateLength | oldCap
  | bound (old : Bool) | width (old : Bool) | span (old : Bool) | paddedLength (old : Bool)
  | minimum | maximum | prefixLength | failures
  | power | counter | zero | leftCopy | rightCopy | scratch
  deriving DecidableEq

/-- Both layout calculations share scratch, while keeping their results separate. -/
@[expose] def traceCircuitLayoutLanes (old : Bool) : CircuitLayoutLane → TraceExtentLane
  | .arity => .arity
  | .cap => if old then .oldCap else .cap
  | .bound => .bound old
  | .width => .width old
  | .span => .span old
  | .paddedLength => .paddedLength old
  | .power => .power
  | .counter => .counter
  | .leftCopy => .leftCopy
  | .rightCopy => .rightCopy
  | .scratch => .scratch

private theorem traceCircuitLayoutLanes_injective (old : Bool) :
    Function.Injective (traceCircuitLayoutLanes old) := by
  intro a b h
  cases old <;> cases a <;> cases b <;> simp_all [traceCircuitLayoutLanes]

@[expose] def traceShapeLanes : RequestShapeLane → TraceExtentLane
  | .arity => .arity
  | .bodyLength => .bodyLength
  | .oldLength => .paddedLength true
  | .candidateWidth => .paddedLength false
  | .candidateLength => .candidateLength
  | .minimum => .minimum
  | .maximum => .maximum
  | .prefixLength => .prefixLength
  | .failures => .failures
  | .leftCopy => .leftCopy
  | .rightCopy => .rightCopy
  | .scratch => .scratch

private theorem traceShapeLanes_injective : Function.Injective traceShapeLanes := by
  intro a b h
  cases a <;> cases b <;> simp_all [traceShapeLanes]

private def extentCompareLanes : Fin 5 → TraceExtentLane
  | 0 => .zero
  | 1 => .cap
  | 2 => .leftCopy
  | 3 => .rightCopy
  | _ => .scratch

private theorem extentCompareLanes_injective : Function.Injective extentCompareLanes := by decide

variable {R : Type}

private def loadOldCap (lanes : TraceExtentLane → R) : Fragment R :=
  ifLess (lanes .zero) (lanes .cap) (lanes .leftCopy) (lanes .rightCopy) (lanes .scratch)
    (add (lanes .cap) (lanes .oldCap) (lanes .scratch)) (incrementBy (lanes .oldCap) 1)

/-- Both padded lengths and the complete measure-only shape check, with the
old circuit budget kept at least one even when the candidate cap is zero. -/
def traceExtentRegister (lanes : TraceExtentLane → R) : Fragment R :=
  (loadOldCap lanes).seq <|
    (circuitLayoutRegister (lanes ∘ traceCircuitLayoutLanes false)).seq <|
    (circuitLayoutRegister (lanes ∘ traceCircuitLayoutLanes true)).seq
      (requestShapeRegister (lanes ∘ traceShapeLanes))

@[expose] def traceExtentRegisterCost (arity cap body candidateLength : Nat) : Nat :=
  (11 * cap + 8) + (circuitLayoutRegisterCost arity cap +
    (circuitLayoutRegisterCost arity (max 1 cap) + requestShapeRegisterCost arity body
      (mergeWitnessLength arity (max 1 cap)) (mergeWitnessLength arity cap) candidateLength))

private theorem mergeWitnessLength_poly {arity cap : Nat → Nat}
    (hArity : PolynomiallyBounded arity) (hCap : PolynomiallyBounded cap) :
    PolynomiallyBounded (fun n ↦ mergeWitnessLength (arity n) (cap n)) := by
  let m := (hArity.add hCap).add (PolynomiallyBounded.const 1)
  apply ((PolynomiallyBounded.const 26).mul (m.pow 2)).mono
  intro n
  have h := mergeRequestLengthBound_le_quadratic (arity n) (cap n)
  unfold mergeRequestLengthBound at h
  omega

theorem traceExtentRegisterCost_polynomiallyBounded {arity cap body candidateLength : Nat → Nat}
    (hArity : PolynomiallyBounded arity) (hCap : PolynomiallyBounded cap)
    (hBody : PolynomiallyBounded body) (hCandidate : PolynomiallyBounded candidateLength) :
    PolynomiallyBounded (fun n ↦ traceExtentRegisterCost
      (arity n) (cap n) (body n) (candidateLength n)) := by
  have hOld : PolynomiallyBounded (fun n ↦ max 1 (cap n)) :=
    (hCap.add (PolynomiallyBounded.const 1)).mono fun n ↦ Nat.max_le.mpr ⟨by omega, by omega⟩
  have hLoad := ((PolynomiallyBounded.const 11).mul hCap).add (PolynomiallyBounded.const 8)
  exact hLoad.add <| (circuitLayoutRegisterCost_polynomiallyBounded hArity hCap).add <|
    (circuitLayoutRegisterCost_polynomiallyBounded hArity hOld).add <|
      requestShapeRegisterCost_polynomiallyBounded hArity hBody
        (mergeWitnessLength_poly hArity hOld) (mergeWitnessLength_poly hArity hCap) hCandidate

@[expose] def traceExtentInputLanes : List TraceExtentLane :=
  [.arity, .cap, .bodyLength, .candidateLength]

/-- The exact extent checks and the width data needed to initialize circuit reads. -/
structure TraceExtentRegisterResult (lanes : TraceExtentLane → R) (before after : R → Nat) :
    Prop where
  oldCap : after (lanes .oldCap) = max 1 (before (lanes .cap))
  width : ∀ old, after (lanes (.width old)) = circuitFieldWidth (before (lanes .arity))
    (if old then max 1 (before (lanes .cap)) else before (lanes .cap))
  span : ∀ old, after (lanes (.span old)) = 3 + 2 * after (lanes (.width old))
  paddedLength : ∀ old, after (lanes (.paddedLength old)) = mergeWitnessLength
    (before (lanes .arity)) (if old then max 1 (before (lanes .cap)) else before (lanes .cap))
  prefixLength : after (lanes .prefixLength) = before (lanes .bodyLength) -
    mergeRequestBodyMinLength (before (lanes .arity)) (before (lanes .cap))
  failureBound : after (lanes .failures) ≤ 3
  valid : after (lanes .failures) = 0 ↔
    let minimum := mergeRequestBodyMinLength (before (lanes .arity)) (before (lanes .cap))
    let expected := mergeWitnessLength (before (lanes .arity)) (before (lanes .cap))
    minimum ≤ before (lanes .bodyLength) ∧ before (lanes .bodyLength) ≤ minimum + expected ∧
      before (lanes .candidateLength) = expected
  inputs : ∀ lane ∈ traceExtentInputLanes, after (lanes lane) = before (lanes lane)
  external : ∀ r, (∀ lane, r ≠ lanes lane) → after r = before r

variable [DecidableEq R]

private theorem runsValues_loadOldCap (lanes : TraceExtentLane → R)
    (hLanes : Function.Injective lanes) (word : BinaryWord) (before : R → Nat)
    (hZero : ∀ lane, lane ∉ traceExtentInputLanes → before (lanes lane) = 0) :
    ∃ ticks ≤ 11 * before (lanes .cap) + 8,
      (loadOldCap lanes).RunsValues word ticks before
        (setValue (lanes .oldCap) (max 1 (before (lanes .cap))) before) := by
  let cap := before (lanes .cap)
  let copyCap := add (lanes .cap) (lanes .oldCap) (lanes .scratch)
  let useOne := incrementBy (lanes .oldCap) 1
  have hEq (a b : TraceExtentLane) : lanes a = lanes b ↔ a = b :=
    ⟨fun h ↦ hLanes h, congrArg lanes⟩
  have hz (lane : TraceExtentLane) : lane ∉ traceExtentInputLanes → before (lanes lane) = 0 :=
    hZero lane
  have hScratch := hz .scratch (by decide)
  have hOld := hz .oldCap (by decide)
  have hCopy := runsValues_add (lanes .cap) (lanes .oldCap) (lanes .scratch) word before
    (by simp [hEq]) (by simp [hEq]) (by simp [hEq]) hScratch
  have hInc := runsValues_incrementBy (lanes .oldCap) 1 word before
  let ticks := if 0 < cap then 5 * cap + 2 else 1
  have hRun : (if before (lanes .zero) < cap then copyCap else useOne).RunsValues word ticks before
      (setValue (lanes .oldCap) (max 1 cap) before) := by
    have hZ := hz .zero (by decide)
    rw [hZ]
    by_cases h : 0 < cap
    · have hMax : max 1 cap = cap := Nat.max_eq_right (by omega)
      simpa only [ticks, ite_eq_left h, hMax, copyCap, cap, hOld, Nat.zero_add] using hCopy
    · have hMax : max 1 cap = 1 := Nat.max_eq_left (by omega)
      simpa only [ticks, ite_eq_right h, hMax, useOne, hOld, Nat.zero_add] using hInc
  have hLoad := runsValues_ifLess (lanes ∘ extentCompareLanes)
    (hLanes.comp extentCompareLanes_injective) copyCap useOne word before
    (hz .leftCopy (by decide)) (hz .rightCopy (by decide)) hScratch hRun
  change (loadOldCap lanes).RunsValues word (ifEqualTime (before (lanes .zero)) cap + ticks) before
    (setValue (lanes .oldCap) (max 1 cap) before) at hLoad
  rw [hz .zero (by decide)] at hLoad
  have hBound : ticks ≤ 5 * cap + 2 := by dsimp [ticks]; split <;> omega
  exact ⟨_, by unfold ifEqualTime; dsimp [cap] at *; omega, hLoad⟩

/-- Compute both layouts and validate the measured request extents without
reading circuit or certificate fields. -/
theorem runsValues_traceExtentRegister (lanes : TraceExtentLane → R)
    (hLanes : Function.Injective lanes) (word : BinaryWord) (before : R → Nat)
    (hZero : ∀ lane, lane ∉ traceExtentInputLanes → before (lanes lane) = 0) :
    ∃ ticks ≤ traceExtentRegisterCost (before (lanes .arity)) (before (lanes .cap))
        (before (lanes .bodyLength)) (before (lanes .candidateLength)),
      ∃ after : R → Nat, (traceExtentRegister lanes).RunsValues word ticks before after ∧
        TraceExtentRegisterResult lanes before after := by
  let arity := before (lanes .arity)
  let cap := before (lanes .cap)
  let oldCap := max 1 cap
  let oldLength := mergeWitnessLength arity oldCap
  let newLength := mergeWitnessLength arity cap
  let loaded := setValue (lanes .oldCap) oldCap before
  let layout := fun side ↦ lanes ∘ traceCircuitLayoutLanes side
  let shape := lanes ∘ traceShapeLanes
  have hNe {a b : TraceExtentLane} (h : a ≠ b) : lanes a ≠ lanes b := fun e ↦ h (hLanes e)
  have hLoadedKeep {lane : TraceExtentLane} (h : lane ≠ .oldCap) :
      loaded (lanes lane) = before (lanes lane) := setValue_other (hNe h) ..
  have hLoadedOld : loaded (lanes .oldCap) = oldCap := setValue_same ..
  have hLayoutKeep {side : Bool} {v u : R → Nat}
      (result : CircuitLayoutRegisterResult (layout side) v u) {lane : TraceExtentLane}
      (h : lane ∉ ([.bound side, .width side, .span side, .paddedLength side] :
        List TraceExtentLane)) : u (lanes lane) = v (lanes lane) := by
    exact result.frame _ (hNe fun e ↦ h (by simp [e, traceCircuitLayoutLanes]))
      (hNe fun e ↦ h (by simp [e, traceCircuitLayoutLanes]))
      (hNe fun e ↦ h (by simp [e, traceCircuitLayoutLanes]))
      (hNe fun e ↦ h (by simp [e, traceCircuitLayoutLanes]))
  have hNewZero (lane : CircuitLayoutLane) (ha : lane ≠ .arity) (hc : lane ≠ .cap) :
      loaded (layout false lane) = 0 := by
    cases lane
    · exact (ha rfl).elim
    · exact (hc rfl).elim
    all_goals
      rw [show layout false _ = lanes (traceCircuitLayoutLanes false _) from rfl, hLoadedKeep]
      · exact hZero _ (by simp [traceCircuitLayoutLanes, traceExtentInputLanes])
      · simp [traceCircuitLayoutLanes]
  obtain ⟨loadTicks, hLoadTime, hLoad⟩ := runsValues_loadOldCap lanes hLanes word before hZero
  obtain ⟨newTicks, hNewTime, newV, hNewRun, hNew⟩ :=
    runsValues_circuitLayoutRegister (layout false)
      (hLanes.comp (traceCircuitLayoutLanes_injective false)) word loaded hNewZero
  have hNewArity : loaded (layout false .arity) = arity := hLoadedKeep (by decide)
  have hNewCap : loaded (layout false .cap) = cap := hLoadedKeep (by decide)
  rw [hNewArity, hNewCap] at hNewTime
  have hOldZero (lane : CircuitLayoutLane) (ha : lane ≠ .arity) (hc : lane ≠ .cap) :
      newV (layout true lane) = 0 := by
    cases lane
    · exact (ha rfl).elim
    · exact (hc rfl).elim
    all_goals
      rw [show layout true _ = lanes (traceCircuitLayoutLanes true _) from rfl,
        hLayoutKeep hNew, hLoadedKeep]
      · exact hZero _ (by simp [traceCircuitLayoutLanes, traceExtentInputLanes])
      · simp [traceCircuitLayoutLanes]
      · simp [traceCircuitLayoutLanes]
  obtain ⟨oldTicks, hOldTime, oldV, hOldRun, hOld⟩ :=
    runsValues_circuitLayoutRegister (layout true)
      (hLanes.comp (traceCircuitLayoutLanes_injective true)) word newV hOldZero
  have hOldArity : newV (layout true .arity) = arity := hNew.arity.trans hNewArity
  have hOldCap : newV (layout true .cap) = oldCap :=
    (hLayoutKeep hNew (lane := .oldCap) (by decide)).trans hLoadedOld
  rw [hOldArity, hOldCap] at hOldTime
  have hKeep {lane : TraceExtentLane}
      (hn : lane ∉ ([.bound false, .width false, .span false, .paddedLength false] :
        List TraceExtentLane))
      (ho : lane ∉ ([.bound true, .width true, .span true, .paddedLength true] :
        List TraceExtentLane)) (hc : lane ≠ .oldCap) :
      oldV (lanes lane) = before (lanes lane) :=
    (hLayoutKeep hOld ho).trans ((hLayoutKeep hNew hn).trans (hLoadedKeep hc))
  have hShapeZero (lane : RequestShapeLane) (h :
      lane ∈ ([.minimum, .maximum, .prefixLength, .failures, .leftCopy, .rightCopy, .scratch] :
        List RequestShapeLane)) : oldV (shape lane) = 0 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact (hKeep (by decide) (by decide) (by decide)).trans (hZero _ (by decide))
  obtain ⟨shapeTicks, hShapeTime, after, hShapeRun, hShape⟩ :=
    runsValues_requestShapeRegister shape (hLanes.comp traceShapeLanes_injective)
      word oldV hShapeZero
  have hShapeArity : oldV (shape .arity) = arity := hOld.arity.trans hOldArity
  have hShapeBody : oldV (shape .bodyLength) = before (lanes .bodyLength) :=
    hKeep (by decide) (by decide) (by decide)
  have hShapeOld : oldV (shape .oldLength) = oldLength := by
    exact hOld.paddedLength.trans (by rw [hOldArity, hOldCap])
  have hShapeNew : oldV (shape .candidateWidth) = newLength :=
    (hLayoutKeep hOld (lane := .paddedLength false) (by decide)).trans
      (hNew.paddedLength.trans (by rw [hNewArity, hNewCap]))
  have hShapeCandidate : oldV (shape .candidateLength) = before (lanes .candidateLength) :=
    hKeep (by decide) (by decide) (by decide)
  rw [hShapeArity, hShapeBody, hShapeOld, hShapeNew, hShapeCandidate] at hShapeTime
  have hAfterKeep {lane : TraceExtentLane}
      (h : lane ∉ ([.minimum, .maximum, .prefixLength, .failures] : List TraceExtentLane)) :
      after (lanes lane) = oldV (lanes lane) := by
    exact hShape.frame _ (hNe fun e ↦ h (by simp [e, traceShapeLanes]))
      (hNe fun e ↦ h (by simp [e, traceShapeLanes]))
      (hNe fun e ↦ h (by simp [e, traceShapeLanes]))
      (hNe fun e ↦ h (by simp [e, traceShapeLanes]))
  have hMinimum := hShape.minimum
  rw [hShapeArity, hShapeOld] at hMinimum
  have hMaximum := hShape.maximum
  rw [hMinimum, hShapeNew] at hMaximum
  have hResult : TraceExtentRegisterResult lanes before after := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (hAfterKeep (by decide)).trans
        ((hLayoutKeep hOld (by decide)).trans hOldCap)
    · intro side
      cases side
      · change after (lanes (.width false)) = circuitFieldWidth arity cap
        exact (hAfterKeep (by decide)).trans ((hLayoutKeep hOld (by decide)).trans
          (hNew.width.trans (by rw [hNewArity, hNewCap])))
      · change after (lanes (.width true)) = circuitFieldWidth arity oldCap
        exact (hAfterKeep (by decide)).trans (hOld.width.trans (by rw [hOldArity, hOldCap]))
    · intro side
      cases side
      · have hWidth : after (lanes (.width false)) = newV (layout false .width) :=
          (hAfterKeep (by decide)).trans (hLayoutKeep hOld (by decide))
        rw [hWidth]
        exact (hAfterKeep (by decide)).trans ((hLayoutKeep hOld (by decide)).trans hNew.span)
      · have hWidth : after (lanes (.width true)) = oldV (layout true .width) :=
          hAfterKeep (by decide)
        rw [hWidth]
        exact (hAfterKeep (by decide)).trans hOld.span
    · intro side
      cases side
      · exact (hAfterKeep (by decide)).trans hShapeNew
      · exact (hAfterKeep (by decide)).trans hShapeOld
    · have hPref := hShape.prefixLength
      rw [hShapeBody, hMinimum] at hPref
      exact hPref
    · change after (shape .failures) ≤ 3
      rw [hShape.failures]
      have hBit (flag : Bool) : flag.toNat ≤ 1 := Bool.toNat_le flag
      exact Nat.add_le_add (Nat.add_le_add (hBit _) (hBit _)) (hBit _)
    · have hValid := hShape.valid
      rw [hShapeBody, hMinimum, hMaximum, hShapeCandidate, hShapeNew] at hValid
      exact hValid
    · intro lane hLane
      simp only [traceExtentInputLanes, List.mem_cons, List.not_mem_nil, or_false] at hLane
      rcases hLane with rfl | rfl | rfl | rfl
      all_goals exact (hAfterKeep (by decide)).trans (hKeep (by decide) (by decide) (by decide))
    · intro r h
      exact (hShape.frame r (h _) (h _) (h _) (h _)).trans
        ((hOld.frame r (h _) (h _) (h _) (h _)).trans
          ((hNew.frame r (h _) (h _) (h _) (h _)).trans (setValue_other (h _) ..)))
  exact ⟨_, Nat.add_le_add hLoadTime (Nat.add_le_add hNewTime (Nat.add_le_add hOldTime hShapeTime)),
    after, hLoad.seq (hNewRun.seq (hOldRun.seq hShapeRun)), hResult⟩

end PvsNP.MCSP
