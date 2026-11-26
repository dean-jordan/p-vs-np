module

public import PvsNP.MCSP.MergeSearch
public import PvsNP.TuringMachine.Registers.Affine
public import PvsNP.TuringMachine.Registers.FieldWidth

/-! # Register arithmetic for a padded circuit description -/

public section

namespace PvsNP.MCSP

open Circuits RegisterMachine RegisterMachine.Fragment

/-- The input, output and temporary registers used by the layout calculation. -/
inductive CircuitLayoutLane where
  | arity | cap | bound | width | span | paddedLength
  | power | counter | leftCopy | rightCopy | scratch
  deriving DecidableEq

private def layoutWidthLanes : FieldWidthLane → CircuitLayoutLane
  | .bound => .bound
  | .width => .width
  | .power => .power
  | .counter => .counter
  | .leftCopy => .leftCopy
  | .rightCopy => .rightCopy
  | .scratch => .scratch

private theorem layoutWidthLanes_injective : Function.Injective layoutWidthLanes := by
  intro a b h
  cases a <;> cases b <;> simp_all [layoutWidthLanes]

variable {R : Type}

/-- Compute the wire bound, field width, gate record span, and padded length. -/
def circuitLayoutRegister (lanes : CircuitLayoutLane → R) : Fragment R :=
  let sum := (add (lanes .arity) (lanes .bound) (lanes .scratch)).seq
    (add (lanes .cap) (lanes .bound) (lanes .scratch))
  let width := fieldWidthRegister (lanes ∘ layoutWidthLanes)
  let span := accumulateAffine (lanes .width) (lanes .span) (lanes .counter) (lanes .scratch) 2 3
  let header := accumulateAffine (lanes .width) (lanes .paddedLength)
    (lanes .counter) (lanes .scratch) 2 0
  let copyCap := add (lanes .cap) (lanes .counter) (lanes .scratch)
  let product := multiply (lanes .counter) (lanes .span) (lanes .paddedLength) (lanes .scratch)
  ((((sum.seq width).seq span).seq header).seq copyCap).seq product

@[expose] def circuitLayoutRegisterCost (arity cap : Nat) : Nat :=
  let w := circuitFieldWidth arity cap
  (5 * arity + 2) + (5 * cap + 2) + fieldWidthRegisterCost (arity + cap) +
    affineTime 2 3 w + affineTime 2 0 w + (5 * cap + 2) +
    (cap * (5 * (3 + 2 * w) + 3) + 1)

theorem circuitLayoutRegisterCost_polynomiallyBounded {arity cap : Nat → Nat}
    (hArity : PolynomiallyBounded arity) (hCap : PolynomiallyBounded cap) :
    PolynomiallyBounded (fun n ↦ circuitLayoutRegisterCost (arity n) (cap n)) := by
  let lit := PolynomiallyBounded.const
  have hSum := hArity.add hCap
  have hWidth : PolynomiallyBounded (fun n ↦ circuitFieldWidth (arity n) (cap n)) :=
    (hSum.add (lit 1)).mono fun n ↦ Nat.add_le_add_right (Nat.log2_le_self _) 1
  have hSpan := (lit 3).add ((lit 2).mul hWidth)
  have hProduct := (hCap.mul (((lit 5).mul hSpan).add (lit 3))).add (lit 1)
  have hCopyArity := ((lit 5).mul hArity).add (lit 2)
  have hCopyCap := ((lit 5).mul hCap).add (lit 2)
  exact (((((hCopyArity.add hCopyCap).add
    (fieldWidthRegisterCost_polynomiallyBounded.comp hSum)).add
    (affineTime_polynomiallyBounded 2 3 hWidth)).add
    (affineTime_polynomiallyBounded 2 0 hWidth)).add hCopyCap).add hProduct

/-- The four computed values, the preserved inputs and the register frame. -/
structure CircuitLayoutRegisterResult (lanes : CircuitLayoutLane → R) (before after : R → Nat) :
    Prop where
  arity : after (lanes .arity) = before (lanes .arity)
  cap : after (lanes .cap) = before (lanes .cap)
  bound : after (lanes .bound) = before (lanes .arity) + before (lanes .cap)
  width : after (lanes .width) = circuitFieldWidth (before (lanes .arity)) (before (lanes .cap))
  span : after (lanes .span) = 3 + 2 * after (lanes .width)
  paddedLength : after (lanes .paddedLength) =
    mergeWitnessLength (before (lanes .arity)) (before (lanes .cap))
  frame : ∀ r, r ≠ lanes .bound → r ≠ lanes .width → r ≠ lanes .span →
    r ≠ lanes .paddedLength → after r = before r

variable [DecidableEq R]

/-- The calculation works for all unary inputs, including a zero gate cap. -/
theorem runsValues_circuitLayoutRegister (lanes : CircuitLayoutLane → R)
    (hLanes : Function.Injective lanes) (x : BinaryWord) (before : R → Nat)
    (hZero : ∀ lane, lane ≠ .arity → lane ≠ .cap → before (lanes lane) = 0) :
    ∃ ticks ≤ circuitLayoutRegisterCost (before (lanes .arity)) (before (lanes .cap)),
      ∃ after : R → Nat, (circuitLayoutRegister lanes).RunsValues x ticks before after ∧
        CircuitLayoutRegisterResult lanes before after := by
  let arity := before (lanes .arity)
  let cap := before (lanes .cap)
  let w := circuitFieldWidth arity cap
  let span := 3 + 2 * w
  have hNe {a b : CircuitLayoutLane} (h : a ≠ b) : lanes a ≠ lanes b := fun e ↦ h (hLanes e)
  have hLane (a b : CircuitLayoutLane) : lanes a = lanes b ↔ a = b :=
    ⟨fun e ↦ hLanes e, congrArg lanes⟩
  let addedArity := setValue (lanes .bound) arity before
  let summed := setValue (lanes .bound) (arity + cap) before
  have hAddArity : (add (lanes .arity) (lanes .bound) (lanes .scratch)).RunsValues
      x (5 * arity + 2) before addedArity := by
    simpa only [hZero .bound (by decide) (by decide), Nat.zero_add, addedArity, arity] using
      runsValues_add (lanes .arity) (lanes .bound) (lanes .scratch) x before
        (hNe (by decide)) (hNe (by decide)) (hNe (by decide))
        (hZero .scratch (by decide) (by decide))
  have hAddCap : (add (lanes .cap) (lanes .bound) (lanes .scratch)).RunsValues
      x (5 * cap + 2) addedArity summed := by
    have hCap := setValue_other (hNe (by decide : CircuitLayoutLane.cap ≠ .bound)) arity before
    have hScratch : addedArity (lanes .scratch) = 0 :=
      (setValue_other (hNe (by decide)) ..).trans (hZero .scratch (by decide) (by decide))
    simpa only [addedArity, hCap, cap, setValue_same, setValue_replace, summed] using
      runsValues_add (lanes .cap) (lanes .bound) (lanes .scratch) x addedArity
        (hNe (by decide)) (hNe (by decide)) (hNe (by decide)) hScratch
  have hSummedZero (r : CircuitLayoutLane) (ha : r ≠ .arity) (hc : r ≠ .cap)
      (hb : r ≠ .bound) : summed (lanes r) = 0 :=
    (setValue_other (hNe hb) ..).trans (hZero r ha hc)
  let widthLanes := lanes ∘ layoutWidthLanes
  have hWidthZero (r : FieldWidthLane) (hr : r ≠ .bound) : summed (widthLanes r) = 0 := by
    apply hSummedZero
    · cases r <;> decide
    · cases r <;> decide
    · cases r <;> simp_all [layoutWidthLanes]
  obtain ⟨widthTicks, hWidthCost, hWidthRun⟩ :=
    runsValues_fieldWidthRegister widthLanes (hLanes.comp layoutWidthLanes_injective)
      x summed hWidthZero
  have hSum : summed (lanes .bound) = arity + cap := setValue_same ..
  rw [show summed (widthLanes .bound) = arity + cap from hSum] at hWidthCost
  let widened := setValue (lanes .width) w summed
  have hWidthRun' : (fieldWidthRegister widthLanes).RunsValues x widthTicks summed widened := by
    simpa only [hSum, widened, w, circuitFieldWidth, widthLanes, Function.comp_apply,
      layoutWidthLanes] using hWidthRun
  have hWidenedWidth : widened (lanes .width) = w := setValue_same ..
  have hWidenedZero (r : CircuitLayoutLane) (ha : r ≠ .arity) (hc : r ≠ .cap)
      (hb : r ≠ .bound) (hw : r ≠ .width) : widened (lanes r) = 0 :=
    (setValue_other (hNe hw) ..).trans (hSummedZero r ha hc hb)
  have hSpanLanes : [lanes .width, lanes .span, lanes .counter, lanes .scratch].Nodup :=
    ((by decide : ([.width, .span, .counter, .scratch] : List CircuitLayoutLane).Nodup)).map hLanes
  let spanned := setValue (lanes .span) span widened
  have hSpanRun : (accumulateAffine (lanes .width) (lanes .span) (lanes .counter)
      (lanes .scratch) 2 3).RunsValues x (affineTime 2 3 w) widened spanned := by
    have hRun := runsValues_accumulateAffine (lanes .width) (lanes .span) (lanes .counter)
      (lanes .scratch) 2 3 x widened hSpanLanes
      (hWidenedZero .counter (by decide) (by decide) (by decide) (by decide))
      (hWidenedZero .scratch (by decide) (by decide) (by decide) (by decide))
    simpa only [hWidenedWidth, hWidenedZero .span (by decide) (by decide) (by decide) (by decide),
      Nat.zero_add, spanned, span, Nat.add_comm] using hRun
  have hSpannedWidth : spanned (lanes .width) = w :=
    (setValue_other (hNe (by decide)) ..).trans hWidenedWidth
  have hSpannedZero (r : CircuitLayoutLane) (ha : r ≠ .arity) (hc : r ≠ .cap)
      (hb : r ≠ .bound) (hw : r ≠ .width) (hs : r ≠ .span) : spanned (lanes r) = 0 :=
    (setValue_other (hNe hs) ..).trans (hWidenedZero r ha hc hb hw)
  have hHeaderLanes : [lanes .width, lanes .paddedLength, lanes .counter, lanes .scratch].Nodup :=
    ((by decide : ([.width, .paddedLength, .counter, .scratch] :
      List CircuitLayoutLane).Nodup)).map hLanes
  let headed := setValue (lanes .paddedLength) (2 * w) spanned
  have hHeaderRun : (accumulateAffine (lanes .width) (lanes .paddedLength) (lanes .counter)
      (lanes .scratch) 2 0).RunsValues x (affineTime 2 0 w) spanned headed := by
    have hRun := runsValues_accumulateAffine (lanes .width) (lanes .paddedLength) (lanes .counter)
      (lanes .scratch) 2 0 x spanned hHeaderLanes
      (hSpannedZero .counter (by decide) (by decide) (by decide) (by decide) (by decide))
      (hSpannedZero .scratch (by decide) (by decide) (by decide) (by decide) (by decide))
    simpa only [hSpannedWidth, hSpannedZero .paddedLength (by decide) (by decide) (by decide)
      (by decide) (by decide), Nat.zero_add, Nat.add_zero, headed] using hRun
  have hHeaderCap : headed (lanes .cap) = cap := by
    simp [headed, spanned, widened, summed, setValue, hLane, cap]
  have hHeaderCounter : headed (lanes .counter) = 0 := by
    simp [headed, spanned, widened, summed, setValue, hLane,
      hZero .counter (by decide) (by decide)]
  have hHeaderScratch : headed (lanes .scratch) = 0 := by
    simp [headed, spanned, widened, summed, setValue, hLane,
      hZero .scratch (by decide) (by decide)]
  let copied := setValue (lanes .counter) cap headed
  have hCopy : (add (lanes .cap) (lanes .counter) (lanes .scratch)).RunsValues
      x (5 * cap + 2) headed copied := by
    simpa only [hHeaderCap, hHeaderCounter, Nat.zero_add, copied] using
      runsValues_add (lanes .cap) (lanes .counter) (lanes .scratch) x headed
        (hNe (by decide)) (hNe (by decide)) (hNe (by decide)) hHeaderScratch
  have hCopiedCap : copied (lanes .counter) = cap := setValue_same ..
  have hCopiedSpan : copied (lanes .span) = span := by
    simp [copied, headed, spanned, setValue, hLane]
  have hCopiedLength : copied (lanes .paddedLength) = 2 * w := by
    simp [copied, headed, setValue, hLane]
  have hCopiedScratch : copied (lanes .scratch) = 0 :=
    (setValue_other (hNe (by decide)) ..).trans hHeaderScratch
  have hClear : setValue (lanes .counter) 0 copied = headed := by
    rw [show copied = setValue (lanes .counter) cap headed by rfl, setValue_replace,
      ← hHeaderCounter, setValue_current]
  let after := setValue (lanes .paddedLength) (mergeWitnessLength arity cap) headed
  have hMultiply : (multiply (lanes .counter) (lanes .span) (lanes .paddedLength)
      (lanes .scratch)).RunsValues x (cap * (5 * span + 3) + 1) copied after := by
    simpa only [hCopiedCap, hCopiedSpan, hCopiedLength, hClear, after, mergeWitnessLength,
      w, span] using runsValues_multiply (lanes .counter) (lanes .span) (lanes .paddedLength)
        (lanes .scratch) x copied (hNe (by decide)) (hNe (by decide)) (hNe (by decide))
        (hNe (by decide)) (hNe (by decide)) (hNe (by decide)) hCopiedScratch
  have hAll := (((((hAddArity.seq hAddCap).seq hWidthRun').seq hSpanRun).seq hHeaderRun).seq
    hCopy).seq hMultiply
  refine ⟨_, ?_, after, hAll, ?_⟩
  · unfold circuitLayoutRegisterCost
    exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add_right (Nat.add_le_add_left hWidthCost _) _) _) _) _
  · have hFrame (r : R) (hb : r ≠ lanes .bound) (hw : r ≠ lanes .width)
        (hs : r ≠ lanes .span) (hl : r ≠ lanes .paddedLength) : after r = before r := by
      simp [after, headed, spanned, widened, summed, setValue, hb, hw, hs, hl]
    have hWidth' : after (lanes .width) = w := by
      simp [after, headed, spanned, widened, setValue, hLane]
    refine ⟨hFrame _ (hNe (by decide)) (hNe (by decide)) (hNe (by decide)) (hNe (by decide)),
      hFrame _ (hNe (by decide)) (hNe (by decide)) (hNe (by decide)) (hNe (by decide)),
      ?_, hWidth', ?_, setValue_same .., hFrame⟩
    · simp [after, headed, spanned, widened, summed, setValue, hLane, arity, cap]
    · rw [hWidth']
      simp [after, headed, spanned, setValue, hLane, span]

end PvsNP.MCSP
