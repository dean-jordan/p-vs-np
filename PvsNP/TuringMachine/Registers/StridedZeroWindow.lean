module

public import PvsNP.TuringMachine.Registers.StridedField

import Init.Data.List.Count

/-! # Check a strided window for zero padding

The scan counts one violation for each true bit or missing input position.
It advances through the window even after a violation, giving a fixed final
cursor and consuming the full width.
-/

public section

namespace PvsNP.RegisterMachine.Fragment

variable {R : Type}

private def paddingViolation : Option Bool → Bool
  | some false => false
  | _ => true

private def zeroWindowIteration (stride : Nat) (lanes : Fin 5 → R) : Fragment R :=
  readRegisterBitAdvance stride (lanes 0) (lanes 3) (lanes 4) fun bit ↦
    incrementBy (lanes 2) (paddingViolation bit).toNat

/-- Lane 0 contains the reverse position, lane 1 the width, and lane 2 the
violation count. Lanes 3 and 4 are scratch and start and finish at zero. -/
def stridedZeroWindow (stride : Nat) (lanes : Fin 5 → R) : Fragment R :=
  countdown (lanes 1) (zeroWindowIteration stride lanes)

/-- The maximum reverse position visited bounds each lookup. -/
@[expose] def stridedZeroWindowCost (stride positionCap width : Nat) : Nat :=
  width * (7 * positionCap + stride + 7) + 1

theorem stridedZeroWindowCost_polynomiallyBounded (stride : Nat)
    {positionCap width : Nat → Nat} (hPosition : PolynomiallyBounded positionCap)
    (hWidth : PolynomiallyBounded width) :
    PolynomiallyBounded (fun n ↦ stridedZeroWindowCost stride (positionCap n) (width n)) :=
  (hWidth.mul ((((PolynomiallyBounded.const 7).mul hPosition).add
    (PolynomiallyBounded.const stride)).add (PolynomiallyBounded.const 7))).add
    (PolynomiallyBounded.const 1)

/-- A complete window has zero violations exactly when every bit is zero. -/
theorem countTrue_eq_zero_iff_replicate_false (bits : BinaryWord) :
    bits.count true = 0 ↔ bits = List.replicate bits.length false := by
  induction bits with
  | nil => simp
  | cons bit bits ih => cases bit <;> simp [List.replicate_succ, ih]

/-- The violation indicator for each requested reverse position. -/
def stridedZeroViolations (x : BinaryWord) (start stride width : Nat) : BinaryWord :=
  List.ofFn fun i : Fin width ↦ paddingViolation x.reverse[start + stride * i.val]?

theorem count_stridedZeroViolations_eq_zero_iff (x : BinaryWord) (start stride width : Nat) :
    (stridedZeroViolations x start stride width).count true = 0 ↔
      ∀ i, i < width → x.reverse[start + stride * i]? = some false := by
  rw [List.count_eq_zero]
  constructor
  · intro h i hi
    have hNot : paddingViolation x.reverse[start + stride * i]? ≠ true := fun he ↦
      h (List.mem_ofFn.mpr ⟨⟨i, hi⟩, he⟩)
    cases hBit : x.reverse[start + stride * i]? with
    | none => simp [paddingViolation, hBit] at hNot
    | some bit => cases bit <;> simp [paddingViolation, hBit] at hNot ⊢
  · intro h hMem
    obtain ⟨i, he⟩ := List.mem_ofFn.mp hMem
    rw [h i.val i.isLt] at he
    cases he

variable [DecidableEq R]

private def zeroIterationValues (stride : Nat) (lanes : Fin 5 → R) (bad : Bool)
    (before : R → Nat) : R → Nat :=
  setValue (lanes 0) (before (lanes 0) + stride)
    (setValue (lanes 2) (before (lanes 2) + bad.toNat) before)

private theorem runsValues_zeroWindowIteration (stride : Nat) (lanes : Fin 5 → R)
    (hLanes : Function.Injective lanes) (x : BinaryWord) (before : R → Nat)
    (cap : Nat) (hPos : before (lanes 0) ≤ cap)
    (hIndex : before (lanes 3) = 0) (hWork : before (lanes 4) = 0) :
    let bad := paddingViolation x.reverse[before (lanes 0)]?
    ∃ ticks ≤ 7 * cap + stride + 6,
      (zeroWindowIteration stride lanes).RunsValues x ticks before
        (zeroIterationValues stride lanes bad before) := by
  have hDiff (i j : Fin 5) (h : i ≠ j) : lanes i ≠ lanes j := fun e ↦ h (hLanes e)
  let bad := paddingViolation x.reverse[before (lanes 0)]?
  have hBranch := runsValues_incrementBy (lanes 2) bad.toNat x before
  have hRead := runsValues_readRegisterBitAdvance stride (lanes 0) (lanes 3) (lanes 4)
    (fun bit ↦ incrementBy (lanes 2) (paddingViolation bit).toNat) x before
    (hDiff 0 3 (by decide)) (hDiff 0 4 (by decide)) (hDiff 3 4 (by decide)) hIndex hWork hBranch
  have hBefore : setValue (lanes 2) (before (lanes 2) + bad.toNat) before (lanes 0) =
      before (lanes 0) := setValue_other (hDiff 0 2 (by decide)) ..
  refine ⟨5 * before (lanes 0) + 2 + (inputAtCost (before (lanes 0)) x.length + bad.toNat) +
    stride, ?_, ?_⟩
  · have hCost := inputAtCost_le (before (lanes 0)) x.length
    have hBit := Bool.toNat_le bad
    omega
  · simpa only [zeroWindowIteration, zeroIterationValues, hBefore] using hRead

private theorem runsValues_stridedZeroWindow_badBits (stride : Nat) (lanes : Fin 5 → R)
    (hLanes : Function.Injective lanes) (x badBits : BinaryWord) (before : R → Nat)
    (cap : Nat) (hWidth : before (lanes 1) = badBits.length)
    (hIndex : before (lanes 3) = 0) (hWork : before (lanes 4) = 0)
    (hCap : ∀ i, i < badBits.length → before (lanes 0) + stride * i ≤ cap)
    (hRead : ∀ i, i < badBits.length →
      paddingViolation x.reverse[before (lanes 0) + stride * i]? = (badBits[i]?).getD false) :
    ∃ ticks ≤ stridedZeroWindowCost stride cap badBits.length, ∃ after : R → Nat,
      (stridedZeroWindow stride lanes).RunsValues x ticks before after ∧
      after (lanes 1) = 0 ∧ after (lanes 0) = before (lanes 0) + stride * badBits.length ∧
      after (lanes 2) = before (lanes 2) + badBits.count true ∧
      ∀ r, r ≠ lanes 0 → r ≠ lanes 1 → r ≠ lanes 2 → after r = before r := by
  let loop := stridedZeroWindow stride lanes
  have hLane (i j : Fin 5) : lanes i = lanes j ↔ i = j := ⟨fun e ↦ hLanes e, congrArg lanes⟩
  induction badBits generalizing before with
  | nil =>
    refine ⟨1, by simp [stridedZeroWindowCost], before, ?_, hWidth, by simp, by simp,
      fun _ _ _ _ ↦ rfl⟩
    intro output
    exact run_countdown_zero (body := zeroWindowIteration stride lanes) rfl hWidth
  | cons bit tail ih =>
    let tested := decrementValues (lanes 1) before
    have hTest (i : Fin 5) (hi : i ≠ 1) : tested (lanes i) = before (lanes i) := by
      simp [tested, decrementValues, hLane, hi]
    have hThisCap := hCap 0 (by simp)
    have hThisBit := hRead 0 (by simp)
    have hBit : paddingViolation x.reverse[tested (lanes 0)]? = bit := by
      simpa only [hTest 0 (by decide), Nat.mul_zero, Nat.add_zero, List.getElem?_cons_zero,
        Option.getD_some] using hThisBit
    obtain ⟨bodyTicks, hBodyCost, hBody⟩ := runsValues_zeroWindowIteration stride lanes hLanes
      x tested cap (by simpa only [hTest 0 (by decide), Nat.mul_zero, Nat.add_zero] using hThisCap)
      ((hTest 3 (by decide)).trans hIndex) ((hTest 4 (by decide)).trans hWork)
    rw [hBit] at hBody
    let advanced := zeroIterationValues stride lanes bit tested
    have hNextPos : advanced (lanes 0) = before (lanes 0) + stride := by
      simp [advanced, zeroIterationValues, hTest 0 (by decide)]
    have hNextWidth : advanced (lanes 1) = tail.length := by
      simp [advanced, zeroIterationValues, tested, decrementValues, setValue, hLane, hWidth]
    have hNextCount : advanced (lanes 2) = before (lanes 2) + bit.toNat := by
      simp [advanced, zeroIterationValues, setValue, hLane, hTest 2 (by decide)]
    have hNextIndex : advanced (lanes 3) = 0 := by
      simp [advanced, zeroIterationValues, setValue, hLane, hTest 3 (by decide), hIndex]
    have hNextWork : advanced (lanes 4) = 0 := by
      simp [advanced, zeroIterationValues, setValue, hLane, hTest 4 (by decide), hWork]
    have hShift (i : Nat) : advanced (lanes 0) + stride * i = before (lanes 0) + stride * (i + 1) :=
      by rw [hNextPos, Nat.mul_succ]; omega
    obtain ⟨tailTicks, hTailCost, after, hTail, hDone, hPos, hCount, hFrame⟩ :=
      ih advanced hNextWidth hNextIndex hNextWork
        (fun i hi ↦ by rw [hShift]; exact hCap (i + 1) (by simpa using hi))
        (fun i hi ↦ by rw [hShift]; exact hRead (i + 1) (by simpa using hi))
    refine ⟨1 + bodyTicks + tailTicks, ?_, after, ?_, hDone, ?_, ?_, ?_⟩
    · rw [stridedZeroWindowCost, List.length_cons, Nat.succ_mul]
      unfold stridedZeroWindowCost at hTailCost
      omega
    · intro output
      let start := loop.enter (⟨none, before, none, output⟩ : Config R Unit)
      let mid := loop.enter (⟨none, advanced, none, output⟩ : Config R Unit)
      have hMore : 0 < before (lanes 1) := by rw [hWidth]; simp
      have hStep := run_countdown_iteration (counter := lanes 1) (cfg := start)
        rfl hMore (hBody output) rfl
      change RegisterMachine.run loop.close x (1 + bodyTicks) start = some mid at hStep
      change RegisterMachine.run loop.close x _ start = _
      rw [RegisterMachine.run_add, hStep, Option.bind_some]
      exact hTail output
    · rw [hPos, hNextPos, List.length_cons, Nat.mul_succ]
      omega
    · rw [hCount, hNextCount]
      cases bit with
      | false => simp
      | true =>
        simp only [Bool.toNat_true, List.count_cons_self]
        omega
    · intro r hp hw hc
      rw [hFrame r hp hw hc]
      simp [advanced, zeroIterationValues, tested, decrementValues, setValue, hp, hw, hc]

/-- On a prepared window, count exactly its true bits using an input-length bound. -/
theorem runsValues_stridedZeroWindow_of_reads (stride : Nat) (lanes : Fin 5 → R)
    (hLanes : Function.Injective lanes) (x bits : BinaryWord) (before : R → Nat)
    (hWidth : before (lanes 1) = bits.length) (hIndex : before (lanes 3) = 0)
    (hWork : before (lanes 4) = 0)
    (hRead : ∀ i, i < bits.length → x.reverse[before (lanes 0) + stride * i]? = bits[i]?) :
    ∃ ticks ≤ stridedZeroWindowCost stride x.length bits.length, ∃ after : R → Nat,
      (stridedZeroWindow stride lanes).RunsValues x ticks before after ∧
      after (lanes 1) = 0 ∧ after (lanes 0) = before (lanes 0) + stride * bits.length ∧
      after (lanes 2) = before (lanes 2) + bits.count true ∧
      ∀ r, r ≠ lanes 0 → r ≠ lanes 1 → r ≠ lanes 2 → after r = before r := by
  refine runsValues_stridedZeroWindow_badBits stride lanes hLanes x bits before x.length
    hWidth hIndex hWork ?_ ?_
  · intro i hi
    have hSome := (hRead i hi).trans (List.getElem?_eq_getElem hi)
    have hIn := (List.getElem?_eq_some_iff.mp hSome).choose
    simpa only [List.length_reverse] using hIn.le
  · intro i hi
    rw [hRead i hi, List.getElem?_eq_getElem hi]
    cases bits[i] <;> rfl

/-- Check an arbitrary indexed window, including requests that extend past the input. -/
theorem runsValues_stridedZeroWindow (stride : Nat) (lanes : Fin 5 → R)
    (hLanes : Function.Injective lanes) (x : BinaryWord) (start width : Nat) (before : R → Nat)
    (hStart : before (lanes 0) = start) (hWidth : before (lanes 1) = width)
    (hIndex : before (lanes 3) = 0) (hWork : before (lanes 4) = 0) :
    ∃ ticks ≤ stridedZeroWindowCost stride (start + stride * width) width, ∃ after : R → Nat,
      (stridedZeroWindow stride lanes).RunsValues x ticks before after ∧ after (lanes 1) = 0 ∧
      after (lanes 0) = start + stride * width ∧
      after (lanes 2) = before (lanes 2) + (stridedZeroViolations x start stride width).count true ∧
      ∀ r, r ≠ lanes 0 → r ≠ lanes 1 → r ≠ lanes 2 → after r = before r := by
  let badBits := stridedZeroViolations x start stride width
  have hLen : badBits.length = width := List.length_ofFn
  have hCap (i : Nat) (hi : i < badBits.length) :
      before (lanes 0) + stride * i ≤ start + stride * width := by
    rw [hLen] at hi
    rw [hStart]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hi.le) _
  have hMatches (i : Nat) (hi : i < badBits.length) :
      paddingViolation x.reverse[before (lanes 0) + stride * i]? = (badBits[i]?).getD false := by
    rw [hLen] at hi
    simp only [hStart, badBits, stridedZeroViolations, List.getElem?_ofFn, dite_eq_left hi,
      Option.getD_some]
  simpa only [hLen, hStart, badBits] using
    runsValues_stridedZeroWindow_badBits stride lanes hLanes x badBits before
      (start + stride * width) (hWidth.trans hLen.symm) hIndex hWork hCap hMatches

end PvsNP.RegisterMachine.Fragment
