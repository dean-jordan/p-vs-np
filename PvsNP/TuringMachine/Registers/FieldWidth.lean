module

public import PvsNP.TuringMachine.Registers.BinaryField
public import PvsNP.TuringMachine.Registers.LessThan

/-! # Compute the bit width of a unary register bound -/

public section

namespace PvsNP.RegisterMachine.Fragment

/-- The input and output registers and the work lanes for width computation. -/
inductive FieldWidthLane where
  | bound | width | power | counter | leftCopy | rightCopy | scratch
  deriving DecidableEq

private def widthCompareLanes : Fin 5 → FieldWidthLane
  | 0 => .bound
  | 1 => .power
  | 2 => .leftCopy
  | 3 => .rightCopy
  | _ => .scratch

private theorem widthCompareLanes_injective : Function.Injective widthCompareLanes := by decide

variable {R : Type}

private def prepareWidth (lanes : FieldWidthLane → R) : Fragment R :=
  ((add (lanes .bound) (lanes .counter) (lanes .scratch)).seq
    (incrementBy (lanes .width) 1)).seq (incrementBy (lanes .power) 2)

private def growWidth (lanes : FieldWidthLane → R) : Fragment R :=
  (pushRegisterBit (lanes .power) (lanes .leftCopy) (lanes .scratch) false).seq
    (incrementBy (lanes .width) 1)

private def widthIteration (lanes : FieldWidthLane → R) : Fragment R :=
  ifLess (lanes .bound) (lanes .power) (lanes .leftCopy) (lanes .rightCopy)
    (lanes .scratch) skip (growWidth lanes)

private def clearPower (lane : R) : Fragment R where
  Label := Unit
  entry := some ()
  code _ := .dec lane none (some ())

/-- Compute `log2 m + 1` in the initially empty width lane while preserving
`m` in the bound lane. All work lanes start and finish empty. -/
def fieldWidthRegister (lanes : FieldWidthLane → R) : Fragment R :=
  ((prepareWidth lanes).seq (countdown (lanes .counter) (widthIteration lanes))).seq
    (clearPower (lanes .power))

/-- A uniform instruction bound in the preserved unary bound. -/
@[expose] def fieldWidthRegisterCost (m : Nat) : Nat :=
  m * (40 * (m + 1) + 10) + 7 * (m + 1) + 6

theorem fieldWidthRegisterCost_polynomiallyBounded :
    PolynomiallyBounded fieldWidthRegisterCost := by
  have hSucc := PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)
  exact ((PolynomiallyBounded.id.mul (((PolynomiallyBounded.const 40).mul hSucc).add
    (PolynomiallyBounded.const 10))).add ((PolynomiallyBounded.const 7).mul hSucc)).add
      (PolynomiallyBounded.const 6)

private theorem pow_width_le (m width : Nat) (hWidth : width ≤ m.log2 + 1) :
    2 ^ width ≤ 2 * (m + 1) := by
  have hPow : 2 ^ width ≤ 2 ^ (m.log2 + 1) := Nat.pow_le_pow_right (by decide) hWidth
  by_cases hZero : m = 0
  · subst m
    have hTwo : 2 ^ ((0 : Nat).log2 + 1) = 2 * (0 + 1) := by decide
    rwa [← hTwo]
  · rw [Nat.pow_succ'] at hPow
    have hLog := Nat.log2_self_le hZero
    omega

private theorem guarded_width_eq_min (m k : Nat) (hPositive : 0 < k) (hWidth : k ≤ m.log2 + 1) :
    (if m < 2 ^ k then k else k + 1) = min (k + 1) (m.log2 + 1) := by
  by_cases hZero : m = 0
  · subst m
    have hK : k = 1 := by simp only [Nat.log2_zero, Nat.zero_add] at hWidth; omega
    simp [hK]
  · by_cases hSmall : m < 2 ^ k
    · have hLog := (Nat.log2_lt hZero).mpr hSmall
      rw [ite_eq_left hSmall, Nat.min_eq_right (by omega)]
      omega
    · have hLog := (Nat.le_log2 hZero).mpr (Nat.le_of_not_gt hSmall)
      rw [ite_eq_right hSmall, Nat.min_eq_left (by omega)]

variable [DecidableEq R]

private def widthValues (lanes : FieldWidthLane → R) (before : R → Nat)
    (remaining k : Nat) : R → Nat :=
  setValue (lanes .counter) remaining
    (setValue (lanes .width) k (setValue (lanes .power) (2 ^ k) before))

private theorem runsValues_prepareWidth (lanes : FieldWidthLane → R)
    (hLanes : Function.Injective lanes) (x : BinaryWord) (before : R → Nat)
    (hZero : ∀ lane, lane ≠ .bound → before (lanes lane) = 0) :
    (prepareWidth lanes).RunsValues x (5 * before (lanes .bound) + 5) before
      (widthValues lanes before (before (lanes .bound)) 1) := by
  have hDiff {u v : FieldWidthLane} (h : u ≠ v) : lanes u ≠ lanes v := fun e ↦ h (hLanes e)
  have hLane (u v : FieldWidthLane) : lanes u = lanes v ↔ u = v :=
    ⟨fun e ↦ hLanes e, congrArg lanes⟩
  let m := before (lanes .bound)
  let copied := setValue (lanes .counter) m before
  have hCopy : (add (lanes .bound) (lanes .counter) (lanes .scratch)).RunsValues
      x (5 * m + 2) before copied := by
    simpa only [hZero .counter (by decide), Nat.zero_add, copied] using
      runsValues_add (lanes .bound) (lanes .counter) (lanes .scratch) x before
        (hDiff (by decide)) (hDiff (by decide)) (hDiff (by decide)) (hZero .scratch (by decide))
  have hCopiedWidth : copied (lanes .width) = 0 := by
    simp [copied, setValue, hLane, hZero .width (by decide)]
  let widened := setValue (lanes .width) 1 copied
  have hWidth : (incrementBy (lanes .width) 1).RunsValues x 1 copied widened := by
    simpa only [hCopiedWidth, Nat.zero_add, widened] using
      runsValues_incrementBy (lanes .width) 1 x copied
  have hWidenedPower : widened (lanes .power) = 0 := by
    simp [widened, copied, setValue, hLane, hZero .power (by decide)]
  have hValues : setValue (lanes .power) 2 widened = widthValues lanes before m 1 := by
    funext r
    by_cases hc : r = lanes .counter <;> by_cases hw : r = lanes .width <;>
      by_cases hp : r = lanes .power <;> simp [widened, copied, widthValues, setValue, hc, hw, hp]
    all_goals subst r; simp_all
  have hPower := runsValues_incrementBy (lanes .power) 2 x widened
  have hTicks : 5 * m + 2 + 1 + 2 = 5 * m + 5 := by omega
  simpa only [prepareWidth, hWidenedPower, Nat.zero_add, hValues, hTicks] using
    (hCopy.seq hWidth).seq hPower

private theorem runsValues_widthIteration (lanes : FieldWidthLane → R)
    (hLanes : Function.Injective lanes) (x : BinaryWord) (before : R → Nat)
    (hZero : ∀ lane, lane ≠ .bound → before (lanes lane) = 0)
    (remaining k : Nat) (hPositive : 0 < k) (hWidth : k ≤ (before (lanes .bound)).log2 + 1) :
    let m := before (lanes .bound)
    ∃ ticks ≤ 40 * (m + 1) + 9, (widthIteration lanes).RunsValues x ticks
      (widthValues lanes before remaining k)
      (widthValues lanes before remaining (min (k + 1) (m.log2 + 1))) := by
  let m := before (lanes .bound)
  let operating := widthValues lanes before remaining k
  have hDiff {u v : FieldWidthLane} (h : u ≠ v) : lanes u ≠ lanes v := fun e ↦ h (hLanes e)
  have hLane (u v : FieldWidthLane) : lanes u = lanes v ↔ u = v :=
    ⟨fun e ↦ hLanes e, congrArg lanes⟩
  have hBound : operating (lanes .bound) = m :=
    by simp [operating, widthValues, setValue, hLane, m]
  have hPower : operating (lanes .power) = 2 ^ k :=
    by simp [operating, widthValues, setValue, hLane]
  have hWidthLane : operating (lanes .width) = k := by
    simp [operating, widthValues, setValue, hLane]
  have hClearLeft : operating (lanes .leftCopy) = 0 := by
    simp [operating, widthValues, setValue, hLane, hZero .leftCopy (by decide)]
  have hClearRight : operating (lanes .rightCopy) = 0 := by
    simp [operating, widthValues, setValue, hLane, hZero .rightCopy (by decide)]
  have hClearScratch : operating (lanes .scratch) = 0 := by
    simp [operating, widthValues, setValue, hLane, hZero .scratch (by decide)]
  have hNext := guarded_width_eq_min m k hPositive hWidth
  let after := widthValues lanes before remaining (min (k + 1) (m.log2 + 1))
  obtain ⟨bodyTicks, hBodyCost, hBody⟩ : ∃ ticks ≤ 11 * 2 ^ k + 6,
      RunsValues
        (if operating (lanes .bound) < operating (lanes .power) then skip else growWidth lanes)
        x ticks operating after := by
    by_cases hSmall : m < 2 ^ k
    · have hSame : after = operating := by
        simp only [ite_eq_left hSmall] at hNext
        simp only [after, operating, ← hNext]
      refine ⟨0, Nat.zero_le _, ?_⟩
      simpa only [hBound, hPower, ite_eq_left hSmall, hSame] using runsValues_skip x operating
    · have hFound : min (k + 1) (m.log2 + 1) = k + 1 := by
        simpa only [ite_eq_right hSmall] using hNext.symm
      let doubled := setValue (lanes .power) (2 * 2 ^ k) operating
      have hDouble := runsValues_pushRegisterBit (lanes .power) (lanes .leftCopy) (lanes .scratch)
        x operating false (hDiff (by decide)) (hDiff (by decide)) (hDiff (by decide))
        hClearLeft hClearScratch
      have hDoubledWidth : doubled (lanes .width) = k :=
        (setValue_other (hDiff (by decide)) ..).trans hWidthLane
      have hValues : setValue (lanes .width) (k + 1) doubled = after := by
        funext r
        by_cases hc : r = lanes .counter <;> by_cases hw : r = lanes .width <;>
          by_cases hp : r = lanes .power <;>
          simp [after, doubled, operating, widthValues, setValue, hFound, hc, hw, hp, Nat.pow_succ']
        all_goals subst r; simp_all
      have hDouble' : RunsValues
          (pushRegisterBit (lanes .power) (lanes .leftCopy) (lanes .scratch) false)
          x (11 * 2 ^ k + 5) operating doubled := by
        simpa only [hPower, pushBit, Bool.toNat_false, Nat.add_zero, doubled] using hDouble
      have hRun := hDouble'.seq (runsValues_incrementBy (lanes .width) 1 x doubled)
      exact ⟨11 * 2 ^ k + 6, le_rfl, by
        simpa only [growWidth, hBound, hPower, ite_eq_right hSmall, hDoubledWidth, hValues]
          using hRun⟩
  have hRun := runsValues_ifLess (lanes ∘ widthCompareLanes)
    (hLanes.comp widthCompareLanes_injective) skip (growWidth lanes) x operating
    hClearLeft hClearRight hClearScratch hBody
  refine ⟨ifEqualTime m (2 ^ k) + bodyTicks, ?_, ?_⟩
  · have hLimit := pow_width_le m k hWidth
    unfold ifEqualTime
    omega
  · simpa only [Function.comp_apply, widthCompareLanes, hBound, hPower, widthIteration] using hRun

private theorem runsValues_widthCountdown (lanes : FieldWidthLane → R)
    (hLanes : Function.Injective lanes) (x : BinaryWord) (before : R → Nat)
    (hZero : ∀ lane, lane ≠ .bound → before (lanes lane) = 0)
    (remaining k : Nat) (hPositive : 0 < k) (hWidth : k ≤ (before (lanes .bound)).log2 + 1) :
    let m := before (lanes .bound)
    ∃ ticks ≤ remaining * (40 * (m + 1) + 10) + 1,
      (countdown (lanes .counter) (widthIteration lanes)).RunsValues x ticks
        (widthValues lanes before remaining k)
        (widthValues lanes before 0 (min (k + remaining) (m.log2 + 1))) := by
  let m := before (lanes .bound)
  let limit := m.log2 + 1
  induction remaining generalizing k with
  | zero =>
    simp only [Nat.zero_mul, Nat.zero_add, Nat.add_zero, Nat.min_eq_left hWidth]
    refine ⟨1, le_rfl, ?_⟩
    intro output
    let frag := countdown (lanes .counter) (widthIteration lanes)
    let start := frag.enter (⟨none, widthValues lanes before 0 k, none, output⟩ : Config R Unit)
    exact run_countdown_zero (counter := lanes .counter) (body := widthIteration lanes)
      (cfg := start) rfl (setValue_same ..)
  | succ remaining ih =>
    let operating := widthValues lanes before (remaining + 1) k
    let tested := widthValues lanes before remaining k
    let next := min (k + 1) limit
    obtain ⟨bodyTicks, hBodyCost, hBody⟩ :=
      runsValues_widthIteration lanes hLanes x before hZero remaining k hPositive hWidth
    have hNextPositive : 0 < next := by dsimp only [next, limit]; omega
    have hNextBound : next ≤ limit := Nat.min_le_right ..
    obtain ⟨restTicks, hRestCost, hRest⟩ := ih next hNextPositive hNextBound
    have hFinally : min (next + remaining) limit = min (k + (remaining + 1)) limit := by
      dsimp only [next]
      omega
    have hTest : decrementValues (lanes .counter) operating = tested := by
      funext r
      by_cases h : r = lanes .counter <;>
        simp [operating, tested, widthValues, setValue, decrementValues, h]
    refine ⟨1 + bodyTicks + restTicks, ?_, ?_⟩
    · rw [Nat.succ_mul]
      omega
    · intro output
      let frag := countdown (lanes .counter) (widthIteration lanes)
      let cfg := frag.enter (⟨none, operating, none, output⟩ : Config R Unit)
      let mid := frag.enter
        (⟨none, widthValues lanes before remaining next, none, output⟩ : Config R Unit)
      have hCounter : 0 < cfg.values (lanes .counter) := by
        change 0 < operating (lanes .counter)
        simp [operating, widthValues]
      have hBody' : (widthIteration lanes).run x bodyTicks
          (countdownBodyStart (lanes .counter) (widthIteration lanes) cfg) =
          some ⟨some none, widthValues lanes before remaining next, none, output⟩ := by
        simpa only [cfg, countdownBodyStart, enter, hTest] using hBody output
      have hStep := run_countdown_iteration (counter := lanes .counter) (cfg := cfg)
        rfl hCounter hBody' rfl
      change RegisterMachine.run frag.close x (1 + bodyTicks) cfg = some mid at hStep
      change RegisterMachine.run frag.close x _ cfg = _
      rw [RegisterMachine.run_add, hStep, Option.bind_some]
      have hRest' := hRest output
      change RegisterMachine.run frag.close x restTicks mid =
        some ⟨some none, widthValues lanes before 0 (min (next + remaining) limit),
          none, output⟩ at hRest'
      rw [hFinally] at hRest'
      exact hRest'

private theorem runsValues_clearPower (lane : R) (x : BinaryWord) (before : R → Nat) :
    (clearPower lane).RunsValues x (before lane + 1) before (clearValues lane before) := by
  intro output
  exact run_clear x (program := (clearPower lane).close) rfl
    (cfg := (clearPower lane).enter (⟨none, before, none, output⟩ : Config R Unit)) rfl

/-- For every unary bound, including zero, compute the logarithmic width with
an exact normal run bounded by a quadratic polynomial. Only the width changes. -/
theorem runsValues_fieldWidthRegister (lanes : FieldWidthLane → R)
    (hLanes : Function.Injective lanes) (x : BinaryWord) (before : R → Nat)
    (hZero : ∀ lane, lane ≠ .bound → before (lanes lane) = 0) :
    let m := before (lanes .bound)
    ∃ ticks ≤ fieldWidthRegisterCost m, (fieldWidthRegister lanes).RunsValues x ticks before
      (setValue (lanes .width) (m.log2 + 1) before) := by
  let m := before (lanes .bound)
  let width := m.log2 + 1
  have hLane (u v : FieldWidthLane) : lanes u = lanes v ↔ u = v :=
    ⟨fun e ↦ hLanes e, congrArg lanes⟩
  have hInit := runsValues_prepareWidth lanes hLanes x before hZero
  have hLog := Nat.log2_le_self m
  have hLimit : min (1 + m) width = width := Nat.min_eq_right (by dsimp [width]; omega)
  obtain ⟨loopTicks, hLoopCost, hLoop⟩ :=
    runsValues_widthCountdown lanes hLanes x before hZero m 1 (by decide)
      (Nat.succ_le_succ (Nat.zero_le m.log2))
  rw [show min (1 + m) (m.log2 + 1) = width from hLimit] at hLoop
  let calculated := widthValues lanes before 0 width
  have hPower : calculated (lanes .power) = 2 ^ width := by
    simp [calculated, widthValues, setValue, hLane]
  have hClear := runsValues_clearPower (lanes .power) x calculated
  have hResult : clearValues (lanes .power) calculated = setValue (lanes .width) width before := by
    funext r
    by_cases hc : r = lanes .counter
    · subst r
      simp [calculated, widthValues, clearValues, setValue, hLane, hZero .counter (by decide)]
    by_cases hp : r = lanes .power
    · subst r
      simp [calculated, clearValues, setValue, hLane, hZero .power (by decide)]
    simp [calculated, widthValues, clearValues, setValue, hc, hp]
  have hTime := pow_width_le m width le_rfl
  refine ⟨5 * m + 5 + loopTicks + (2 ^ width + 1), ?_, ?_⟩
  · change 5 * m + 5 + loopTicks + (2 ^ width + 1) ≤ fieldWidthRegisterCost m
    change loopTicks ≤ m * (40 * (m + 1) + 10) + 1 at hLoopCost
    unfold fieldWidthRegisterCost
    omega
  · simpa only [fieldWidthRegister, m, hPower, hResult] using (hInit.seq hLoop).seq hClear

end PvsNP.RegisterMachine.Fragment
