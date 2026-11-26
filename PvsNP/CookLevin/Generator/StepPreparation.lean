module

public import PvsNP.CookLevin.Generator.NameRegister
public import PvsNP.CookLevin.Generator.PreparedField

/-! # Register setup for the current and next tableau row -/

@[expose] public section

namespace PvsNP.CookLevin

open RegisterMachine RegisterMachine.Fragment

/-- Persistent coordinates, the six name bases, and temporary registers. -/
inductive StepPreparationLane where
  | time | stride | width
  | stateBase | headBase | cellBase | nextStateBase | nextHeadBase | nextCellBase
  | multiplier | scratch
  deriving DecidableEq

/-- The register roles are pairwise distinct. -/
abbrev StepPreparationLanes (R : Type) := StepPreparationLane ↪ R

variable {R : Type} (lanes : StepPreparationLanes R)

local notation "T" => lanes StepPreparationLane.time
local notation "D" => lanes StepPreparationLane.stride
local notation "W" => lanes StepPreparationLane.width
local notation "SB" => lanes StepPreparationLane.stateBase
local notation "HB" => lanes StepPreparationLane.headBase
local notation "CB" => lanes StepPreparationLane.cellBase
local notation "SN" => lanes StepPreparationLane.nextStateBase
local notation "HN" => lanes StepPreparationLane.nextHeadBase
local notation "CN" => lanes StepPreparationLane.nextCellBase
local notation "M" => lanes StepPreparationLane.multiplier
local notation "A" => lanes StepPreparationLane.scratch

/-- The base and work registers must start empty. -/
structure StepPreparationReady (v : R → Nat) : Prop where
  stateBase : v SB = 0
  headBase : v HB = 0
  cellBase : v CB = 0
  nextStateBase : v SN = 0
  nextHeadBase : v HN = 0
  nextCellBase : v CN = 0
  multiplier : v M = 0
  scratch : v A = 0

/-- Compute both rows' bases from one multiplication by the stride. -/
def stepPreparationFragment (states : Nat) : Fragment R :=
  let currentState := accumulateName T D SB M A
  let currentHead := (add SB HB A).seq (incrementBy HB states)
  let currentCell := (add HB CB A).seq (add W CB A)
  let nextState := (add SB SN A).seq (add D SN A)
  let nextHead := (add SN HN A).seq (incrementBy HN states)
  let nextCell := (add HN CN A).seq (add W CN A)
  (((((currentState.seq currentHead).seq currentCell).seq nextState).seq nextHead).seq nextCell)

/-- Clear the prepared bases in reverse order, preserving the output. -/
def stepCleanupFragment : Fragment R :=
  (((((clear CN).seq (clear HN)).seq (clear SN)).seq (clear CB)).seq (clear HB)).seq (clear SB)

/-- Exact cost of preparing the bases. -/
def stepPreparationTime (time stride width states : Nat) : Nat :=
  let current := time * stride
  let next := (time + 1) * stride
  accumulateNameTime time stride + ((5 * current + 2) + states) +
    ((5 * (current + states) + 2) + (5 * width + 2)) +
    ((5 * current + 2) + (5 * stride + 2)) + ((5 * next + 2) + states) +
    ((5 * (next + states) + 2) + (5 * width + 2))

/-- Exact cost of clearing all six bases. -/
def stepCleanupTime (time stride width states : Nat) : Nat :=
  let current := time * stride
  let next := (time + 1) * stride
  (next + states + width + 1) + (next + states + 1) + (next + 1) +
    (current + states + width + 1) + (current + states + 1) + (current + 1)

theorem stepPreparationTime_mono_time (stride width states : Nat) {time upper : Nat}
    (h : time ≤ upper) :
    stepPreparationTime time stride width states ≤
      stepPreparationTime upper stride width states := by
  have hCurrent := Nat.mul_le_mul_right stride h
  have hNext := Nat.mul_le_mul_right stride (Nat.add_le_add_right h 1)
  have hName := Nat.mul_le_mul_right (5 * stride + 3) h
  simp only [stepPreparationTime, accumulateNameTime]
  omega

theorem stepCleanupTime_mono_time (stride width states : Nat) {time upper : Nat}
    (h : time ≤ upper) :
    stepCleanupTime time stride width states ≤ stepCleanupTime upper stride width states := by
  have hCurrent := Nat.mul_le_mul_right stride h
  have hNext := Nat.mul_le_mul_right stride (Nat.add_le_add_right h 1)
  simp only [stepCleanupTime]
  omega

theorem stepPreparationTime_polynomiallyBounded {time stride width : Nat → Nat}
    (hTime : PolynomiallyBounded time) (hStride : PolynomiallyBounded stride)
    (hWidth : PolynomiallyBounded width) (states : Nat) :
    PolynomiallyBounded (fun n ↦ stepPreparationTime (time n) (stride n) (width n) states) := by
  let lit := PolynomiallyBounded.const
  have hAdd {f : Nat → Nat} (h : PolynomiallyBounded f) :
      PolynomiallyBounded (fun n ↦ 5 * f n + 2) := ((lit 5).mul h).add (lit 2)
  have hCurrent := hTime.mul hStride
  have hNext := (hTime.add (lit 1)).mul hStride
  have hInit := accumulateNameTime_polynomiallyBounded hTime hStride
  have hHead := (hAdd hCurrent).add (lit states)
  have hCell := (hAdd (hCurrent.add (lit states))).add (hAdd hWidth)
  have hNextState := (hAdd hCurrent).add (hAdd hStride)
  have hNextHead := (hAdd hNext).add (lit states)
  have hNextCell := (hAdd (hNext.add (lit states))).add (hAdd hWidth)
  exact ((((hInit.add hHead).add hCell).add hNextState).add hNextHead).add hNextCell

theorem stepCleanupTime_polynomiallyBounded {time stride width : Nat → Nat}
    (hTime : PolynomiallyBounded time) (hStride : PolynomiallyBounded stride)
    (hWidth : PolynomiallyBounded width) (states : Nat) :
    PolynomiallyBounded (fun n ↦ stepCleanupTime (time n) (stride n) (width n) states) := by
  let lit := PolynomiallyBounded.const
  have hCurrent := hTime.mul hStride
  have hNext := (hTime.add (lit 1)).mul hStride
  have hHead := hCurrent.add (lit states)
  have hNextHead := hNext.add (lit states)
  have hCurrentCell := (hHead.add hWidth).add (lit 1)
  have hNextCell := (hNextHead.add hWidth).add (lit 1)
  exact ((((hNextCell.add (hNextHead.add (lit 1))).add (hNext.add (lit 1))).add
    hCurrentCell).add (hHead.add (lit 1))).add (hCurrent.add (lit 1))

variable [DecidableEq R]

/-- The prepared valuation, with only the six named bases changed. -/
def stepPreparationValues (v : R → Nat) (states : Nat) : R → Nat :=
  let current := v T * v D
  let next := (v T + 1) * v D
  setValue CN (next + states + v W)
    (setValue HN (next + states)
      (setValue SN next
        (setValue CB (current + states + v W)
          (setValue HB (current + states) (setValue SB current v)))))

private theorem setLane_apply (source target : StepPreparationLane) (n : Nat) (v : R → Nat) :
    setValue (lanes source) n v (lanes target) =
      if target = source then n else v (lanes target) := by
  simp [setValue, lanes.injective.eq_iff]

theorem stepPreparationValues_at (v : R → Nat) (states : Nat) (lane : StepPreparationLane) :
    stepPreparationValues lanes v states (lanes lane) =
      match lane with
      | .stateBase => v T * v D
      | .headBase => v T * v D + states
      | .cellBase => v T * v D + states + v W
      | .nextStateBase => (v T + 1) * v D
      | .nextHeadBase => (v T + 1) * v D + states
      | .nextCellBase => (v T + 1) * v D + states + v W
      | _ => v (lanes lane) := by
  cases lane <;> simp [stepPreparationValues, setLane_apply]

theorem stepPreparationValues_other (v : R → Nat) (states : Nat) (r : R)
    (hState : r ≠ SB) (hHead : r ≠ HB) (hCell : r ≠ CB)
    (hNextState : r ≠ SN) (hNextHead : r ≠ HN) (hNextCell : r ≠ CN) :
    stepPreparationValues lanes v states r = v r := by
  simp [stepPreparationValues, setValue, hState, hHead, hCell, hNextState, hNextHead, hNextCell]

private theorem runsValues_copyInc (source target scratch : R) (amount : Nat) (x : BinaryWord)
    (v : R → Nat) (hST : source ≠ target) (hSA : source ≠ scratch) (hTA : target ≠ scratch)
    (hTarget : v target = 0) (hScratch : v scratch = 0) :
    ((add source target scratch).seq (incrementBy target amount)).RunsValues x
      ((5 * v source + 2) + amount) v (setValue target (v source + amount) v) := by
  have hCopy := runsValues_add source target scratch x v hST hSA hTA hScratch
  simp only [hTarget, Nat.zero_add] at hCopy
  have hAdd := runsValues_incrementBy target amount x (setValue target (v source) v)
  rw [setValue_same, setValue_replace] at hAdd
  exact hCopy.seq hAdd

private theorem runsValues_copyAdd (source extra target scratch : R) (x : BinaryWord)
    (v : R → Nat) (hST : source ≠ target) (hSA : source ≠ scratch) (hTA : target ≠ scratch)
    (hET : extra ≠ target) (hEA : extra ≠ scratch)
    (hTarget : v target = 0) (hScratch : v scratch = 0) :
    ((add source target scratch).seq (add extra target scratch)).RunsValues x
      ((5 * v source + 2) + (5 * v extra + 2)) v (setValue target (v source + v extra) v) := by
  have hCopy := runsValues_add source target scratch x v hST hSA hTA hScratch
  rw [hTarget, Nat.zero_add] at hCopy
  have hSecond := runsValues_add extra target scratch x (setValue target (v source) v)
    hET hEA hTA (by simpa only [setValue_other hTA.symm] using hScratch)
  rw [setValue_same, setValue_other hET, setValue_replace] at hSecond
  exact hCopy.seq hSecond

private theorem runsValues_stateBase (x : BinaryWord) (v : R → Nat)
    (hReady : StepPreparationReady lanes v) :
    (accumulateName T D SB M A).RunsValues x (accumulateNameTime (v T) (v D)) v
      (setValue SB (v T * v D) v) := by
  intro output
  let cfg : Config R Unit := ⟨none, v, none, output⟩
  have hDistinct : [T, D, SB, M, A].Nodup := List.Nodup.map lanes.injective
    (by decide : [StepPreparationLane.time, .stride, .stateBase, .multiplier, .scratch].Nodup)
  change (accumulateName T D SB M A).run x (accumulateNameTime (v T) (v D))
    ((accumulateName T D SB M A).enter cfg) =
      some ⟨some none, fun r ↦ if r = SB then v T * v D else v r, none, output⟩
  simpa only [cfg, enter, hReady.stateBase, Nat.zero_add] using
    run_accumulateName x T D SB M A cfg hDistinct hReady.multiplier hReady.scratch

/-- The preparation writes the six exact bases while restoring the work registers. -/
theorem runsValues_stepPreparationFragment (states : Nat) (x : BinaryWord) (v : R → Nat)
    (hReady : StepPreparationReady lanes v) :
    (stepPreparationFragment lanes states).RunsValues x
      (stepPreparationTime (v T) (v D) (v W) states) v (stepPreparationValues lanes v states) := by
  let current := v T * v D
  let next := (v T + 1) * v D
  let stateBase := setValue SB current v
  let headBase := setValue HB (current + states) stateBase
  let cellBase := setValue CB (current + states + v W) headBase
  let nextStateBase := setValue SN next cellBase
  let nextHeadBase := setValue HN (next + states) nextStateBase
  have hState := runsValues_stateBase lanes x v hReady
  have hHead := runsValues_copyInc SB HB A states x stateBase
    (lanes.injective.ne (by decide)) (lanes.injective.ne (by decide))
    (lanes.injective.ne (by decide))
    (by simpa [stateBase, setLane_apply] using hReady.headBase)
    (by simpa [stateBase, setLane_apply] using hReady.scratch)
  simp only [stateBase, setValue_same] at hHead
  have hCell := runsValues_copyAdd HB W CB A x headBase
    (lanes.injective.ne (by decide)) (lanes.injective.ne (by decide))
    (lanes.injective.ne (by decide)) (lanes.injective.ne (by decide))
    (lanes.injective.ne (by decide))
    (by simpa [headBase, stateBase, setLane_apply] using hReady.cellBase)
    (by simpa [headBase, stateBase, setLane_apply] using hReady.scratch)
  simp only [headBase, stateBase, setLane_apply, reduceCtorEq, ite_true, ite_false] at hCell
  have hNextState := runsValues_copyAdd SB D SN A x cellBase
    (lanes.injective.ne (by decide)) (lanes.injective.ne (by decide))
    (lanes.injective.ne (by decide)) (lanes.injective.ne (by decide))
    (lanes.injective.ne (by decide))
    (by simpa [cellBase, headBase, stateBase, setLane_apply] using hReady.nextStateBase)
    (by simpa [cellBase, headBase, stateBase, setLane_apply] using hReady.scratch)
  have hNext : current + v D = next := by simp [current, next, Nat.add_mul]
  simp only [cellBase, headBase, stateBase, setLane_apply, reduceCtorEq, ite_true, ite_false,
    hNext] at hNextState
  have hNextHead := runsValues_copyInc SN HN A states x nextStateBase
    (lanes.injective.ne (by decide)) (lanes.injective.ne (by decide))
    (lanes.injective.ne (by decide))
    (by simpa [nextStateBase, cellBase, headBase, stateBase, setLane_apply] using
      hReady.nextHeadBase)
    (by simpa [nextStateBase, cellBase, headBase, stateBase, setLane_apply] using hReady.scratch)
  simp only [nextStateBase, setValue_same] at hNextHead
  have hNextCell := runsValues_copyAdd HN W CN A x nextHeadBase
    (lanes.injective.ne (by decide)) (lanes.injective.ne (by decide))
    (lanes.injective.ne (by decide)) (lanes.injective.ne (by decide))
    (lanes.injective.ne (by decide))
    (by simpa [nextHeadBase, nextStateBase, cellBase, headBase, stateBase, setLane_apply] using
      hReady.nextCellBase)
    (by simpa [nextHeadBase, nextStateBase, cellBase, headBase, stateBase, setLane_apply] using
      hReady.scratch)
  simp only [nextHeadBase, nextStateBase, cellBase, headBase, stateBase,
    setLane_apply, reduceCtorEq, ite_true, ite_false] at hNextCell
  exact ((((hState.seq hHead).seq hCell).seq hNextState).seq hNextHead).seq hNextCell

private theorem runsValues_clearUpdated (r : R) (n : Nat) (x : BinaryWord) (v : R → Nat)
    (hZero : v r = 0) :
    (clear r).RunsValues x (n + 1) (setValue r n v) v := by
  have hClear : setValue r 0 (setValue r n v) = v := by
    rw [setValue_replace, ← hZero, setValue_current]
  simpa only [setValue_same, hClear] using runsValues_clear r x (setValue r n v)

/-- Clear the bases after a payload that preserved the prepared valuation. -/
theorem runsValues_stepCleanupFragment (states : Nat) (x : BinaryWord) (v : R → Nat)
    (hReady : StepPreparationReady lanes v) :
    (stepCleanupFragment lanes).RunsValues x (stepCleanupTime (v T) (v D) (v W) states)
      (stepPreparationValues lanes v states) v := by
  let current := v T * v D
  let next := (v T + 1) * v D
  let stateBase := setValue SB current v
  let headBase := setValue HB (current + states) stateBase
  let cellBase := setValue CB (current + states + v W) headBase
  let nextStateBase := setValue SN next cellBase
  let nextHeadBase := setValue HN (next + states) nextStateBase
  have hNextCell := runsValues_clearUpdated CN (next + states + v W) x nextHeadBase
    (by simpa [nextHeadBase, nextStateBase, cellBase, headBase, stateBase, setLane_apply] using
      hReady.nextCellBase)
  have hNextHead := runsValues_clearUpdated HN (next + states) x nextStateBase
    (by simpa [nextStateBase, cellBase, headBase, stateBase, setLane_apply] using
      hReady.nextHeadBase)
  have hNextState := runsValues_clearUpdated SN next x cellBase
    (by simpa [cellBase, headBase, stateBase, setLane_apply] using hReady.nextStateBase)
  have hCell := runsValues_clearUpdated CB (current + states + v W) x headBase
    (by simpa [headBase, stateBase, setLane_apply] using hReady.cellBase)
  have hHead := runsValues_clearUpdated HB (current + states) x stateBase
    (by simpa [stateBase, setLane_apply] using hReady.headBase)
  have hState := runsValues_clearUpdated SB current x v hReady.stateBase
  exact ((((hNextCell.seq hNextHead).seq hNextState).seq hCell).seq hHead).seq hState

end PvsNP.CookLevin
