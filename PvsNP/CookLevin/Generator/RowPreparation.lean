module

public import PvsNP.CookLevin.Generator.NameRegister
public import PvsNP.TuringMachine.Registers.OutputRuns

/-! # Register setup for exactly-one tableau fields -/

@[expose] public section

namespace PvsNP.CookLevin

open RegisterMachine RegisterMachine.Fragment

/-- Register roles used to prepare a contiguous field of numeric atom names. -/
inductive RowPreparationLane where
  | time | stride | width | position | base | count | multiplier | scratch
  deriving DecidableEq

/-- The preparation uses distinct registers for its eight roles. -/
abbrev RowPreparationLanes (R : Type) := RowPreparationLane ↪ R

namespace RowPreparationLanes

variable {R : Type} (lanes : RowPreparationLanes R)

local notation "T" => lanes RowPreparationLane.time
local notation "D" => lanes RowPreparationLane.stride
local notation "W" => lanes RowPreparationLane.width
local notation "P" => lanes RowPreparationLane.position
local notation "B" => lanes RowPreparationLane.base
local notation "N" => lanes RowPreparationLane.count
local notation "M" => lanes RowPreparationLane.multiplier
local notation "S" => lanes RowPreparationLane.scratch

/-- The four registers that must start empty. -/
structure Ready (values : R → Nat) : Prop where
  base : values B = 0
  count : values N = 0
  multiplier : values M = 0
  scratch : values S = 0

/-- Initialize a state field with base `time * stride`. -/
def stateField (states : Nat) : Fragment R :=
  (accumulateName T D B M S).seq (incrementBy N states)

/-- Prepare the base shared by the head and cell fields. -/
def shiftedBase (states : Nat) : Fragment R :=
  (accumulateName T D B M S).seq (incrementBy B states)

/-- Initialize a head field with its base and window width. -/
def headField (states : Nat) : Fragment R :=
  (lanes.shiftedBase states).seq (add W N S)

/-- Initialize the symbol field for the current cell. -/
def cellField (states symbols : Nat) : Fragment R :=
  ((((lanes.shiftedBase states).seq (add W B S)).seq (incrementBy M symbols)).seq
    (multiply M P B S)).seq (incrementBy N symbols)

/-- Exact instruction count for state preparation. -/
def stateTime (values : R → Nat) (states : Nat) : Nat :=
  accumulateNameTime (values T) (values D) + states

/-- Exact instruction count for head preparation. -/
def headTime (values : R → Nat) (states : Nat) : Nat :=
  lanes.stateTime values states + (5 * values W + 2)

/-- Exact instruction count for cell preparation. -/
def cellTime (values : R → Nat) (states symbols : Nat) : Nat :=
  lanes.headTime values states + symbols + (symbols * (5 * values P + 3) + 1) + symbols

theorem stateTime_polynomiallyBounded {values : Nat → R → Nat}
    (hTime : PolynomiallyBounded (fun n ↦ values n T))
    (hStride : PolynomiallyBounded (fun n ↦ values n D)) (states : Nat) :
    PolynomiallyBounded (fun n ↦ lanes.stateTime (values n) states) :=
  (accumulateNameTime_polynomiallyBounded hTime hStride).add (PolynomiallyBounded.const states)

theorem headTime_polynomiallyBounded {values : Nat → R → Nat}
    (hTime : PolynomiallyBounded (fun n ↦ values n T))
    (hStride : PolynomiallyBounded (fun n ↦ values n D))
    (hWidth : PolynomiallyBounded (fun n ↦ values n W)) (states : Nat) :
    PolynomiallyBounded (fun n ↦ lanes.headTime (values n) states) :=
  (lanes.stateTime_polynomiallyBounded hTime hStride states).add
    (((PolynomiallyBounded.const 5).mul hWidth).add (PolynomiallyBounded.const 2))

theorem cellTime_polynomiallyBounded {values : Nat → R → Nat}
    (hTime : PolynomiallyBounded (fun n ↦ values n T))
    (hStride : PolynomiallyBounded (fun n ↦ values n D))
    (hWidth : PolynomiallyBounded (fun n ↦ values n W))
    (hPosition : PolynomiallyBounded (fun n ↦ values n P)) (states symbols : Nat) :
    PolynomiallyBounded (fun n ↦ lanes.cellTime (values n) states symbols) := by
  let lit := PolynomiallyBounded.const
  have hLoop := ((lit symbols).mul (((lit 5).mul hPosition).add (lit 3))).add (lit 1)
  exact (((lanes.headTime_polynomiallyBounded hTime hStride hWidth states).add
    (lit symbols)).add hLoop).add (lit symbols)

variable [DecidableEq R]

/-- The state field contains a contiguous block of state indices. -/
def stateValues (values : R → Nat) (states : Nat) : R → Nat :=
  setValue N states (setValue B (values T * values D) values)

/-- The head field starts after all state indices in the row. -/
def headValues (values : R → Nat) (states : Nat) : R → Nat :=
  setValue N (values W) (setValue B (values T * values D + states) values)

/-- The cell field starts after the head indices and preceding cell fields. -/
def cellValues (values : R → Nat) (states symbols : Nat) : R → Nat :=
  setValue N symbols
    (setValue B (values T * values D + states + values W + values P * symbols) values)

private theorem runsValues_timeBase (x : BinaryWord) (before : R → Nat)
    (hReady : lanes.Ready before) :
    (accumulateName T D B M S).RunsValues x
      (accumulateNameTime (before T) (before D)) before
      (setValue B (before T * before D) before) := by
  intro output
  let cfg : Config R Unit := ⟨none, before, none, output⟩
  have hDistinct : [T, D, B, M, S].Nodup :=
    List.Nodup.map lanes.injective
      (by decide : [RowPreparationLane.time, .stride, .base, .multiplier, .scratch].Nodup)
  change (accumulateName T D B M S).run x (accumulateNameTime (before T) (before D))
    ((accumulateName T D B M S).enter cfg) =
      some ⟨some none, fun r ↦ if r = B then before T * before D else before r, none, output⟩
  simpa only [cfg, enter, hReady.base, Nat.zero_add] using
    run_accumulateName x T D B M S cfg hDistinct hReady.multiplier hReady.scratch

theorem runsValues_stateField (states : Nat) (x : BinaryWord) (before : R → Nat)
    (hReady : lanes.Ready before) :
    (lanes.stateField states).RunsValues x (lanes.stateTime before states)
      before (lanes.stateValues before states) := by
  let named := setValue B (before T * before D) before
  have hCount : named N = 0 :=
    (setValue_other (lanes.injective.ne (by decide)) ..).trans hReady.count
  have hSet := runsValues_incrementBy N states x named
  rw [hCount, Nat.zero_add] at hSet
  exact (lanes.runsValues_timeBase x before hReady).seq hSet

private theorem runsValues_shiftedBase (states : Nat) (x : BinaryWord) (before : R → Nat)
    (hReady : lanes.Ready before) :
    (lanes.shiftedBase states).RunsValues x (lanes.stateTime before states)
      before (setValue B (before T * before D + states) before) := by
  have hSet := runsValues_incrementBy B states x (setValue B (before T * before D) before)
  rw [setValue_same, setValue_replace] at hSet
  exact (lanes.runsValues_timeBase x before hReady).seq hSet

theorem runsValues_headField (states : Nat) (x : BinaryWord) (before : R → Nat)
    (hReady : lanes.Ready before) :
    (lanes.headField states).RunsValues x (lanes.headTime before states)
      before (lanes.headValues before states) := by
  let named := setValue B (before T * before D + states) before
  have hCount : named N = 0 :=
    (setValue_other (lanes.injective.ne (by decide)) ..).trans hReady.count
  have hWidth : named W = before W := setValue_other (lanes.injective.ne (by decide)) ..
  have hScratch : named S = 0 :=
    (setValue_other (lanes.injective.ne (by decide)) ..).trans hReady.scratch
  have hSet := runsValues_add W N S x named
    (lanes.injective.ne (by decide)) (lanes.injective.ne (by decide))
    (lanes.injective.ne (by decide)) hScratch
  rw [hCount, hWidth, Nat.zero_add] at hSet
  exact (lanes.runsValues_shiftedBase states x before hReady).seq hSet

theorem runsValues_cellField (states symbols : Nat) (x : BinaryWord) (before : R → Nat)
    (hReady : lanes.Ready before) :
    (lanes.cellField states symbols).RunsValues x (lanes.cellTime before states symbols)
      before (lanes.cellValues before states symbols) := by
  let headBase := before T * before D + states
  let cellBase := headBase + before W
  let shifted := setValue B headBase before
  let withWidth := setValue B cellBase before
  let withFactor := setValue M symbols withWidth
  let named := setValue B (cellBase + before P * symbols) before
  have hShiftedWidth : shifted W = before W := setValue_other (lanes.injective.ne (by decide)) ..
  have hShiftedScratch : shifted S = 0 :=
    (setValue_other (lanes.injective.ne (by decide)) ..).trans hReady.scratch
  have hAddWidth := runsValues_add W B S x shifted
    (lanes.injective.ne (by decide)) (lanes.injective.ne (by decide))
    (lanes.injective.ne (by decide)) hShiftedScratch
  simp only [hShiftedWidth, shifted, setValue_same, setValue_replace] at hAddWidth
  have hEmptyFactor : withWidth M = 0 := by
    simp [withWidth, setValue, lanes.injective.eq_iff, hReady.multiplier]
  have hLoad := runsValues_incrementBy M symbols x withWidth
  rw [hEmptyFactor, Nat.zero_add] at hLoad
  have hFactor : withFactor M = symbols := setValue_same ..
  have hPosition : withFactor P = before P := by
    simp [withFactor, withWidth, setValue, lanes.injective.eq_iff]
  have hBase : withFactor B = cellBase := by
    simp [withFactor, withWidth, setValue, lanes.injective.eq_iff]
  have hScratch : withFactor S = 0 := by
    simp [withFactor, withWidth, setValue, lanes.injective.eq_iff, hReady.scratch]
  have hCleared : setValue M 0 withFactor = withWidth := by
    simpa only [withFactor, setValue_replace, hEmptyFactor] using setValue_current M withWidth
  have hProduct := runsValues_multiply M P B S x withFactor
    (lanes.injective.ne (by decide)) (lanes.injective.ne (by decide))
    (lanes.injective.ne (by decide)) (lanes.injective.ne (by decide))
    (lanes.injective.ne (by decide)) (lanes.injective.ne (by decide)) hScratch
  simp only [hFactor, hPosition, hBase, hCleared, withWidth, setValue_replace,
    Nat.mul_comm symbols (before P)] at hProduct
  have hCount : named N = 0 := by
    simp [named, setValue, lanes.injective.eq_iff, hReady.count]
  have hSet := runsValues_incrementBy N symbols x named
  rw [hCount, Nat.zero_add] at hSet
  exact ((((lanes.runsValues_shiftedBase states x before hReady).seq hAddWidth).seq hLoad).seq
    hProduct).seq hSet

end RowPreparationLanes

end PvsNP.CookLevin
