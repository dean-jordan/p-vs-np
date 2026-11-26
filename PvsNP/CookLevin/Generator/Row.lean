module

public import PvsNP.CookLevin.Generator.PreparedField
public import PvsNP.CookLevin.Generator.RowModel
public import PvsNP.CookLevin.Generator.RowPreparation

/-! # Finite register code for the constraints of one row -/

@[expose] public section

namespace PvsNP.CookLevin

open RegisterMachine Fragment

/-- The persistent row coordinates and the registers reused by every row field. -/
inductive RowLane where
  | time | stride | width | position | multiplier | preparationScratch
  | field (lane : ExactlyOneLane)
  deriving DecidableEq

/-- The field part of the larger row valuation. -/
def rowFieldLanes {R : Type} (lanes : RowLane ↪ R) : ExactlyOneLane ↪ R :=
  ⟨fun lane ↦ lanes (.field lane), fun _ _ h ↦ RowLane.field.inj (lanes.injective h)⟩

/-- The preparer writes to the same base and count lanes used by the field program. -/
def rowPreparationCode : RowPreparationLane → RowLane
  | .time => .time
  | .stride => .stride
  | .width => .width
  | .position => .position
  | .base => .field .base
  | .count => .field .count
  | .multiplier => .multiplier
  | .scratch => .preparationScratch

def rowPreparationLanes {R : Type} (lanes : RowLane ↪ R) : RowPreparationLanes R :=
  ⟨fun lane ↦ lanes (rowPreparationCode lane), by
    intro a b h
    have same := lanes.injective h
    cases a <;> cases b <;> simp_all [rowPreparationCode]⟩

variable {R : Type} (lanes : RowLane ↪ R)

local notation "T" => lanes RowLane.time
local notation "D" => lanes RowLane.stride
local notation "W" => lanes RowLane.width
local notation "P" => lanes RowLane.position
local notation "A" => lanes RowLane.preparationScratch
local notation "setup" => rowPreparationLanes lanes
local notation "fieldLanes" => rowFieldLanes lanes

/-- Zero work lanes required at a row field boundary. -/
structure RowReady (v : R → Nat) : Prop where
  prepare : (setup).Ready v
  work : ExactlyOneScratchZero fieldLanes v
  left : v (fieldLanes .left) = 0
  right : v (fieldLanes .right) = 0

/-- Descend through the window cells, consuming the position counter. -/
abbrev rowCellFields (states symbols : Nat) : Fragment R :=
  (add W P A).seq (countdown P (preparedField fieldLanes ((setup).cellField states symbols)))

/-- Emit the cell fields, the head field, and the state field in that order. -/
abbrev rowFragment (states symbols : Nat) : Fragment R :=
  let head := preparedField fieldLanes ((setup).headField states)
  let state := preparedField fieldLanes ((setup).stateField states)
  ((rowCellFields lanes states symbols).seq head).seq state

variable [DecidableEq R]

/-- Bound every cell field using the window width as an upper bound on its position. -/
def rowCellFieldTimeBound (v : R → Nat) (states symbols : Nat) : Nat :=
  preparedFieldTimeBound ((setup).cellTime (setValue P (v W) v) states symbols)
    (v T * v D + states + v W + v W * symbols) symbols

/-- A uniform budget for all the fields of one row. -/
def rowTimeBound (v : R → Nat) (states symbols : Nat) : Nat :=
  ((5 * v W + 2 + (v W * (rowCellFieldTimeBound lanes v states symbols + 1) + 1)) +
    preparedFieldTimeBound ((setup).headTime v states) (v T * v D + states) (v W)) +
    preparedFieldTimeBound ((setup).stateTime v states) (v T * v D) states

private theorem readyAtPosition (v : R → Nat) (i : Nat) (h : RowReady lanes v) :
    RowReady lanes (setValue P i v) := by
  have fixed (lane : RowPreparationLane) (hNe : rowPreparationCode lane ≠ .position) :
      setValue P i v (setup lane) = v (setup lane) :=
    setValue_other (lanes.injective.ne hNe) i v
  have fieldFixed (lane : ExactlyOneLane) :
      setValue P i v (fieldLanes lane) = v (fieldLanes lane) :=
    setValue_other (lanes.injective.ne (show RowLane.field lane ≠ .position from fun eq ↦ by
      cases eq)) i v
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact (fixed .base (by decide)).trans h.prepare.base
  · exact (fixed .count (by decide)).trans h.prepare.count
  · exact (fixed .multiplier (by decide)).trans h.prepare.multiplier
  · exact (fixed .scratch (by decide)).trans h.prepare.scratch
  · simpa only [ExactlyOneScratchZero, fieldFixed] using h.work
  · exact (fieldFixed .left).trans h.left
  · exact (fieldFixed .right).trans h.right

private theorem run_rowCellFields (states symbols : Nat) (x suffix : BinaryWord) (v : R → Nat)
    (hReady : RowReady lanes v) (hPosition : v P = 0) :
    ∃ cost ≤ 5 * v W + 2 + (v W * (rowCellFieldTimeBound lanes v states symbols + 1) + 1),
      (rowCellFields lanes states symbols).RunsOutput x cost v v suffix
        ((List.range (v W)).reverse.foldl (fun acc i ↦
          exactlyOneFieldOutput (v T * v D + states + v W + i * symbols) symbols acc) suffix) := by
  let body := preparedField fieldLanes ((setup).cellField states symbols)
  have hBody (i : Nat) (hi : i < v W) (acc : BinaryWord) :
      ∃ cost ≤ rowCellFieldTimeBound lanes v states symbols,
        body.RunsOutput x cost (setValue P i v) (setValue P i v) acc
          (exactlyOneFieldOutput (v T * v D + states + v W + i * symbols) symbols acc) := by
    let atCell := setValue P i v
    have hReady' := readyAtPosition lanes v i hReady
    have ht : atCell T = v T := by simp [atCell, setValue]
    have hd : atCell D = v D := by simp [atCell, setValue]
    have hw : atCell W = v W := by simp [atCell, setValue]
    have hp : atCell P = i := setValue_same ..
    have hPrepare := (setup).runsValues_cellField states symbols x atCell hReady'.prepare
    change ((setup).cellField states symbols).RunsValues x ((setup).cellTime atCell states symbols)
      atCell (setValue (fieldLanes .count) symbols
        (setValue (fieldLanes .base) (atCell T * atCell D + states + atCell W + atCell P * symbols)
          atCell)) at hPrepare
    rw [ht, hd, hw, hp] at hPrepare
    obtain ⟨cost, hCost, hRun⟩ := run_preparedField fieldLanes _ x acc atCell _ _ _ hPrepare
      hReady'.prepare.base hReady'.prepare.count hReady'.left hReady'.right hReady'.work
    have hPrepEq (j : Nat) : (setup).cellTime (setValue P j v) states symbols =
        (setup).headTime v states + symbols + (symbols * (5 * j + 3) + 1) + symbols := by
      simp [RowPreparationLanes.cellTime, RowPreparationLanes.headTime,
        RowPreparationLanes.stateTime, rowPreparationLanes, rowPreparationCode, setValue]
    have hPrepCost : (setup).cellTime atCell states symbols ≤
        (setup).cellTime (setValue P (v W) v) states symbols := by
      rw [show atCell = setValue P i v from rfl, hPrepEq, hPrepEq]
      have hMul := Nat.mul_le_mul_left symbols (show 5 * i + 3 ≤ 5 * v W + 3 by omega)
      omega
    have hPos := Nat.mul_le_mul_right symbols (Nat.le_of_lt hi)
    have hBase : v T * v D + states + v W + i * symbols ≤
        v T * v D + states + v W + v W * symbols := by omega
    have hField := exactlyOneFieldTimeBound_mono hBase (Nat.le_refl symbols)
    have hTotal : preparedFieldTimeBound ((setup).cellTime atCell states symbols)
        (v T * v D + states + v W + i * symbols) symbols ≤
          rowCellFieldTimeBound lanes v states symbols := by
      simp only [rowCellFieldTimeBound, preparedFieldTimeBound]
      omega
    exact ⟨cost, hCost.trans hTotal, hRun⟩
  exact runsOutput_initializedCountdown W P A body x v
    (rowCellFieldTimeBound lanes v states symbols)
    (fun acc i ↦ exactlyOneFieldOutput (v T * v D + states + v W + i * symbols) symbols acc)
    (lanes.injective.ne (by decide)) (lanes.injective.ne (by decide))
    (lanes.injective.ne (by decide)) hPosition hReady.prepare.scratch hBody suffix

/-- The finite row program emits all its fields and restores the entry valuation. -/
theorem run_rowFragment (states symbols : Nat) (x suffix : BinaryWord) (v : R → Nat)
    (hReady : RowReady lanes v) (hPosition : v P = 0) :
    ∃ cost ≤ rowTimeBound lanes v states symbols,
      (rowFragment lanes states symbols).RunsOutput x cost v v suffix
        (tableauRowOutput states symbols (v W) (v D) (v T) suffix) := by
  obtain ⟨cells, hCells, hCellRun⟩ := run_rowCellFields lanes states symbols x suffix v
    hReady hPosition
  obtain ⟨head, hHead, hHeadRun⟩ := run_preparedField fieldLanes _ x _ v
    ((setup).headTime v states) (v T * v D + states) (v W)
    ((setup).runsValues_headField states x v hReady.prepare)
    hReady.prepare.base hReady.prepare.count hReady.left hReady.right hReady.work
  obtain ⟨state, hState, hStateRun⟩ := run_preparedField fieldLanes _ x _ v
    ((setup).stateTime v states) (v T * v D) states
    ((setup).runsValues_stateField states x v hReady.prepare)
    hReady.prepare.base hReady.prepare.count hReady.left hReady.right hReady.work
  exact ⟨cells + head + state, Nat.add_le_add (Nat.add_le_add hCells hHead) hState,
    (hCellRun.seq hHeadRun).seq hStateRun⟩

/-- The row cost is polynomial in the persistent coordinates for fixed alphabet sizes. -/
theorem rowTimeBound_polynomiallyBounded {v : Nat → R → Nat}
    (ht : PolynomiallyBounded (fun n ↦ v n T)) (hd : PolynomiallyBounded (fun n ↦ v n D))
    (hw : PolynomiallyBounded (fun n ↦ v n W)) (states symbols : Nat) :
    PolynomiallyBounded (fun n ↦ rowTimeBound lanes (v n) states symbols) := by
  let lit := PolynomiallyBounded.const
  let atLast (n : Nat) := setValue P (v n W) (v n)
  have ht' : PolynomiallyBounded (fun n ↦ atLast n (setup .time)) := by
    simpa [atLast, rowPreparationLanes, rowPreparationCode, setValue] using ht
  have hd' : PolynomiallyBounded (fun n ↦ atLast n (setup .stride)) := by
    simpa [atLast, rowPreparationLanes, rowPreparationCode, setValue] using hd
  have hw' : PolynomiallyBounded (fun n ↦ atLast n (setup .width)) := by
    simpa [atLast, rowPreparationLanes, rowPreparationCode, setValue] using hw
  have hp' : PolynomiallyBounded (fun n ↦ atLast n (setup .position)) := by
    simpa [atLast, rowPreparationLanes, rowPreparationCode] using hw
  have hBase := ht.mul hd
  have hHeadBase := hBase.add (lit states)
  have hCellBase := (hHeadBase.add hw).add (hw.mul (lit symbols))
  have hCell := preparedFieldTimeBound_polynomiallyBounded
    ((setup).cellTime_polynomiallyBounded ht' hd' hw' hp' states symbols) hCellBase (lit symbols)
  have hHead := preparedFieldTimeBound_polynomiallyBounded
    ((setup).headTime_polynomiallyBounded ht hd hw states) hHeadBase hw
  have hState := preparedFieldTimeBound_polynomiallyBounded
    ((setup).stateTime_polynomiallyBounded ht hd states) hBase (lit states)
  have hCopy := ((lit 5).mul hw).add (lit 2)
  have hCells := hCopy.add ((hw.mul (hCell.add (lit 1))).add (lit 1))
  exact (hCells.add hHead).add hState

end PvsNP.CookLevin
