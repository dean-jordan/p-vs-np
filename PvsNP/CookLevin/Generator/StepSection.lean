module

public import PvsNP.CookLevin.Generator.Blocks
public import PvsNP.CookLevin.Generator.StepBudget

/-! # Linking all transitions for one time -/

@[expose] public section

namespace PvsNP.CookLevin

open RegisterMachine Fragment

/-- The two clause generators share the prepared bases and width. -/
inductive StepSectionLane where
  | parameter (lane : StepPreparationLane)
  | copy (lane : StepCopyLane)
  | update (lane : StepUpdateLane)
  deriving DecidableEq

def stepCopyCode : StepCopyLane → StepSectionLane
  | .width => .parameter .width
  | .headBase => .parameter .headBase
  | .cellBase => .parameter .cellBase
  | .nextCellBase => .parameter .nextCellBase
  | lane => .copy lane

def stepUpdateCode : StepUpdateLane → StepSectionLane
  | .width => .parameter .width
  | .stateBase => .parameter .stateBase
  | .headBase => .parameter .headBase
  | .cellBase => .parameter .cellBase
  | .nextStateBase => .parameter .nextStateBase
  | .nextHeadBase => .parameter .nextHeadBase
  | .nextCellBase => .parameter .nextCellBase
  | lane => .update lane

variable {R : Type} (lanes : StepSectionLane ↪ R)

def stepPreparationLayout : StepPreparationLanes R :=
  ⟨fun p ↦ lanes (.parameter p), fun _ _ h ↦ StepSectionLane.parameter.inj (lanes.injective h)⟩

def stepCopyLayout : StepCopyLanes R :=
  ⟨fun c ↦ lanes (stepCopyCode c), by
    intro a b h
    have eq := lanes.injective h
    cases a <;> cases b <;> first | rfl | cases eq⟩

def stepUpdateLayout : StepUpdateLane ↪ R :=
  ⟨fun u ↦ lanes (stepUpdateCode u), by
    intro a b h
    have eq := lanes.injective h
    cases a <;> cases b <;> first | rfl | cases eq⟩

@[simp] theorem stepPreparationLayout_apply (p : StepPreparationLane) :
    stepPreparationLayout lanes p = lanes (.parameter p) := rfl

@[simp] theorem stepCopyLayout_apply (c : StepCopyLane) :
    stepCopyLayout lanes c = lanes (stepCopyCode c) := rfl

@[simp] theorem stepUpdateLayout_apply (u : StepUpdateLane) :
    stepUpdateLayout lanes u = lanes (stepUpdateCode u) := rfl

local notation "T" => lanes (StepSectionLane.parameter StepPreparationLane.time)
local notation "D" => lanes (StepSectionLane.parameter StepPreparationLane.stride)
local notation "W" => lanes (StepSectionLane.parameter StepPreparationLane.width)
local notation "Prep" => stepPreparationLayout lanes
local notation "Copy" => stepCopyLayout lanes
local notation "Update" => stepUpdateLayout lanes

/-- The incoming coordinates are the only occupied registers of this block. -/
def StepSectionReady (v : R → Nat) : Prop :=
  ∀ lane : StepSectionLane, lane ≠ .parameter .time → lane ≠ .parameter .stride →
    lane ≠ .parameter .width → v (lanes lane) = 0

/-- Prepare both rows, emit copy and update clauses, then clear the bases. -/
abbrev stepSectionFragment {states symbols certificates : Nat}
    (table : FiniteTable states symbols certificates) : Fragment R :=
  (((stepPreparationFragment Prep states).seq (stepCopiesFragment Copy symbols)).seq
    (stepUpdatesFragment Update table)).seq (stepCleanupFragment Prep)

private theorem prepareReady (v : R → Nat) (h : StepSectionReady lanes v) :
    StepPreparationReady Prep v := by
  constructor <;> exact h _ (by decide) (by decide) (by decide)

variable [DecidableEq R]

private theorem untouchedWork (v : R → Nat) (states : Nat) (h : StepSectionReady lanes v)
    (l : StepSectionLane) (hl : ∀ p, l ≠ .parameter p) :
    stepPreparationValues Prep v states (lanes l) = 0 := by
  rw [stepPreparationValues_other Prep v states _ (lanes.injective.ne (hl .stateBase))
    (lanes.injective.ne (hl .headBase)) (lanes.injective.ne (hl .cellBase))
    (lanes.injective.ne (hl .nextStateBase)) (lanes.injective.ne (hl .nextHeadBase))
    (lanes.injective.ne (hl .nextCellBase))]
  exact h l (hl .time) (hl .stride) (hl .width)

private theorem copyReady (v : R → Nat) (states : Nat) (h : StepSectionReady lanes v) :
    StepCopiesReady Copy (stepPreparationValues Prep v states) := by
  have zero (k : StepCopyLane) := untouchedWork lanes v states h (.copy k)
    (fun _ e ↦ by cases e)
  exact ⟨⟨zero .cellOffset, zero .multiplier, zero .arithmeticScratch, zero .literalIndex,
      zero .literalScratch, zero .compareHead, zero .compareCell, zero .compareScratch⟩,
    zero .head, zero .cell, zero .symbol⟩

private theorem updateReady (v : R → Nat) (states : Nat) (h : StepSectionReady lanes v) :
    StepUpdateReady Update (stepPreparationValues Prep v states) ∧
      stepPreparationValues Prep v states (Update .position) = 0 := by
  have zero (k : StepUpdateLane) := untouchedWork lanes v states h (.update k)
    (fun _ e ↦ by cases e)
  exact ⟨⟨zero .stateOffset, zero .nextStateOffset, zero .readOffset, zero .writtenOffset,
      zero .nextPosition, zero .multiplier, zero .index, zero .scratch, zero .leftCopy,
      zero .rightCopy⟩, zero .position⟩

/-- The linked step emits the exact indexed clauses and restores its entry registers. -/
theorem run_stepSectionFragment {states symbols certificates : Nat}
    (table : FiniteTable states symbols certificates) (x suffix : BinaryWord) (v : R → Nat)
    (hStride : v D = Tableau.atomStride states (v W) symbols) (hReady : StepSectionReady lanes v) :
    ∃ cost ≤ stepTimeBound states symbols (v W) (v D) (v T),
      (stepSectionFragment lanes table).RunsOutput x cost v v suffix
        (table.foldStepClauses (emitIndexedClause (width := v W)) suffix (v T)) := by
  let loaded := stepPreparationValues Prep v states
  have entryReady := prepareReady lanes v hReady
  have hPrepare := runsValues_stepPreparationFragment Prep states x v entryReady
  have hCleanup := runsValues_stepCleanupFragment Prep states x v entryReady
  have hAt (p : StepPreparationLane) := stepPreparationValues_at Prep v states p
  simp only [stepPreparationLayout_apply] at hAt
  have hBases : StepUpdateBases Update loaded (v T) states symbols (v W) := by
    constructor <;> simp [loaded, stepUpdateCode, hAt, hStride]
  obtain ⟨ct, hCt, hCopy⟩ := run_stepCopiesFragment Copy symbols x suffix loaded
    (copyReady lanes v states hReady)
  simp only [loaded, stepCopyLayout_apply, stepCopyCode, hAt] at hCt hCopy
  obtain ⟨hUpdateReady, hPosition⟩ := updateReady lanes v states hReady
  obtain ⟨ut, hUt, hUpdate⟩ := runsOutput_stepUpdatesFragment Update table x _ loaded
    hPosition hBases hUpdateReady
  rw [stepUpdatesTimeBound_eq_numeric Update loaded hBases, ← hStride] at hUt
  have hOutput : stepUpdatesOutput table (v T) (v W)
      (stepCopiesOutput (v W) symbols (v T * v D + states) (v T * v D + states + v W)
        ((v T + 1) * v D + states + v W) suffix) =
      table.foldStepClauses (emitIndexedClause (width := v W)) suffix (v T) := by
    change _ = table.foldStepClauses prependIndexedUpdateClause suffix (v T)
    rw [foldStepClauses_eq_updateOutput, hStride, stepCopiesOutput_eq]
    rfl
  rw [hOutput] at hUpdate
  exact ⟨_, Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_left hCt _) hUt) _,
    (((hPrepare.withOutput suffix).seq hCopy).seq hUpdate).seq (hCleanup.withOutput _)⟩

end PvsNP.CookLevin
