module

public import PvsNP.CookLevin.Generator.GapClause
public import PvsNP.CookLevin.Generator.UpdateClauses
public import PvsNP.CookLevin.Generator.Traversal
public import PvsNP.TuringMachine.Registers.Affine
public import PvsNP.TuringMachine.Registers.Sequence

/-! # Register traversal for tableau transition updates -/

@[expose] public section

namespace PvsNP.CookLevin

open RegisterMachine RegisterMachine.Fragment

/-- Persistent dimensions and bases, followed by the work lanes of one transition leaf. -/
inductive StepUpdateLane where
  | width | position | stateBase | headBase | cellBase | nextStateBase | nextHeadBase | nextCellBase
  | stateOffset | readOffset | nextStateOffset | nextPosition | writtenOffset
  | multiplier | index | scratch | leftCopy | rightCopy
  deriving DecidableEq

variable {R : Type} (lanes : StepUpdateLane ↪ R)

local notation "W" => lanes StepUpdateLane.width
local notation "P" => lanes StepUpdateLane.position
local notation "SB" => lanes StepUpdateLane.stateBase
local notation "HB" => lanes StepUpdateLane.headBase
local notation "CB" => lanes StepUpdateLane.cellBase
local notation "NSB" => lanes StepUpdateLane.nextStateBase
local notation "NHB" => lanes StepUpdateLane.nextHeadBase
local notation "NCB" => lanes StepUpdateLane.nextCellBase
local notation "SO" => lanes StepUpdateLane.stateOffset
local notation "RO" => lanes StepUpdateLane.readOffset
local notation "NSO" => lanes StepUpdateLane.nextStateOffset
local notation "H" => lanes StepUpdateLane.nextPosition
local notation "WO" => lanes StepUpdateLane.writtenOffset
local notation "M" => lanes StepUpdateLane.multiplier
local notation "Z" => lanes StepUpdateLane.index
local notation "S" => lanes StepUpdateLane.scratch
local notation "C₁" => lanes StepUpdateLane.leftCopy
local notation "C₂" => lanes StepUpdateLane.rightCopy

/-- The offsets, comparison copies, and scratch registers must start empty. -/
def StepUpdateReady (v : R → Nat) : Prop :=
  v SO = 0 ∧ v NSO = 0 ∧ v RO = 0 ∧ v WO = 0 ∧ v H = 0 ∧
    v M = 0 ∧ v Z = 0 ∧ v S = 0 ∧ v C₁ = 0 ∧ v C₂ = 0

/-- The six atom operands consumed by the update clause emitter. -/
def stepUpdateClauseLanes : UpdateClauseLanes R where
  guards := ⟨⟨SB, SO⟩, ⟨HB, P⟩, ⟨CB, RO⟩⟩
  nextState := ⟨NSB, NSO⟩
  nextHead := ⟨NHB, H⟩
  written := ⟨NCB, WO⟩
  index := Z
  scratch := S

/-- Decrement once with saturation and reach the same exit on either branch. -/
abbrev decrementOnce (lane : R) : Fragment R where
  Label := Unit
  entry := some ()
  code _ := .dec lane none none

/-- The numeric head move clamps at the window endpoints. -/
def updateHeadPosition (move : Option Turing.Dir) (width position : Nat) : Nat :=
  match move with
  | none => position
  | some .left => position - 1
  | some .right => if position + 1 < width then position + 1 else position

theorem updateHeadPosition_eq (move : Option Turing.Dir) {width : Nat} (i : Fin width) :
    updateHeadPosition move width i.val =
      (move.elim i (fun dir ↦ Machine.windowMoveHead dir i)).val := by
  cases move with
  | none => rfl
  | some dir =>
    cases dir with
    | left => rfl
    | right =>
      by_cases h : i.val + 1 < width <;>
        simp [updateHeadPosition, Machine.windowMoveHead, h]

theorem updateHeadPosition_le (move : Option Turing.Dir) (width position : Nat) :
    updateHeadPosition move width position ≤ position + 1 := by
  cases move with
  | none => exact Nat.le_succ _
  | some dir =>
    cases dir with
    | left => exact (Nat.sub_le ..).trans (Nat.le_succ _)
    | right =>
      by_cases h : position + 1 < width <;> simp [updateHeadPosition, h]

/-- Adjust the copied head position according to the fixed transition direction. -/
abbrev adjustUpdateHead : Option Turing.Dir → Fragment R
  | none => skip
  | some .left => decrementOnce H
  | some .right => (incrementBy H 1).seq (ifLess H W C₁ C₂ S skip (decrementOnce H))

/-- Budget for any fixed move, including a possible right-endpoint test. -/
def updateHeadTimeBound (position width : Nat) : Nat :=
  1 + (ifEqualTime (position + 1) width + 1)

variable [DecidableEq R]

private theorem runsValues_decrementOnce (lane : R) (x : BinaryWord) (v : R → Nat) :
    (decrementOnce lane).RunsValues x 1 v (setValue lane (v lane - 1) v) := by
  intro suffix
  let cfg : Config R Unit := ⟨none, v, none, suffix⟩
  let start := (decrementOnce lane).enter cfg
  have hPC : start.pc = some (some ()) := rfl
  have hRule : (decrementOnce lane).close (some ()) = .dec lane none none := rfl
  change RegisterMachine.run (decrementOnce lane).close x 1 start = _
  by_cases hZero : v lane = 0
  · have h := step_dec_zero (x := x) hPC hRule (show start.values lane = 0 from hZero)
    have hSub : v lane - 1 = v lane := by omega
    rw [RegisterMachine.run_succ, h, Option.bind_some, run_zero, hSub, setValue_current]
    rfl
  · have h := step_dec_pos (x := x) hPC hRule
      (show 0 < start.values lane from Nat.pos_of_ne_zero hZero)
    rw [RegisterMachine.run_succ, h, Option.bind_some, run_zero]
    have hValues : decrementValues lane v = setValue lane (v lane - 1) v := by
      funext r
      by_cases hr : r = lane
      · subst r
        simp [decrementValues, setValue]
      · simp [decrementValues, setValue, hr]
    exact congrArg (fun values ↦ some (⟨some none, values, none, suffix⟩ :
      (decrementOnce lane).Cfg)) hValues

private theorem runsOutput_adjustUpdateHead (move : Option Turing.Dir) (x suffix : BinaryWord)
    (v : R → Nat) (hCopyI : v C₁ = 0) (hCopyJ : v C₂ = 0) (hScratch : v S = 0) :
    ∃ cost ≤ updateHeadTimeBound (v H) (v W),
      (adjustUpdateHead lanes move).RunsOutput x cost v
        (setValue H (updateHeadPosition move (v W) (v H)) v) suffix suffix := by
  cases move with
  | none =>
    refine ⟨0, Nat.zero_le _, ?_⟩
    simpa only [adjustUpdateHead, updateHeadPosition, setValue_current] using
      runsOutput_skip x v suffix
  | some dir =>
    cases dir with
    | left =>
      refine ⟨1, by unfold updateHeadTimeBound; omega, ?_⟩
      exact (runsValues_decrementOnce H x v).withOutput suffix
    | right =>
      let moved := setValue H (v H + 1) v
      let after := setValue H (updateHeadPosition (some .right) (v W) (v H)) v
      have hInc := runsValues_incrementBy H 1 x v
      have hComp : ∃ cost ≤ ifEqualTime (moved H) (moved W) + 1,
          (ifLess H W C₁ C₂ S skip (decrementOnce H)).RunsOutput x cost moved after
            suffix suffix := by
        apply runsOutput_ifLess x moved after suffix suffix 1 (by simp) (by simp)
          (by simpa [moved, setValue] using hCopyI) (by simpa [moved, setValue] using hCopyJ)
          (by simpa [moved, setValue] using hScratch)
        · intro h
          have hLt : v H + 1 < v W := by simpa [moved, setValue] using h
          refine ⟨0, by omega, ?_⟩
          simpa only [after, updateHeadPosition, ite_eq_left hLt, moved] using
            runsOutput_skip x moved suffix
        · intro h
          have hNotLt : ¬ v H + 1 < v W := by simpa [moved, setValue] using h
          refine ⟨1, Nat.le_refl _, ?_⟩
          simpa only [after, updateHeadPosition, ite_eq_right hNotLt, moved, setValue_same,
            Nat.add_sub_cancel, setValue_replace] using
              (runsValues_decrementOnce H x moved).withOutput suffix
      obtain ⟨cost, hCost, hRun⟩ := hComp
      have hBound : cost ≤ ifEqualTime (v H + 1) (v W) + 1 := by
        simpa [moved, setValue] using hCost
      exact ⟨1 + cost, Nat.add_le_add_left hBound _, (hInc.withOutput suffix).seq hRun⟩

/-- The six names' persistent bases for one indexed step. -/
structure StepUpdateBases (v : R → Nat) (t states symbols window : Nat) : Prop where
  width : v W = window
  state : v SB = t * Tableau.atomStride states window symbols
  head : v HB = t * Tableau.atomStride states window symbols + states
  cell : v CB = t * Tableau.atomStride states window symbols + states + window
  nextState : v NSB = (t + 1) * Tableau.atomStride states window symbols
  nextHead : v NHB = (t + 1) * Tableau.atomStride states window symbols + states
  nextCell : v NCB = (t + 1) * Tableau.atomStride states window symbols + states + window

variable {qCount symbolCount certificateCount : Nat}

/-- Prepare the constant state offsets and the two affine cell offsets. -/
abbrev prepareUpdateOffsets (q : Fin qCount) (read : Fin symbolCount)
    (entry : IndexedTransition qCount symbolCount) : Fragment R :=
  (((incrementBy SO q.val).seq (incrementBy NSO entry.next.val)).seq
    (accumulateAffine P RO M S symbolCount read.val)).seq
      (accumulateAffine P WO M S symbolCount entry.written.val)

/-- The cleanup order reverses the order in which offsets were loaded. -/
abbrev clearUpdateOffsets : Fragment R :=
  ((((clear H).seq (clear WO)).seq (clear RO)).seq (clear NSO)).seq (clear SO)

/-- One finite leaf for a fixed verifier state and read symbol. -/
abbrev stepUpdateLeaf (table : FiniteTable qCount symbolCount certificateCount)
    (q : Fin qCount) (read : Fin symbolCount) : Fragment R :=
  let entry := table.entry q read
  let prepare := ((prepareUpdateOffsets lanes q read entry).seq (add P H S)).seq
    (adjustUpdateHead lanes entry.move)
  (prepare.seq (stepUpdateClauseLanes lanes).fragment).seq (clearUpdateOffsets lanes)

/-- Bound every loaded offset by a function of the alphabet sizes and window width. -/
def stepUpdateOffsetBound (states symbols width : Nat) : Nat :=
  states + symbols * width + symbols + width + 1

/-- A common bound on all six persistent bases. -/
def stepUpdateBaseBound (v : R → Nat) : Nat := v SB + v HB + v CB + v NSB + v NHB + v NCB

/-- Budget for offset preparation and the clamped head move. -/
def stepUpdatePrepareTimeBound (states symbols width : Nat) : Nat :=
  states + states + affineTime symbols symbols width + affineTime symbols symbols width +
    (5 * width + 2) + updateHeadTimeBound width width

/-- Uniform budget for one transition leaf at any position in the window. -/
def stepUpdateLeafTimeBound (states symbols : Nat) (v : R → Nat) : Nat :=
  let width := v W
  let offset := stepUpdateOffsetBound states symbols width
  stepUpdatePrepareTimeBound states symbols width +
    (12 * offsetLiteralTime (stepUpdateBaseBound lanes v) offset + 6) + 5 * (offset + 1)

private theorem runsValues_clear_loaded (lane : R) (x : BinaryWord) (v : R → Nat)
    (value : Nat) (hZero : v lane = 0) :
    (clear lane).RunsValues x (value + 1) (setValue lane value v) v := by
  have hClear := runsValues_clear lane x (setValue lane value v)
  rw [setValue_same, setValue_replace, ← hZero, setValue_current] at hClear
  exact hClear

omit [DecidableEq R] in
private theorem stepUpdateClauseLanes_disjoint : (stepUpdateClauseLanes lanes).Disjoint := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
    simp [stepUpdateClauseLanes, UpdateNameLanes.Disjoint]

/-- Prepare the six names, emit all three clauses, then clear the loaded offsets. -/
theorem runsOutput_stepUpdateLeaf (table : FiniteTable qCount symbolCount certificateCount)
    (q : Fin qCount) (read : Fin symbolCount) (x suffix : BinaryWord) (v : R → Nat)
    {t width : Nat} (i : Fin width) (hPosition : v P = i.val)
    (hBases : StepUpdateBases lanes v t qCount symbolCount width)
    (hReady : StepUpdateReady lanes v) :
    ∃ cost ≤ stepUpdateLeafTimeBound lanes qCount symbolCount v,
      (stepUpdateLeaf lanes table q read).RunsOutput x cost v v suffix
        ((CNF.mapAtoms indexedAtomName
          (Tableau.localUpdate table.windowAdvance t q i read)).reverse.foldl
          (fun out clause ↦ true :: (CNFCode.encodeClause clause ++ out)) suffix) := by
  obtain ⟨hSO, hNSO, hRO, hWO, hH, hM, hZ, hS, hC₁, hC₂⟩ := hReady
  let entry := table.entry q read
  let readOffset := symbolCount * v P + read.val
  let writtenOffset := symbolCount * v P + entry.written.val
  let dest := updateHeadPosition entry.move (v W) (v P)
  let withState := setValue SO q.val v
  let withStates := setValue NSO entry.next.val withState
  let withRead := setValue RO readOffset withStates
  let withOffsets := setValue WO writtenOffset withRead
  let copied := setValue H (v P) withOffsets
  let loaded := setValue H dest withOffsets
  have hState : (incrementBy SO q.val).RunsValues x q.val v withState := by
    simpa only [hSO, Nat.zero_add] using runsValues_incrementBy SO q.val x v
  have hNextState : (incrementBy NSO entry.next.val).RunsValues x entry.next.val
      withState withStates := by
    have hZero : withState NSO = 0 := by simpa [withState, setValue] using hNSO
    simpa only [hZero, Nat.zero_add] using runsValues_incrementBy NSO entry.next.val x withState
  have hRead : (accumulateAffine P RO M S symbolCount read.val).RunsValues x
      (affineTime symbolCount read.val (v P)) withStates withRead := by
    have hRun := runsValues_accumulateAffine P RO M S symbolCount read.val x withStates (by simp)
      (by simpa [withStates, withState, setValue] using hM)
      (by simpa [withStates, withState, setValue] using hS)
    have hOld : withStates RO = 0 := by simpa [withStates, withState, setValue] using hRO
    have hCarry : withStates P = v P := by simp [withStates, withState, setValue]
    simpa only [hOld, hCarry, Nat.zero_add] using hRun
  have hWritten : (accumulateAffine P WO M S symbolCount entry.written.val).RunsValues x
      (affineTime symbolCount entry.written.val (v P)) withRead withOffsets := by
    have hRun := runsValues_accumulateAffine P WO M S symbolCount entry.written.val x withRead
      (by simp) (by simpa [withRead, withStates, withState, setValue] using hM)
      (by simpa [withRead, withStates, withState, setValue] using hS)
    have hOld : withRead WO = 0 := by simpa [withRead, withStates, withState, setValue] using hWO
    have hCarry : withRead P = v P := by simp [withRead, withStates, withState, setValue]
    simpa only [hOld, hCarry, Nat.zero_add] using hRun
  have hCopy : (add P H S).RunsValues x (5 * v P + 2) withOffsets copied := by
    have hRun := runsValues_add P H S x withOffsets (by simp) (by simp) (by simp)
      (by simpa [withOffsets, withRead, withStates, withState, setValue] using hS)
    have hZero : withOffsets H = 0 := by
      simpa [withOffsets, withRead, withStates, withState, setValue] using hH
    have hCarry : withOffsets P = v P := by
      simp [withOffsets, withRead, withStates, withState, setValue]
    simpa only [hZero, hCarry, Nat.zero_add] using hRun
  obtain ⟨headCost, hHeadCost, hHeadRun⟩ := runsOutput_adjustUpdateHead lanes entry.move
    x suffix copied
    (by simpa [copied, withOffsets, withRead, withStates, withState, setValue] using hC₁)
    (by simpa [copied, withOffsets, withRead, withStates, withState, setValue] using hC₂)
    (by simpa [copied, withOffsets, withRead, withStates, withState, setValue] using hS)
  have hCopiedH : copied H = v P := setValue_same ..
  have hCopiedW : copied W = v W := by
    simp [copied, withOffsets, withRead, withStates, withState, setValue]
  rw [hCopiedH, hCopiedW] at hHeadCost hHeadRun
  have hHeadRun' : (adjustUpdateHead lanes entry.move).RunsOutput x headCost copied loaded
      suffix suffix := by
    simpa only [copied, setValue_replace, dest] using hHeadRun
  have hPrepare := (((((hState.seq hNextState).seq hRead).seq hWritten).seq hCopy).withOutput
    suffix).seq hHeadRun'
  have hDest : dest = (table.windowAdvance q i read).2.1.val := by
    change updateHeadPosition entry.move (v W) (v P) = _
    rw [hBases.width, hPosition, updateHeadPosition_eq]
    rfl
  have hNames : (stepUpdateClauseLanes lanes).Names loaded table.windowAdvance t q i read := by
    constructor <;> simp [stepUpdateClauseLanes, UpdateNameLanes.name, loaded, withOffsets,
      withRead, withStates, withState, setValue, indexedAtomName, Tableau.Atom.name,
      Tableau.Atom.time, Tableau.Atom.offset, hBases.state, hBases.head, hBases.cell,
      hBases.nextState, hBases.nextHead, hBases.nextCell, hPosition, readOffset, writtenOffset,
      hDest, entry, FiniteTable.windowAdvance, Nat.mul_comm symbolCount, Nat.add_assoc]
  have hEmit := (stepUpdateClauseLanes lanes).runsOutput_localUpdate x loaded suffix
    table.windowAdvance t q i read hNames (stepUpdateClauseLanes_disjoint lanes)
    (by simpa [stepUpdateClauseLanes, loaded, withOffsets, withRead, withStates, withState,
      setValue] using hZ)
    (by simpa [stepUpdateClauseLanes, loaded, withOffsets, withRead, withStates, withState,
      setValue] using hS)
  have hClearH := runsValues_clear_loaded H x withOffsets dest
    (by simpa [withOffsets, withRead, withStates, withState, setValue] using hH)
  have hClearWO := runsValues_clear_loaded WO x withRead writtenOffset
    (by simpa [withRead, withStates, withState, setValue] using hWO)
  have hClearRO := runsValues_clear_loaded RO x withStates readOffset
    (by simpa [withStates, withState, setValue] using hRO)
  have hClearNSO := runsValues_clear_loaded NSO x withState entry.next.val
    (by simpa [withState, setValue] using hNSO)
  have hClearSO := runsValues_clear_loaded SO x v q.val hSO
  have hCleanup := ((((hClearH.seq hClearWO).seq hClearRO).seq hClearNSO).seq hClearSO).withOutput
    ((CNF.mapAtoms indexedAtomName
      (Tableau.localUpdate table.windowAdvance t q i read)).reverse.foldl
      (fun out clause ↦ true :: (CNFCode.encodeClause clause ++ out)) suffix)
  have hPos : v P ≤ v W := by rw [hPosition, hBases.width]; exact Nat.le_of_lt i.isLt
  have hPrepareBound : q.val + entry.next.val + affineTime symbolCount read.val (v P) +
      affineTime symbolCount entry.written.val (v P) + (5 * v P + 2) + headCost ≤
      stepUpdatePrepareTimeBound qCount symbolCount (v W) := by
    have hAffine (constant : Nat) (h : constant ≤ symbolCount) :
        affineTime symbolCount constant (v P) ≤ affineTime symbolCount symbolCount (v W) := by
      apply (affineTime_mono symbolCount constant hPos).trans
      unfold affineTime
      omega
    have hRead := hAffine read.val (Nat.le_of_lt read.isLt)
    have hWritten := hAffine entry.written.val (Nat.le_of_lt entry.written.isLt)
    have hHead : updateHeadTimeBound (v P) (v W) ≤ updateHeadTimeBound (v W) (v W) := by
      unfold updateHeadTimeBound ifEqualTime
      omega
    have hq := q.isLt
    have hn := entry.next.isLt
    unfold stepUpdatePrepareTimeBound
    omega
  let maxOffset := stepUpdateOffsetBound qCount symbolCount (v W)
  have hScale := Nat.mul_le_mul_left symbolCount hPos
  have hReadLe : readOffset ≤ maxOffset := by
    have hTag := read.isLt
    dsimp [readOffset, maxOffset, stepUpdateOffsetBound]
    omega
  have hWrittenLe : writtenOffset ≤ maxOffset := by
    have hTag := entry.written.isLt
    dsimp [writtenOffset, maxOffset, stepUpdateOffsetBound]
    omega
  have hDestLe : dest ≤ maxOffset := by
    have h := updateHeadPosition_le entry.move (v W) (v P)
    dsimp [maxOffset, stepUpdateOffsetBound]
    omega
  have hStateLe : q.val ≤ maxOffset := by
    have h := q.isLt
    dsimp [maxOffset, stepUpdateOffsetBound]
    omega
  have hNextLe : entry.next.val ≤ maxOffset := by
    have h := entry.next.isLt
    dsimp [maxOffset, stepUpdateOffsetBound]
    omega
  have hHeadLe : v P ≤ maxOffset := by
    dsimp [maxOffset, stepUpdateOffsetBound]
    omega
  have hEmitBound : (stepUpdateClauseLanes lanes).time loaded ≤
      12 * offsetLiteralTime (stepUpdateBaseBound lanes v) maxOffset + 6 := by
    simp [UpdateClauseLanes.time, UpdateGuardLanes.time, UpdateNameLanes.time,
      stepUpdateClauseLanes, offsetLiteralTime, stepUpdateBaseBound,
      loaded, withOffsets, withRead, withStates, withState, setValue]
    omega
  have hCleanBound : dest + 1 + (writtenOffset + 1) + (readOffset + 1) + (entry.next.val + 1) +
      (q.val + 1) ≤ 5 * (maxOffset + 1) := by omega
  exact ⟨_, Nat.add_le_add (Nat.add_le_add hPrepareBound hEmitBound) hCleanBound,
    (hPrepare.seq hEmit).seq hCleanup⟩

/-- One state's chronological symbol list is fixed by the verifier's alphabet. -/
abbrev stepUpdatesAtPosition (table : FiniteTable qCount symbolCount certificateCount)
    (q : Fin qCount) : Fragment R :=
  sequence ((List.finRange symbolCount).reverse.map (stepUpdateLeaf lanes table q))

/-- For one state, count down the head positions without consuming the width. -/
abbrev stepUpdatesForState (table : FiniteTable qCount symbolCount certificateCount)
    (q : Fin qCount) : Fragment R :=
  (add W P S).seq (countdown P (stepUpdatesAtPosition lanes table q))

/-- Visit fixed states and symbols in descending order around the dynamic head loop. -/
abbrev stepUpdatesFragment (table : FiniteTable qCount symbolCount certificateCount) : Fragment R :=
  sequence ((List.finRange qCount).reverse.map (stepUpdatesForState lanes table))

/-- Prepend a clause with numeric names and the enclosing formula's clause marker. -/
def prependIndexedUpdateClause {width : Nat} (out : BinaryWord)
    (clause : CNF.Clause (Tableau.Atom (Fin qCount) (Fin symbolCount) width)) : BinaryWord :=
  true :: (CNFCode.encodeClause (clause.map (CNF.Literal.map indexedAtomName)) ++ out)

/-- Output of one transition, in the order in which it prepends its clauses. -/
def stepUpdateOutput (table : FiniteTable qCount symbolCount certificateCount)
    (t : Nat) (q : Fin qCount) {width : Nat} (i : Fin width) (read : Fin symbolCount)
    (suffix : BinaryWord) : BinaryWord :=
  (Tableau.localUpdate table.windowAdvance t q i read).reverse.foldl
    prependIndexedUpdateClause suffix

/-- Output of the update section of `FiniteTable.foldStepClauses`. -/
def stepUpdatesOutput (table : FiniteTable qCount symbolCount certificateCount)
    (t width : Nat) (suffix : BinaryWord) : BinaryWord :=
  Traversal.foldFinDesc qCount (fun out q ↦ Traversal.foldFinDesc width (fun out i ↦
    Traversal.foldFinDesc symbolCount (fun out read ↦ stepUpdateOutput table t q i read out) out)
    out) suffix

/-- In the indexed traversal, the copy section supplies the suffix for the update section. -/
theorem foldStepClauses_eq_updateOutput
    (table : FiniteTable qCount symbolCount certificateCount) (t width : Nat)
    (suffix : BinaryWord) :
    table.foldStepClauses (width := width) prependIndexedUpdateClause suffix t =
      stepUpdatesOutput table t width (Traversal.foldFinDesc width (fun out i ↦
        Traversal.foldFinDesc width (fun out j ↦ Traversal.foldFinDesc symbolCount
          (fun out read ↦ (Tableau.localCopy (Q := Fin qCount) t i j read).reverse.foldl
            prependIndexedUpdateClause out) out) out) suffix) := rfl

/-- The state-loop budget bounds every transition key and head position. -/
def stepUpdatesStateTimeBound (states symbols : Nat) (v : R → Nat) : Nat :=
  (5 * v W + 2) + (v W * (symbols * stepUpdateLeafTimeBound lanes states symbols v + 1) + 1)

/-- Uniform per-time budget for all transition-update clauses. -/
def stepUpdatesTimeBound (states symbols : Nat) (v : R → Nat) : Nat :=
  states * stepUpdatesStateTimeBound lanes states symbols v

private theorem runsOutput_stepUpdatesAtPosition
    (table : FiniteTable qCount symbolCount certificateCount) (q : Fin qCount)
    (x suffix : BinaryWord) (v : R → Nat) {t width : Nat} (i : Fin width)
    (hPos : v P = i.val) (hBases : StepUpdateBases lanes v t qCount symbolCount width)
    (hReady : StepUpdateReady lanes v) :
    ∃ cost ≤ symbolCount * stepUpdateLeafTimeBound lanes qCount symbolCount v,
      (stepUpdatesAtPosition lanes table q).RunsOutput x cost v v suffix
        (Traversal.foldFinDesc symbolCount
          (fun out read ↦ stepUpdateOutput table t q i read out) suffix) := by
  let keys := (List.finRange symbolCount).reverse
  have hBody (read : Fin symbolCount) (_ : read ∈ keys) (out : BinaryWord) :
      ∃ cost ≤ stepUpdateLeafTimeBound lanes qCount symbolCount v,
        (stepUpdateLeaf lanes table q read).RunsOutput x cost v v out
          (stepUpdateOutput table t q i read out) := by
    change ∃ cost ≤ stepUpdateLeafTimeBound lanes qCount symbolCount v,
      (stepUpdateLeaf lanes table q read).RunsOutput x cost v v out
        ((Tableau.localUpdate table.windowAdvance t q i read).reverse.foldl
          (fun acc clause ↦ true :: (CNFCode.encodeClause
            (clause.map (CNF.Literal.map indexedAtomName)) ++ acc)) out)
    simpa only [CNF.mapAtoms, ← List.map_reverse, List.foldl_map, Function.comp_def] using
        runsOutput_stepUpdateLeaf lanes table q read x out v i hPos hBases hReady
  rw [Traversal.foldFinDesc_eq]
  simpa only [keys, List.length_reverse, List.length_finRange] using
    runsOutput_sequence keys (stepUpdateLeaf lanes table q)
      (fun out read ↦ stepUpdateOutput table t q i read out) x v
      (stepUpdateLeafTimeBound lanes qCount symbolCount v) hBody suffix

private theorem runsOutput_stepUpdatesForState
    (table : FiniteTable qCount symbolCount certificateCount) (q : Fin qCount)
    (x suffix : BinaryWord) (v : R → Nat) {t width : Nat}
    (hPositionZero : v P = 0) (hBases : StepUpdateBases lanes v t qCount symbolCount width)
    (hReady : StepUpdateReady lanes v) :
    ∃ cost ≤ stepUpdatesStateTimeBound lanes qCount symbolCount v,
      (stepUpdatesForState lanes table q).RunsOutput x cost v v suffix
        (Traversal.foldFinDesc width (fun out i ↦ Traversal.foldFinDesc symbolCount
          (fun out read ↦ stepUpdateOutput table t q i read out) out) suffix) := by
  let update (out : BinaryWord) (j : Nat) :=
    if h : j < width then Traversal.foldFinDesc symbolCount
      (fun acc read ↦ stepUpdateOutput table t q ⟨j, h⟩ read acc) out
    else out
  let bound := symbolCount * stepUpdateLeafTimeBound lanes qCount symbolCount v
  have hBody (j : Nat) (hj : j < v W) (out : BinaryWord) :
      ∃ cost ≤ bound, (stepUpdatesAtPosition lanes table q).RunsOutput x cost
        (setValue P j v) (setValue P j v) out (update out j) := by
    let current := setValue P j v
    have hReady' : StepUpdateReady lanes current := by
      simpa [StepUpdateReady, current, setValue] using hReady
    have hBases' : StepUpdateBases lanes current t qCount symbolCount width := by
      exact ⟨by simpa [current, setValue] using hBases.width,
        by simpa [current, setValue] using hBases.state,
        by simpa [current, setValue] using hBases.head,
        by simpa [current, setValue] using hBases.cell,
        by simpa [current, setValue] using hBases.nextState,
        by simpa [current, setValue] using hBases.nextHead,
        by simpa [current, setValue] using hBases.nextCell⟩
    have hLimit : j < width := hBases.width ▸ hj
    have hRun := runsOutput_stepUpdatesAtPosition lanes table q x out current ⟨j, hLimit⟩
      (setValue_same ..) hBases' hReady'
    simpa [stepUpdateLeafTimeBound, stepUpdateBaseBound, current, setValue,
      update, bound, hLimit] using hRun
  have hScratch : v S = 0 := by
    obtain ⟨_, _, _, _, _, _, _, hs, _, _⟩ := hReady
    exact hs
  obtain ⟨cost, hCost, hRun⟩ := runsOutput_initializedCountdown W P S
    (stepUpdatesAtPosition lanes table q) x v bound update
    (by simp) (by simp) (by simp) hPositionZero hScratch hBody suffix
  have hOutput : (List.range (v W)).reverse.foldl update suffix =
      Traversal.foldFinDesc width (fun out i ↦ Traversal.foldFinDesc symbolCount
        (fun out read ↦ stepUpdateOutput table t q i read out) out) suffix := by
    rw [hBases.width, ← foldFinDesc_values]
    apply congrArg (fun f ↦ Traversal.foldFinDesc width f suffix)
    funext out i
    simp [update, i.isLt]
  rw [hOutput] at hRun
  exact ⟨cost, hCost, hRun⟩

/-- Emit the complete update section for one time, restoring all work and persistent lanes. -/
theorem runsOutput_stepUpdatesFragment
    (table : FiniteTable qCount symbolCount certificateCount) (x suffix : BinaryWord)
    (v : R → Nat) {t width : Nat} (hPositionZero : v P = 0)
    (hBases : StepUpdateBases lanes v t qCount symbolCount width)
    (hReady : StepUpdateReady lanes v) :
    ∃ cost ≤ stepUpdatesTimeBound lanes qCount symbolCount v,
      (stepUpdatesFragment lanes table).RunsOutput x cost v v suffix
        (stepUpdatesOutput table t width suffix) := by
  let states := (List.finRange qCount).reverse
  let update (out : BinaryWord) (q : Fin qCount) := Traversal.foldFinDesc width
    (fun out i ↦ Traversal.foldFinDesc symbolCount
      (fun out read ↦ stepUpdateOutput table t q i read out) out) out
  have hBody (q : Fin qCount) (_ : q ∈ states) (out : BinaryWord) :
      ∃ cost ≤ stepUpdatesStateTimeBound lanes qCount symbolCount v,
        (stepUpdatesForState lanes table q).RunsOutput x cost v v out (update out q) :=
    runsOutput_stepUpdatesForState lanes table q x out v hPositionZero hBases hReady
  simpa only [stepUpdatesTimeBound, stepUpdatesOutput, Traversal.foldFinDesc_eq qCount,
    states, update, List.length_reverse, List.length_finRange] using
      runsOutput_sequence states (stepUpdatesForState lanes table) update x v
        (stepUpdatesStateTimeBound lanes qCount symbolCount v) hBody suffix

omit [DecidableEq R] in
/-- The per-time update cost is polynomial in the width and the six supplied bases. -/
theorem stepUpdatesTimeBound_polynomiallyBounded (states symbols : Nat) {v : Nat → R → Nat}
    (hValues : ∀ r, PolynomiallyBounded (fun n ↦ v n r)) :
    PolynomiallyBounded (fun n ↦ stepUpdatesTimeBound lanes states symbols (v n)) := by
  let constant := PolynomiallyBounded.const
  have width := hValues W
  have copies := (((constant 5).mul width).add (constant 2))
  have headCompare := (((constant 6).mul ((width.add (constant 1)).add width)).add (constant 6))
  have movement := (constant 1).add (headCompare.add (constant 1))
  have affine := affineTime_polynomiallyBounded symbols symbols width
  have prepare := ((((constant states).add (constant states)).add affine).add affine).add copies
  have base := (((((hValues SB).add (hValues HB)).add (hValues CB)).add (hValues NSB)).add
    (hValues NHB)).add (hValues NCB)
  have offset := ((((constant states).add ((constant symbols).mul width)).add
    (constant symbols)).add width).add (constant 1)
  have emission := ((constant 12).mul (offsetLiteralTime_polynomiallyBounded base offset)).add
    (constant 6)
  have cleanup := (constant 5).mul (offset.add (constant 1))
  have leaf := ((prepare.add movement).add emission).add cleanup
  have work := (constant symbols).mul leaf
  have headLoop := copies.add ((width.mul (work.add (constant 1))).add (constant 1))
  exact (constant states).mul headLoop

end PvsNP.CookLevin
