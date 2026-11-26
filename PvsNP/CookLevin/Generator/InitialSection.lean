module

public import PvsNP.CookLevin.Generator.InitialCells
public import PvsNP.CookLevin.Generator.InitialGaps
public import PvsNP.CookLevin.Generator.InitialHeader
public import PvsNP.CookLevin.Generator.InitialParameters

/-! # Complete register program for the initial tableau section -/

@[expose] public section

namespace PvsNP.CookLevin

open RegisterMachine RegisterMachine.Fragment

/-- Persistent parameters, computed boundaries, and work registers of the initial section. -/
inductive InitialSectionLane where
  | length | offset | capacity | width | lower | upper | gapBase | cellBase
  | left | right | leftOffset | rightOffset | successor | relative
  | work | literal | leftCopy | rightCopy | scratch | zero
  deriving DecidableEq

/-- Share the input parameters and the result lanes of the boundary calculation. -/
def initialSectionParameterCode : InitialParameterLane ↪ InitialSectionLane where
  toFun
    | .length => .length
    | .offset => .offset
    | .capacity => .capacity
    | .width => .width
    | .lower => .lower
    | .upper => .upper
    | .base => .gapBase
    | .scratch => .scratch
  inj' a b h := by cases a <;> cases b <;> simp_all

/-- Share the boundaries, width, and temporary registers with the gap traversal. -/
def initialSectionGapCode : InitialGapLane ↪ InitialSectionLane where
  toFun
    | .width => .width
    | .multiplier => .work
    | .gap .left => .left
    | .gap .right => .right
    | .gap .lower => .lower
    | .gap .upper => .upper
    | .gap .atomBase => .gapBase
    | .gap .leftOffset => .leftOffset
    | .gap .rightOffset => .rightOffset
    | .gap .successor => .successor
    | .gap .index => .literal
    | .gap .leftCopy => .leftCopy
    | .gap .rightCopy => .rightCopy
    | .gap .scratch => .scratch
  inj' a b h := by
    rcases a with _ | _ | a <;> rcases b with _ | _ | b
    all_goals first
      | rfl
      | cases a <;> cases b <;> simp_all
      | cases a <;> simp_all
      | cases b <;> simp_all
      | simp_all

/-- The cell traversal uses its own base and relative index. -/
def initialSectionCellCode : InitialCellLane ↪ InitialSectionLane where
  toFun
    | .length => .length
    | .offset => .offset
    | .width => .width
    | .lower => .lower
    | .upper => .upper
    | .position => .left
    | .base => .cellBase
    | .relative => .relative
    | .work => .work
    | .literal => .literal
    | .leftCopy => .leftCopy
    | .rightCopy => .rightCopy
    | .scratch => .scratch
  inj' a b h := by cases a <;> cases b <;> simp_all

variable {R : Type} (lanes : InitialSectionLane ↪ R)
variable {states symbols certificates : Nat}
variable (table : FiniteTable states symbols certificates)

local notation "P" => initialSectionParameterCode.trans lanes
local notation "G" => initialSectionGapCode.trans lanes
local notation "C" => initialSectionCellCode.trans lanes

/-- The section enters with only its four persistent data registers populated. -/
def InitialSectionReady (v : R → Nat) : Prop :=
  ∀ role, role ∉ [InitialSectionLane.length, .offset, .capacity, .width] → v (lanes role) = 0

/-- Link parameter setup, gaps, cells, then the head and state clauses. -/
def initialSectionFragment : Fragment R :=
  (((initialParametersFragment P states).seq (initialGapsFragment G symbols table.blank.val)).seq
    (initialCellsFragment C table)).seq
      (initialHeaderFragment (lanes .offset) (lanes .zero) (lanes .literal) (lanes .scratch)
        states table.initial.val)

/-- Prepend one framed clause after replacing its indexed atoms by their natural names. -/
def emitNamedTableauClause {width : Nat} (out : BinaryWord)
    (clause : CNF.Clause (Tableau.Atom (Fin states) (Fin symbols) width)) : BinaryWord :=
  true :: (CNFCode.encodeClause (clause.map (CNF.Literal.map indexedAtomName)) ++ out)

/-- The initial section's output, prepended to the previously emitted suffix. -/
def initialSectionOutput {width : Nat} (x suffix : BinaryWord) (head : Fin width)
    (capacity : Nat) : BinaryWord :=
  table.foldInitialClauses emitNamedTableauClause suffix head x capacity

/-- A polynomial budget for setup and all three clause-emitting passes. -/
def initialSectionTimeBound (length offset capacity width : Nat) : Nat :=
  let lower := offset + length + 1
  let upper := lower + capacity
  initialParametersTime length offset capacity width states +
    initialGapsTimeBound width symbols table.blank.val (states + width) lower upper +
    initialCellsTimeBound table length offset width lower upper +
    initialHeaderTime states table.initial.val offset

theorem initialSectionTimeBound_polynomiallyBounded {length offset capacity width : Nat → Nat}
    (hLength : PolynomiallyBounded length) (hOffset : PolynomiallyBounded offset)
    (hCapacity : PolynomiallyBounded capacity) (hWidth : PolynomiallyBounded width) :
    PolynomiallyBounded (fun n ↦ initialSectionTimeBound table (length n) (offset n)
      (capacity n) (width n)) := by
  let k := PolynomiallyBounded.const
  have hLo := (hOffset.add hLength).add (k 1)
  have hHi := hLo.add hCapacity
  have hBase := (k states).add hWidth
  have hParameters := initialParametersTime_polynomiallyBounded states
    hLength hOffset hCapacity hWidth
  have hGaps := initialGapsTimeBound_polynomiallyBounded symbols table.blank.val hWidth
    hBase hLo hHi
  have hCells := initialCellsTimeBound_polynomiallyBounded table hLength hOffset hWidth hLo hHi
  have hHeader := initialHeaderTime_polynomiallyBounded states table.initial.val hOffset
  exact ((hParameters.add hGaps).add hCells).add hHeader

variable [DecidableEq R]

/-- Only the certificate boundaries and gap name base retain new values at the exit. -/
abbrev initialSectionValues (states : Nat) (v : R → Nat) : R → Nat :=
  initialParametersValues P states v

theorem initialSectionValues_eq (states : Nat) (v : R → Nat) :
    initialSectionValues lanes states v =
      setValue (lanes .gapBase) (v (lanes .width) + states)
        (setValue (lanes .upper) (v (lanes .offset) + v (lanes .length) + 1 + v (lanes .capacity))
          (setValue (lanes .lower) (v (lanes .offset) + v (lanes .length) + 1) v)) := rfl

/-- Registers other than the three prepared operands retain their values. -/
theorem initialSectionValues_other (states : Nat) (v : R → Nat) (role : InitialSectionLane)
    (hRole : role ∉ [.lower, .upper, .gapBase]) :
    initialSectionValues lanes states v (lanes role) = v (lanes role) := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hRole
  obtain ⟨hLo, hHi, hBase⟩ := hRole
  simp [initialSectionValues_eq, setValue, hLo, hHi, hBase]

private theorem initialSectionPreparedZero (states : Nat) (v : R → Nat)
    (hReady : InitialSectionReady lanes v) (role : InitialSectionLane)
    (hRole : role ∉ [.length, .offset, .capacity, .width, .lower, .upper, .gapBase]) :
    initialSectionValues lanes states v (lanes role) = 0 := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hRole
  obtain ⟨hN, hT, hCap, hW, hLo, hHi, hBase⟩ := hRole
  rw [initialSectionValues_other lanes states v role (by simp [hLo, hHi, hBase])]
  exact hReady role (by simp [hN, hT, hCap, hW])

omit [DecidableEq R] in
private theorem initialSectionOutput_parts {width : Nat} (x suffix : BinaryWord)
    (head : Fin width) (capacity : Nat) :
    initialHeaderOutput states table.initial.val head.val
      (initialCellsOutput table x capacity head.val width
        (initialGapsOutput width symbols table.blank.val (states + width)
          (head.val + x.length + 1) (head.val + x.length + 1 + capacity) suffix)) =
      initialSectionOutput table x suffix head capacity := by
  have hCell (out : BinaryWord) (i : Fin width) :
      initialCellOutput table x capacity head.val width out i.val =
        (table.initialCell x capacity head.val i).reverse.foldl emitNamedTableauClause out := by
    rw [initialCellOutput_eq, CNF.mapAtoms, ← List.map_reverse, List.foldl_map]
    rfl
  unfold initialSectionOutput FiniteTable.foldInitialClauses
  rw [initialGapsOutput_eq, initialCellsOutput, ← foldFinDesc_values, initialHeaderOutput_eq]
  simp only [hCell, emitNamedTableauClause, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, List.foldl_cons, List.foldl_nil]
  rfl

/-- The linked section emits all initial clauses and keeps the persistent input parameters. -/
theorem run_initialSectionFragment {width : Nat} (x suffix : BinaryWord)
    (capacity : Nat) (head : Fin width) (v : R → Nat)
    (hLength : v (lanes .length) = x.length) (hOffset : v (lanes .offset) = head.val)
    (hCapacity : v (lanes .capacity) = capacity) (hWidth : v (lanes .width) = width)
    (hReady : InitialSectionReady lanes v) :
    ∃ cost ≤ initialSectionTimeBound table x.length head.val capacity width,
      (initialSectionFragment lanes table).RunsOutput x cost v
        (initialSectionValues lanes states v) suffix
        (initialSectionOutput table x suffix head capacity) := by
  let prepared := initialSectionValues lanes states v
  let lower := head.val + x.length + 1
  let upper := lower + capacity
  have hInitialReady : InitialParametersReady P v :=
    ⟨hReady .lower (by decide), hReady .upper (by decide), hReady .gapBase (by decide),
      hReady .scratch (by decide)⟩
  have hPrepare := run_initialParametersFragment P states x v hInitialReady
  change (initialParametersFragment P states).RunsValues x
    (initialParametersTime (v (lanes .length)) (v (lanes .offset)) (v (lanes .capacity))
      (v (lanes .width)) states) v prepared at hPrepare
  rw [hLength, hOffset, hCapacity, hWidth] at hPrepare
  have hZero (role : InitialSectionLane) (hRole :
      role ∉ [.length, .offset, .capacity, .width, .lower, .upper, .gapBase]) :
      prepared (lanes role) = 0 :=
    initialSectionPreparedZero lanes states v hReady role hRole
  have hN : prepared (lanes .length) = x.length :=
    (initialSectionValues_other lanes states v .length (by decide)).trans hLength
  have hT : prepared (lanes .offset) = head.val :=
    (initialSectionValues_other lanes states v .offset (by decide)).trans hOffset
  have hW : prepared (lanes .width) = width :=
    (initialSectionValues_other lanes states v .width (by decide)).trans hWidth
  have hLo : prepared (lanes .lower) = lower := by
    simp [prepared, initialSectionValues_eq, setValue, lower, hLength, hOffset]
  have hHi : prepared (lanes .upper) = upper := by
    simp [prepared, initialSectionValues_eq, setValue, upper, lower, hLength, hOffset, hCapacity]
  have hBase : prepared (lanes .gapBase) = states + width := by
    simp [prepared, initialSectionValues_eq, hWidth, Nat.add_comm]
  have hGapReady : InitialGapsReady G prepared :=
    ⟨hZero .work (by decide), hZero .leftOffset (by decide), hZero .rightOffset (by decide),
      hZero .successor (by decide),
      hZero .literal (by decide), hZero .leftCopy (by decide), hZero .rightCopy (by decide),
      hZero .scratch (by decide)⟩
  obtain ⟨gapCost, hGapCost, hGap⟩ := run_initialGapsFragment G symbols table.blank.val
    x suffix prepared hGapReady (hZero .left (by decide)) (hZero .right (by decide))
  let gapOut := initialGapsOutput width symbols table.blank.val (states + width) lower upper suffix
  change gapCost ≤ initialGapsTimeBound (prepared (lanes .width)) symbols table.blank.val
    (prepared (lanes .gapBase)) (prepared (lanes .lower)) (prepared (lanes .upper)) at hGapCost
  change (initialGapsFragment G symbols table.blank.val).RunsOutput x gapCost prepared prepared
    suffix (initialGapsOutput (prepared (lanes .width)) symbols table.blank.val
      (prepared (lanes .gapBase)) (prepared (lanes .lower)) (prepared (lanes .upper)) suffix)
    at hGap
  rw [hW, hBase, hLo, hHi] at hGapCost hGap
  have hCellParams : InitialCellParameters C x capacity head.val width prepared :=
    ⟨hN, hT, hW, hLo, hHi⟩
  have hCellReady : InitialCellReady C prepared :=
    ⟨⟨hZero .relative (by decide), hZero .work (by decide), hZero .literal (by decide),
      hZero .leftCopy (by decide), hZero .rightCopy (by decide), hZero .scratch (by decide)⟩,
      hZero .cellBase (by decide)⟩
  obtain ⟨cellCost, hCellCost, hCells⟩ := runsOutput_initialCells C table x gapOut
    capacity head.val width prepared hCellParams (hZero .left (by decide)) hCellReady
  change cellCost ≤ initialCellsTimeBound table x.length head.val width lower upper
    at hCellCost
  rw [← initialCellsOutput_eq table x capacity head.val width gapOut] at hCells
  let cellOut := initialCellsOutput table x capacity head.val width gapOut
  have hHeaderLanes : [lanes .offset, lanes .zero, lanes .literal, lanes .scratch].Nodup :=
    List.Nodup.map lanes.injective
      (by decide : [InitialSectionLane.offset, .zero, .literal, .scratch].Nodup)
  have hHeader := run_initialHeaderFragment (lanes .offset) (lanes .zero) (lanes .literal)
    (lanes .scratch) states table.initial.val x cellOut prepared hHeaderLanes
      (hZero .zero (by decide)) (hZero .literal (by decide)) (hZero .scratch (by decide))
  rw [hT] at hHeader
  rw [show initialHeaderOutput states table.initial.val head.val cellOut =
      initialSectionOutput table x suffix head capacity from
    initialSectionOutput_parts table x suffix head capacity] at hHeader
  refine ⟨initialParametersTime x.length head.val capacity width states + gapCost + cellCost +
    initialHeaderTime states table.initial.val head.val, ?_, ?_⟩
  · unfold initialSectionTimeBound
    change _ ≤ initialParametersTime x.length head.val capacity width states +
      initialGapsTimeBound width symbols table.blank.val (states + width) lower upper +
      initialCellsTimeBound table x.length head.val width lower upper +
      initialHeaderTime states table.initial.val head.val
    omega
  · exact (((hPrepare.withOutput suffix).seq hGap).seq hCells).seq hHeader

/-- At the center of a width-two-horizon-plus-one window, the same run uses the actual
initial head of the indexed verifier tableau. -/
theorem run_initialSectionWindow (x suffix : BinaryWord) (capacity time : Nat) (v : R → Nat)
    (hLength : v (lanes .length) = x.length) (hOffset : v (lanes .offset) = time)
    (hCapacity : v (lanes .capacity) = capacity) (hWidth : v (lanes .width) = 2 * time + 1)
    (hReady : InitialSectionReady lanes v) :
    ∃ cost ≤ initialSectionTimeBound table x.length time capacity (2 * time + 1),
      (initialSectionFragment lanes table).RunsOutput x cost v
        (initialSectionValues lanes states v) suffix
        (initialSectionOutput table x suffix (Machine.windowCenter time) capacity) :=
  run_initialSectionFragment lanes table x suffix capacity (Machine.windowCenter time) v
    hLength hOffset hCapacity hWidth hReady

end PvsNP.CookLevin
