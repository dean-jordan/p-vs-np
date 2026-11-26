module

public import PvsNP.CookLevin.Generator.FiniteTable
public import PvsNP.CookLevin.Generator.FrameNames
public import PvsNP.TuringMachine.Registers.Conditional
public import PvsNP.TuringMachine.Registers.OutputRuns

/-! # Emitting the tableau's local copy clause -/

@[expose] public section

namespace PvsNP.CookLevin

open RegisterMachine RegisterMachine.Fragment

/-- Registers holding the local copy coordinates, atom name bases, and temporary values. -/
structure CopyClauseLanes (R : Type) where
  head : R
  cell : R
  cellOffset : R
  headBase : R
  cellBase : R
  nextCellBase : R
  literalIndex : R
  literalScratch : R
  compareHead : R
  compareCell : R
  compareScratch : R

namespace CopyClauseLanes

variable {R : Type} (lanes : CopyClauseLanes R)

/-- Distinctness is needed within each operation. The comparison and emission
may share scratch registers because each operation restores them. -/
structure Disjoint : Prop where
  headLiteral : [lanes.headBase, lanes.head, lanes.literalIndex, lanes.literalScratch].Nodup
  cellLiteral : [lanes.cellBase, lanes.cellOffset, lanes.literalIndex, lanes.literalScratch].Nodup
  nextLiteral :
    [lanes.nextCellBase, lanes.cellOffset, lanes.literalIndex, lanes.literalScratch].Nodup
  headCompare : [lanes.head, lanes.compareHead, lanes.compareCell, lanes.compareScratch].Nodup
  cellCompare : [lanes.cell, lanes.compareHead, lanes.compareCell, lanes.compareScratch].Nodup

/-- The names and signs of a copy clause when the head and copied cell differ. -/
def clause (values : R → Nat) : CNF.Clause Nat :=
  [.neg (values lanes.headBase + values lanes.head),
    .neg (values lanes.cellBase + values lanes.cellOffset),
    .pos (values lanes.nextCellBase + values lanes.cellOffset)]

/-- The copy clause is present only for a cell away from the head. -/
def formula (values : R → Nat) : CNF.Formula Nat :=
  if values lanes.head = values lanes.cell then [] else [lanes.clause values]

/-- Prepend one framed copy clause by emitting the terminator and literals backwards. -/
def rawFragment : Fragment R :=
  let next := emitOffsetLiteral lanes.nextCellBase lanes.cellOffset
    lanes.literalIndex lanes.literalScratch true
  let cell := emitOffsetLiteral lanes.cellBase lanes.cellOffset
    lanes.literalIndex lanes.literalScratch false
  let head := emitOffsetLiteral lanes.headBase lanes.head
    lanes.literalIndex lanes.literalScratch false
  ((((emitBit false).seq next).seq cell).seq head).seq (emitBit true)

/-- Compare the coordinates and emit the clause only for different positions. -/
def fragment : Fragment R :=
  ifEqual lanes.head lanes.cell lanes.compareHead lanes.compareCell lanes.compareScratch
    skip lanes.rawFragment

/-- Cost of emitting one framed clause. -/
def rawTime (values : R → Nat) : Nat :=
  1 + offsetLiteralTime (values lanes.nextCellBase) (values lanes.cellOffset) +
    offsetLiteralTime (values lanes.cellBase) (values lanes.cellOffset) +
    offsetLiteralTime (values lanes.headBase) (values lanes.head) + 1

/-- Exact cost, including the coordinate comparison and any selected emission. -/
def time (values : R → Nat) : Nat :=
  ifEqualTime (values lanes.head) (values lanes.cell) +
    if values lanes.head = values lanes.cell then 0 else lanes.rawTime values

/-- A uniform cost bound for both comparison outcomes. -/
def timeBound (values : R → Nat) : Nat :=
  ifEqualTime (values lanes.head) (values lanes.cell) + lanes.rawTime values

theorem time_le_timeBound (values : R → Nat) : lanes.time values ≤ lanes.timeBound values := by
  unfold time timeBound
  split <;> omega

theorem timeBound_polynomiallyBounded {values : Nat → R → Nat}
    (hValues : ∀ r, PolynomiallyBounded (fun n ↦ values n r)) :
    PolynomiallyBounded (fun n ↦ lanes.timeBound (values n)) := by
  let lit := PolynomiallyBounded.const
  have hCompare := ((lit 6).mul ((hValues lanes.head).add (hValues lanes.cell))).add (lit 6)
  have hNext := offsetLiteralTime_polynomiallyBounded
    (hValues lanes.nextCellBase) (hValues lanes.cellOffset)
  have hCell := offsetLiteralTime_polynomiallyBounded
    (hValues lanes.cellBase) (hValues lanes.cellOffset)
  have hHead := offsetLiteralTime_polynomiallyBounded (hValues lanes.headBase) (hValues lanes.head)
  exact hCompare.add (((((lit 1).add hNext).add hCell).add hHead).add (lit 1))

theorem time_polynomiallyBounded {values : Nat → R → Nat}
    (hValues : ∀ r, PolynomiallyBounded (fun n ↦ values n r)) :
    PolynomiallyBounded (fun n ↦ lanes.time (values n)) :=
  (lanes.timeBound_polynomiallyBounded hValues).mono fun n ↦ lanes.time_le_timeBound (values n)

variable [DecidableEq R]

private theorem runsOutput_bit (bit : Bool) (x : BinaryWord) (values : R → Nat)
    (suffix : BinaryWord) : (emitBit bit).RunsOutput x 1 values values suffix (bit :: suffix) :=
  run_emitBit bit x (⟨none, values, none, suffix⟩ : Config R Unit) rfl

private theorem runsOutput_offsetLiteral (base offset index scratch : R) (positive : Bool)
    (x : BinaryWord) (values : R → Nat) (suffix : BinaryWord)
    (hLanes : [base, offset, index, scratch].Nodup)
    (hIndex : values index = 0) (hScratch : values scratch = 0) :
    (emitOffsetLiteral base offset index scratch positive).RunsOutput x
      (offsetLiteralTime (values base) (values offset)) values values suffix
      (true :: (CNFCode.encodeLiteral
        (if positive then .pos (values base + values offset)
          else .neg (values base + values offset)) ++ suffix)) :=
  run_emitOffsetLiteral base offset index scratch positive x
    (⟨none, values, none, suffix⟩ : Config R Unit) hLanes hIndex hScratch rfl

/-- Emitting the clause prepends its exact binary encoding and restores every register. -/
theorem runsOutput_rawFragment (x : BinaryWord) (values : R → Nat) (suffix : BinaryWord)
    (hHead : [lanes.headBase, lanes.head, lanes.literalIndex, lanes.literalScratch].Nodup)
    (hCell : [lanes.cellBase, lanes.cellOffset, lanes.literalIndex, lanes.literalScratch].Nodup)
    (hNext : [lanes.nextCellBase, lanes.cellOffset, lanes.literalIndex, lanes.literalScratch].Nodup)
    (hIndex : values lanes.literalIndex = 0) (hScratch : values lanes.literalScratch = 0) :
    lanes.rawFragment.RunsOutput x (lanes.rawTime values) values values suffix
      (true :: (CNFCode.encodeClause (lanes.clause values) ++ suffix)) := by
  have hEnd := runsOutput_bit false x values suffix
  have hNextLine := hEnd.seq (runsOutput_offsetLiteral lanes.nextCellBase lanes.cellOffset
    lanes.literalIndex lanes.literalScratch true x values _ hNext hIndex hScratch)
  have hCellLine := hNextLine.seq (runsOutput_offsetLiteral lanes.cellBase lanes.cellOffset
    lanes.literalIndex lanes.literalScratch false x values _ hCell hIndex hScratch)
  have hHeadLine := hCellLine.seq (runsOutput_offsetLiteral lanes.headBase lanes.head
    lanes.literalIndex lanes.literalScratch false x values _ hHead hIndex hScratch)
  have hRun := hHeadLine.seq (runsOutput_bit true x values _)
  simpa only [rawFragment, rawTime, clause, ite_true, Bool.false_eq_true, ite_false,
    CNFCode.encodeClause_cons, CNFCode.encodeClause_nil, List.cons_append, List.append_assoc,
    List.singleton_append, List.nil_append] using hRun

/-- The fragment emits exactly the framed clauses of the numeric copy formula. -/
theorem runsOutput_fragment (x : BinaryWord) (values : R → Nat) (suffix : BinaryWord)
    (hLanes : lanes.Disjoint)
    (hIndex : values lanes.literalIndex = 0) (hLiteralScratch : values lanes.literalScratch = 0)
    (hHeadZero : values lanes.compareHead = 0) (hCellZero : values lanes.compareCell = 0)
    (hCompareScratch : values lanes.compareScratch = 0) :
    lanes.fragment.RunsOutput x (lanes.time values) values values suffix
      ((lanes.formula values).reverse.foldl
        (fun out clause ↦ true :: (CNFCode.encodeClause clause ++ out)) suffix) := by
  have hHead := hLanes.headCompare
  have hCell := hLanes.cellCompare
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or,
    not_false_eq_true, List.nodup_nil, and_true] at hHead hCell
  obtain ⟨⟨hHeadCopy, _, hHeadScratch⟩, ⟨hCopies, hHeadCopyScratch⟩, hCellCopyScratch⟩ := hHead
  obtain ⟨⟨hCellHeadCopy, hCellCopy, hCellScratch⟩, _, _⟩ := hCell
  let cfg : Config R Unit := ⟨none, values, none, suffix⟩
  by_cases hEq : values lanes.head = values lanes.cell
  · have hRun := run_ifEqual_eq (equal := skip) (different := lanes.rawFragment) x
      hHeadCopy hHeadScratch hCellHeadCopy hCellCopy hCellScratch hCopies hHeadCopyScratch
      hCellCopyScratch cfg hHeadZero hCellZero hCompareScratch hEq
      (runsOutput_skip x values suffix) rfl
    simpa only [RunsOutput, fragment, time, formula, ite_eq_left hEq, List.reverse_nil,
      List.foldl_nil, Nat.add_zero, cfg] using hRun
  · have hRaw := lanes.runsOutput_rawFragment x values suffix hLanes.headLiteral hLanes.cellLiteral
      hLanes.nextLiteral hIndex hLiteralScratch
    have hRun := run_ifEqual_ne (equal := skip) (different := lanes.rawFragment) x
      hHeadCopy hHeadScratch hCellHeadCopy hCellCopy hCellScratch hCopies hHeadCopyScratch
      hCellCopyScratch cfg hHeadZero hCellZero hCompareScratch hEq hRaw rfl
    simpa only [RunsOutput, fragment, time, formula, ite_eq_right hEq, List.reverse_singleton,
      List.foldl_cons, List.foldl_nil, cfg] using hRun

omit [DecidableEq R] in
/-- With the computed bases and offset, the numeric formula is the named tableau copy clause. -/
theorem formula_eq_localCopy {qCount symbolCount width : Nat} (values : R → Nat)
    (t : Nat) (head cell : Fin width) (symbol : Fin symbolCount)
    (hHead : values lanes.head = head.val) (hCell : values lanes.cell = cell.val)
    (hOffset : values lanes.cellOffset = cell.val * symbolCount + symbol.val)
    (hHeadBase : values lanes.headBase = t * Tableau.atomStride qCount width symbolCount + qCount)
    (hCellBase : values lanes.cellBase =
      t * Tableau.atomStride qCount width symbolCount + qCount + width)
    (hNextBase : values lanes.nextCellBase =
      (t + 1) * Tableau.atomStride qCount width symbolCount + qCount + width) :
    lanes.formula values = CNF.mapAtoms (indexedAtomName (qCount := qCount))
      (Tableau.localCopy t head cell symbol) := by
  by_cases hEq : head = cell
  · simp [formula, Tableau.localCopy, CNF.mapAtoms, hHead, hCell, hEq]
  · simp [formula, clause, Tableau.localCopy, CNF.mapAtoms, CNF.guard, CNF.Literal.map,
      CNF.Literal.complement, indexedAtomName, Tableau.Atom.name, Tableau.Atom.time,
      Tableau.Atom.offset, hHead, hCell, hOffset, hHeadBase, hCellBase, hNextBase, hEq,
      Fin.val_ne_iff.mpr hEq, Nat.add_assoc]

end CopyClauseLanes

end PvsNP.CookLevin
