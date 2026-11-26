module

public import PvsNP.CookLevin.Generator.CopyClause
public import PvsNP.CookLevin.Generator.PreparedField
public import PvsNP.TuringMachine.Registers.Affine

/-! # Register enumeration of one step's copy constraints -/

@[expose] public section

namespace PvsNP.CookLevin

open RegisterMachine RegisterMachine.Fragment

/-- The dimensions, name bases, and work registers for the copy loop. -/
inductive StepCopyLane where
  | width | head | cell | symbol | cellOffset | headBase | cellBase | nextCellBase
  | literalIndex | literalScratch | compareHead | compareCell | compareScratch
  | multiplier | arithmeticScratch
  deriving DecidableEq

/-- Distinct allocation for the copy loop registers. -/
abbrev StepCopyLanes (R : Type) := StepCopyLane ↪ R

variable {R : Type} (lanes : StepCopyLanes R)

local notation "W" => lanes StepCopyLane.width
local notation "I" => lanes StepCopyLane.head
local notation "J" => lanes StepCopyLane.cell
local notation "U" => lanes StepCopyLane.symbol
local notation "O" => lanes StepCopyLane.cellOffset
local notation "HB" => lanes StepCopyLane.headBase
local notation "CB" => lanes StepCopyLane.cellBase
local notation "NB" => lanes StepCopyLane.nextCellBase
local notation "M" => lanes StepCopyLane.multiplier
local notation "A" => lanes StepCopyLane.arithmeticScratch

/-- The registers used by one copy clause. -/
def stepCopyClauseLanes : CopyClauseLanes R :=
  ⟨I, J, O, HB, CB, NB, lanes .literalIndex, lanes .literalScratch,
    lanes .compareHead, lanes .compareCell, lanes .compareScratch⟩

/-- The temporaries in a copy clause are zero at each loop boundary. -/
def StepCopyWorkZero (v : R → Nat) : Prop :=
  v O = 0 ∧ v M = 0 ∧ v A = 0 ∧
    v (lanes .literalIndex) = 0 ∧ v (lanes .literalScratch) = 0 ∧
    v (lanes .compareHead) = 0 ∧ v (lanes .compareCell) = 0 ∧ v (lanes .compareScratch) = 0

/-- All counters and work registers begin empty. -/
structure StepCopiesReady (v : R → Nat) : Prop where
  work : StepCopyWorkZero lanes v
  head : v I = 0
  cell : v J = 0
  symbol : v U = 0

/-- Compute the cell offset from the current cell and symbol, then emit and clear it. -/
def stepCopyAt (symbols : Nat) : Fragment R :=
  (((accumulateAffine J O M A symbols 0).seq (add U O A)).seq
    (stepCopyClauseLanes lanes).fragment).seq (clear O)

/-- Descend through the fixed symbol alphabet for the current cell. -/
def stepCopySymbols (symbols : Nat) : Fragment R :=
  (incrementBy U symbols).seq (countdown U (stepCopyAt lanes symbols))

/-- Descend through the window cells for the current head position. -/
def stepCopyCells (symbols : Nat) : Fragment R :=
  (add W J A).seq (countdown J (stepCopySymbols lanes symbols))

/-- Enumerate head positions, cells and symbols in reverse clause order. -/
def stepCopiesFragment (symbols : Nat) : Fragment R :=
  (add W I A).seq (countdown I (stepCopyCells lanes symbols))

/-- Output of one framed copy clause at numeric coordinates. -/
def copyAtOutput (symbols headBase cellBase nextCellBase i j s : Nat) (suffix : BinaryWord) :
    BinaryWord :=
  if i = j then suffix else
    let offset := j * symbols + s
    true :: (CNFCode.encodeClause
      [.neg (headBase + i), .neg (cellBase + offset), .pos (nextCellBase + offset)] ++ suffix)

/-- The reverse symbol loop at one cell. -/
def copySymbolsOutput (symbols headBase cellBase nextCellBase i j : Nat) (suffix : BinaryWord) :
    BinaryWord :=
  (List.range symbols).reverse.foldl
    (fun out s ↦ copyAtOutput symbols headBase cellBase nextCellBase i j s out) suffix

/-- The reverse cell loop at one head position. -/
def copyCellsOutput (width symbols headBase cellBase nextCellBase i : Nat) (suffix : BinaryWord) :
    BinaryWord :=
  (List.range width).reverse.foldl
    (fun out j ↦ copySymbolsOutput symbols headBase cellBase nextCellBase i j out) suffix

/-- The binary copy section for one time step. -/
def stepCopiesOutput (width symbols headBase cellBase nextCellBase : Nat) (suffix : BinaryWord) :
    BinaryWord :=
  (List.range width).reverse.foldl
    (fun out i ↦ copyCellsOutput width symbols headBase cellBase nextCellBase i out) suffix

/-- Bound one iteration by charging a clause even if the comparison skips it. -/
def copyAtTimeBound (width symbols headBase cellBase nextCellBase : Nat) : Nat :=
  let offset := width * symbols + symbols
  let emit := ifEqualTime width width +
    (1 + offsetLiteralTime nextCellBase offset + offsetLiteralTime cellBase offset +
      offsetLiteralTime headBase width + 1)
  affineTime symbols 0 width + (5 * symbols + 2) + emit + (offset + 1)

/-- Uniform bound for the symbol loop. -/
def copySymbolsTimeBound (width symbols headBase cellBase nextCellBase : Nat) : Nat :=
  symbols + (symbols * (copyAtTimeBound width symbols headBase cellBase nextCellBase + 1) + 1)

/-- Uniform bound for an initialized countdown. -/
def initializedCopyTimeBound (width body : Nat) : Nat :=
  5 * width + 2 + (width * (body + 1) + 1)

/-- Uniform bound for the two window loops and their fixed symbol loops. -/
def stepCopiesTimeBound (width symbols headBase cellBase nextCellBase : Nat) : Nat :=
  initializedCopyTimeBound width
    (initializedCopyTimeBound width
      (copySymbolsTimeBound width symbols headBase cellBase nextCellBase))

theorem stepCopiesTimeBound_polynomiallyBounded
    {width headBase cellBase nextCellBase : Nat → Nat}
    (hWidth : PolynomiallyBounded width) (hHead : PolynomiallyBounded headBase)
    (hCell : PolynomiallyBounded cellBase) (hNext : PolynomiallyBounded nextCellBase)
    (symbols : Nat) :
    PolynomiallyBounded (fun n ↦
      stepCopiesTimeBound (width n) symbols (headBase n) (cellBase n) (nextCellBase n)) := by
  let lit := PolynomiallyBounded.const
  have hOffset := (hWidth.mul (lit symbols)).add (lit symbols)
  have hCopy := (((lit 6).mul (hWidth.add hWidth)).add (lit 6)).add
    (((((lit 1).add (offsetLiteralTime_polynomiallyBounded hNext hOffset)).add
      (offsetLiteralTime_polynomiallyBounded hCell hOffset)).add
      (offsetLiteralTime_polynomiallyBounded hHead hWidth)).add (lit 1))
  have hMultiply := affineTime_polynomiallyBounded symbols 0 hWidth
  have hLeaf := ((hMultiply.add
    (((lit 5).mul (lit symbols)).add (lit 2))).add hCopy).add (hOffset.add (lit 1))
  have hSymbols := (lit symbols).add (((lit symbols).mul (hLeaf.add (lit 1))).add (lit 1))
  have hLoop {body : Nat → Nat} (hBody : PolynomiallyBounded body) :
      PolynomiallyBounded (fun n ↦ initializedCopyTimeBound (width n) (body n)) :=
    (((lit 5).mul hWidth).add (lit 2)).add ((hWidth.mul (hBody.add (lit 1))).add (lit 1))
  exact hLoop (hLoop hSymbols)

private theorem stepCopyClauseLanes_disjoint : (stepCopyClauseLanes lanes).Disjoint := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact List.Nodup.map lanes.injective
      (by decide : [StepCopyLane.headBase, .head, .literalIndex, .literalScratch].Nodup)
  · exact List.Nodup.map lanes.injective
      (by decide : [StepCopyLane.cellBase, .cellOffset, .literalIndex, .literalScratch].Nodup)
  · exact List.Nodup.map lanes.injective
      (by decide : [StepCopyLane.nextCellBase, .cellOffset, .literalIndex, .literalScratch].Nodup)
  · exact List.Nodup.map lanes.injective
      (by decide : [StepCopyLane.head, .compareHead, .compareCell, .compareScratch].Nodup)
  · exact List.Nodup.map lanes.injective
      (by decide : [StepCopyLane.cell, .compareHead, .compareCell, .compareScratch].Nodup)

variable [DecidableEq R]

private theorem setLane_apply (source target : StepCopyLane) (n : Nat) (v : R → Nat) :
    setValue (lanes source) n v (lanes target) =
      if target = source then n else v (lanes target) := by
  simp [setValue, lanes.injective.eq_iff]

/-- The composed leaf computes and clears the offset, preserving all incoming data. -/
theorem run_stepCopyAt (symbols : Nat) (x suffix : BinaryWord) (v : R → Nat)
    (hWork : StepCopyWorkZero lanes v) (hI : v I ≤ v W) (hJ : v J ≤ v W)
    (hU : v U ≤ symbols) :
    ∃ cost ≤ copyAtTimeBound (v W) symbols (v HB) (v CB) (v NB),
      (stepCopyAt lanes symbols).RunsOutput x cost v v suffix
        (copyAtOutput symbols (v HB) (v CB) (v NB) (v I) (v J) (v U) suffix) := by
  obtain ⟨hOffset, hMultiplier, hScratch, hIndex, hLiteral, hHead, hCell, hCompare⟩ := hWork
  let product := v J * symbols
  let offset := product + v U
  let multiplied := setValue O product v
  let prepared := setValue O offset v
  let names := stepCopyClauseLanes lanes
  let output := copyAtOutput symbols (v HB) (v CB) (v NB) (v I) (v J) (v U) suffix
  have hNodup : [J, O, M, A].Nodup := List.Nodup.map lanes.injective
    (by decide : [StepCopyLane.cell, .cellOffset, .multiplier, .arithmeticScratch].Nodup)
  have hMultiply := runsValues_accumulateAffine J O M A symbols 0 x v hNodup hMultiplier hScratch
  rw [hOffset, Nat.zero_add, Nat.add_zero, Nat.mul_comm symbols (v J)] at hMultiply
  have hSymbol : multiplied U = v U := by simp [multiplied, setValue, lanes.injective.eq_iff]
  have hAdd := runsValues_add U O A x multiplied
    (lanes.injective.ne (by decide)) (lanes.injective.ne (by decide))
    (lanes.injective.ne (by decide))
    (by simpa [multiplied, setValue, lanes.injective.eq_iff] using hScratch)
  simp only [hSymbol, multiplied, setValue_same, setValue_replace] at hAdd
  have hEmit := names.runsOutput_fragment x prepared suffix (stepCopyClauseLanes_disjoint lanes)
    (by simpa [names, stepCopyClauseLanes, prepared, setLane_apply] using hIndex)
    (by simpa [names, stepCopyClauseLanes, prepared, setLane_apply] using hLiteral)
    (by simpa [names, stepCopyClauseLanes, prepared, setLane_apply] using hHead)
    (by simpa [names, stepCopyClauseLanes, prepared, setLane_apply] using hCell)
    (by simpa [names, stepCopyClauseLanes, prepared, setLane_apply] using hCompare)
  have hOutput : (names.formula prepared).reverse.foldl
      (fun out clause ↦ true :: (CNFCode.encodeClause clause ++ out)) suffix = output := by
    by_cases hEq : v I = v J <;>
      simp [output, names, CopyClauseLanes.formula, CopyClauseLanes.clause, stepCopyClauseLanes,
        copyAtOutput, prepared, setValue, lanes.injective.eq_iff, offset, product, hEq]
  rw [hOutput] at hEmit
  have hClear := runsValues_clear O x prepared
  have hRestore : setValue O 0 prepared = v := by
    simpa only [prepared, setValue_replace, hOffset] using setValue_current O v
  simp only [prepared, setValue_same, hRestore] at hClear
  refine ⟨affineTime symbols 0 (v J) + (5 * v U + 2) + names.time prepared + (offset + 1),
    ?_, (((hMultiply.withOutput suffix).seq (hAdd.withOutput suffix)).seq hEmit).seq
      (hClear.withOutput output)⟩
  have hMultiplyTime := affineTime_mono symbols 0 hJ
  have hOffsetBound : offset ≤ v W * symbols + symbols :=
    Nat.add_le_add (Nat.mul_le_mul_right symbols hJ) hU
  have hEmitTime := names.time_le_timeBound prepared
  have hEmitBound : names.timeBound prepared = ifEqualTime (v I) (v J) +
      (1 + offsetLiteralTime (v NB) offset + offsetLiteralTime (v CB) offset +
        offsetLiteralTime (v HB) (v I) + 1) := by
    simp [names, CopyClauseLanes.timeBound, CopyClauseLanes.rawTime, stepCopyClauseLanes, prepared,
      setLane_apply]
  rw [hEmitBound] at hEmitTime
  simp only [copyAtTimeBound, ifEqualTime, offsetLiteralTime] at hEmitTime ⊢
  omega

private theorem run_stepCopySymbols (symbols : Nat) (x suffix : BinaryWord) (v : R → Nat)
    (hWork : StepCopyWorkZero lanes v) (hZero : v U = 0)
    (hI : v I ≤ v W) (hJ : v J ≤ v W) :
    ∃ cost ≤ copySymbolsTimeBound (v W) symbols (v HB) (v CB) (v NB),
      (stepCopySymbols lanes symbols).RunsOutput x cost v v suffix
        (copySymbolsOutput symbols (v HB) (v CB) (v NB) (v I) (v J) suffix) := by
  let initial := setValue U symbols v
  let bound := copyAtTimeBound (v W) symbols (v HB) (v CB) (v NB)
  let update (out : BinaryWord) (s : Nat) :=
    copyAtOutput symbols (v HB) (v CB) (v NB) (v I) (v J) s out
  have hInit : (incrementBy U symbols).RunsValues x symbols v initial := by
    simpa only [hZero, Nat.zero_add, initial] using runsValues_incrementBy U symbols x v
  have hInitial : initial U = symbols := setValue_same ..
  have hBody (i : Nat) (hi : i < initial U) (out : BinaryWord) :
      ∃ cost ≤ bound, (stepCopyAt lanes symbols).RunsOutput x cost (setValue U i initial)
        (setValue U i initial) out (update out i) := by
    let current := setValue U i v
    have hCurrent (lane : StepCopyLane) (hNe : lane ≠ .symbol) :
        current (lanes lane) = v (lanes lane) := setValue_other (lanes.injective.ne hNe) i v
    have hSymbol : current U ≤ symbols := by
      rw [show current U = i from setValue_same ..]
      exact Nat.le_of_lt (hInitial ▸ hi)
    obtain ⟨cost, hCost, hRun⟩ := run_stepCopyAt lanes symbols x out current
      (by simpa [StepCopyWorkZero, current, setLane_apply] using hWork)
      (by simpa only [hCurrent .head (by decide), hCurrent .width (by decide)] using hI)
      (by simpa only [hCurrent .cell (by decide), hCurrent .width (by decide)] using hJ) hSymbol
    rw [hCurrent .headBase (by decide), hCurrent .cellBase (by decide),
      hCurrent .nextCellBase (by decide)] at hCost hRun
    rw [hCurrent .width (by decide)] at hCost
    rw [hCurrent .head (by decide), hCurrent .cell (by decide),
      show current U = i from setValue_same ..] at hRun
    exact ⟨cost, hCost, by simpa only [current, update, initial, setValue_replace] using hRun⟩
  obtain ⟨cost, hCost, hRun⟩ := runsOutput_countdown U (stepCopyAt lanes symbols)
    x initial bound update hBody suffix
  have hClear : setValue U 0 initial = v := by
    simpa only [initial, setValue_replace, hZero] using setValue_current U v
  rw [hInitial] at hCost
  rw [hInitial, hClear] at hRun
  exact ⟨_, Nat.add_le_add_left hCost _, (hInit.withOutput suffix).seq hRun⟩

private theorem run_stepCopyCells (symbols : Nat) (x suffix : BinaryWord) (v : R → Nat)
    (hWork : StepCopyWorkZero lanes v) (hCell : v J = 0) (hSymbol : v U = 0) (hHead : v I ≤ v W) :
    ∃ cost ≤ initializedCopyTimeBound (v W)
        (copySymbolsTimeBound (v W) symbols (v HB) (v CB) (v NB)),
      (stepCopyCells lanes symbols).RunsOutput x cost v v suffix
        (copyCellsOutput (v W) symbols (v HB) (v CB) (v NB) (v I) suffix) := by
  let bound := copySymbolsTimeBound (v W) symbols (v HB) (v CB) (v NB)
  let update (out : BinaryWord) (j : Nat) :=
    copySymbolsOutput symbols (v HB) (v CB) (v NB) (v I) j out
  have hBody (j : Nat) (hj : j < v W) (out : BinaryWord) :
      ∃ cost ≤ bound, (stepCopySymbols lanes symbols).RunsOutput x cost (setValue J j v)
        (setValue J j v) out (update out j) := by
    have h := run_stepCopySymbols lanes symbols x out (setValue J j v)
      (by simpa [StepCopyWorkZero, setLane_apply] using hWork)
      (by simpa [setLane_apply] using hSymbol)
      (by simpa [setLane_apply] using hHead)
      (by simpa [setLane_apply] using Nat.le_of_lt hj)
    simpa [setLane_apply, bound, update] using h
  exact runsOutput_initializedCountdown W J A (stepCopySymbols lanes symbols) x v
    bound update (lanes.injective.ne (by decide)) (lanes.injective.ne (by decide))
    (lanes.injective.ne (by decide)) hCell hWork.2.2.1 hBody suffix

/-- All copy clauses at one time are emitted within their uniform budget. -/
theorem run_stepCopiesFragment (symbols : Nat) (x suffix : BinaryWord) (v : R → Nat)
    (hReady : StepCopiesReady lanes v) :
    ∃ cost ≤ stepCopiesTimeBound (v W) symbols (v HB) (v CB) (v NB),
      (stepCopiesFragment lanes symbols).RunsOutput x cost v v suffix
        (stepCopiesOutput (v W) symbols (v HB) (v CB) (v NB) suffix) := by
  let bound := initializedCopyTimeBound (v W)
    (copySymbolsTimeBound (v W) symbols (v HB) (v CB) (v NB))
  let update (out : BinaryWord) (i : Nat) :=
    copyCellsOutput (v W) symbols (v HB) (v CB) (v NB) i out
  have hBody (i : Nat) (hi : i < v W) (out : BinaryWord) :
      ∃ cost ≤ bound, (stepCopyCells lanes symbols).RunsOutput x cost (setValue I i v)
        (setValue I i v) out (update out i) := by
    have h := run_stepCopyCells lanes symbols x out (setValue I i v)
      (by simpa [StepCopyWorkZero, setLane_apply] using hReady.work)
      (by simpa [setLane_apply] using hReady.cell)
      (by simpa [setLane_apply] using hReady.symbol)
      (by simpa [setLane_apply] using Nat.le_of_lt hi)
    simpa [setLane_apply, bound, update] using h
  exact runsOutput_initializedCountdown W I A (stepCopyCells lanes symbols) x v
    bound update (lanes.injective.ne (by decide)) (lanes.injective.ne (by decide))
    (lanes.injective.ne (by decide)) hReady.head hReady.work.2.2.1 hBody suffix

/-- The numeric output matches the copy prefix of the indexed step traversal. -/
theorem stepCopiesOutput_eq (states symbols width time : Nat) (suffix : BinaryWord) :
    let stride := Tableau.atomStride states width symbols
    stepCopiesOutput width symbols (time * stride + states) (time * stride + states + width)
        ((time + 1) * stride + states + width) suffix =
      Traversal.foldFinDesc width (fun acc i ↦ Traversal.foldFinDesc width
        (fun acc j ↦ Traversal.foldFinDesc symbols (fun acc s ↦
          (Tableau.localCopy time i j s).reverse.foldl
            (fun out (clause : CNF.Clause (Tableau.Atom (Fin states) (Fin symbols) width)) ↦
              true :: (CNFCode.encodeClause (clause.map (CNF.Literal.map indexedAtomName)) ++ out))
            acc) acc) acc) suffix := by
  dsimp only
  let stride := Tableau.atomStride states width symbols
  let headBase := time * stride + states
  let cellBase := time * stride + states + width
  let nextCellBase := (time + 1) * stride + states + width
  let emit (out : BinaryWord)
      (clause : CNF.Clause (Tableau.Atom (Fin states) (Fin symbols) width)) :=
    true :: (CNFCode.encodeClause (clause.map (CNF.Literal.map indexedAtomName)) ++ out)
  change stepCopiesOutput width symbols headBase cellBase nextCellBase suffix =
    Traversal.foldFinDesc width (fun acc i ↦ Traversal.foldFinDesc width
      (fun acc j ↦ Traversal.foldFinDesc symbols (fun acc s ↦
        (Tableau.localCopy time i j s).reverse.foldl emit acc) acc) acc) suffix
  have hAt (i j : Fin width) (s : Fin symbols) (acc : BinaryWord) :
      (Tableau.localCopy time i j s).reverse.foldl emit acc =
        copyAtOutput symbols headBase cellBase nextCellBase i.val j.val s.val acc := by
    by_cases hEq : i = j
    · simp [Tableau.localCopy, copyAtOutput, hEq]
    · simp [Tableau.localCopy, copyAtOutput, hEq, Fin.val_ne_iff.mpr hEq, emit,
        CNF.guard, CNF.Literal.complement, CNF.Literal.map, indexedAtomName, Tableau.Atom.name,
        Tableau.Atom.time, Tableau.Atom.offset, headBase, cellBase, nextCellBase, stride,
        Nat.add_assoc]
  have hSymbols (i j : Fin width) (acc : BinaryWord) :
      Traversal.foldFinDesc symbols
        (fun acc s ↦ (Tableau.localCopy time i j s).reverse.foldl emit acc) acc =
        copySymbolsOutput symbols headBase cellBase nextCellBase i.val j.val acc := by
    simp only [hAt, copySymbolsOutput]
    exact foldFinDesc_values symbols
      (fun out s ↦ copyAtOutput symbols headBase cellBase nextCellBase i.val j.val s out) acc
  have hCells (i : Fin width) (acc : BinaryWord) :
      Traversal.foldFinDesc width (fun acc j ↦ Traversal.foldFinDesc symbols
        (fun acc s ↦ (Tableau.localCopy time i j s).reverse.foldl emit acc) acc) acc =
        copyCellsOutput width symbols headBase cellBase nextCellBase i.val acc := by
    simp only [hSymbols, copyCellsOutput]
    exact foldFinDesc_values width
      (fun out j ↦ copySymbolsOutput symbols headBase cellBase nextCellBase i.val j out) acc
  simp only [hCells, stepCopiesOutput]
  exact (foldFinDesc_values width
    (fun out i ↦ copyCellsOutput width symbols headBase cellBase nextCellBase i out) suffix).symm

end PvsNP.CookLevin
