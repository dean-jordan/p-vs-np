module

public import PvsNP.CookLevin.Generator.CertificateCell
public import PvsNP.CookLevin.Generator.GapClause
public import PvsNP.CookLevin.Generator.InputCell
public import PvsNP.TuringMachine.Registers.Subtract

/-! # Emitting the initial tableau cells -/

@[expose] public section

namespace PvsNP.CookLevin

open RegisterMachine RegisterMachine.Fragment

/-- Persistent data and temporary registers for the initial cell pass. -/
inductive InitialCellLane where
  | length | offset | width | lower | upper | position | base | relative
  | work | literal | leftCopy | rightCopy | scratch
  deriving DecidableEq

variable {R : Type} (lanes : InitialCellLane ↪ R)
variable {qCount symbolCount certificateCount : Nat}
variable (table : FiniteTable qCount symbolCount certificateCount)

local notation "Len" => lanes InitialCellLane.length
local notation "Off" => lanes InitialCellLane.offset
local notation "W" => lanes InitialCellLane.width
local notation "Lo" => lanes InitialCellLane.lower
local notation "Hi" => lanes InitialCellLane.upper
local notation "I" => lanes InitialCellLane.position
local notation "B" => lanes InitialCellLane.base
local notation "J" => lanes InitialCellLane.relative
local notation "M" => lanes InitialCellLane.work
local notation "Z" => lanes InitialCellLane.literal
local notation "CP" => lanes InitialCellLane.leftCopy
local notation "CQ" => lanes InitialCellLane.rightCopy
local notation "S" => lanes InitialCellLane.scratch

/-- Temporary values available after preparing the cell base. -/
structure InitialCellScratchZero (v : R → Nat) : Prop where
  relative : v J = 0
  work : v M = 0
  literal : v Z = 0
  leftCopy : v CP = 0
  rightCopy : v CQ = 0
  scratch : v S = 0

/-- Temporary values available before preparing and emitting a cell. -/
structure InitialCellReady (v : R → Nat) : Prop extends InitialCellScratchZero lanes v where
  base : v B = 0

/-- The input interval ends at the separator, followed by the certificate interval. -/
structure InitialCellParameters (x : BinaryWord) (capacity offsetValue widthValue : Nat)
    (v : R → Nat) : Prop where
  length : v Len = x.length
  offset : v Off = offsetValue
  width : v W = widthValue
  lower : v Lo = offsetValue + x.length + 1
  upper : v Hi = offsetValue + x.length + 1 + capacity

/-- Offsets within a cell's symbol interval, in clause order. -/
def initialCellOffsets (x : BinaryWord) (capacity offset i : Nat) : CNF.Clause Nat :=
  if i < offset then [.pos table.blank.val]
  else if i < offset + x.length + 1 then
    [.pos (inputCellSymbol table.bitZero.val table.bitOne.val table.separator.val
      x[i - offset]?)]
  else if i < offset + x.length + 1 + capacity then table.certificateCellOffsets
  else [.pos table.blank.val]

/-- The base of the cell's contiguous interval of atom names in row zero. -/
def initialCellBase (states symbols width i : Nat) : Nat := states + width + i * symbols

/-- Prepend the framed clause for a cell to the accumulated output. -/
def initialCellOutput (x : BinaryWord) (capacity offset width : Nat)
    (suffix : BinaryWord) (i : Nat) : BinaryWord :=
  true :: (CNFCode.encodeClause ((initialCellOffsets table x capacity offset i).map
    (CNF.Literal.map fun code ↦ initialCellBase qCount symbolCount width i + code)) ++ suffix)

/-- Prepare the numeric base from the persistent width and current position. -/
def initialCellPrepare (states symbols : Nat) : Fragment R :=
  (((incrementBy B states).seq (add W B S)).seq (incrementBy M symbols)).seq (multiply M I B S)

/-- Form an input index relative to the offset and emit its bit or separator clause. -/
def initialCellRead : Fragment R :=
  ((add I J S).seq (subtract Off J CP S)).seq
    (inputCell Len J M S B Z table.bitZero.val table.bitOne.val table.separator.val)

/-- Choose between the two regions past the input and separator. -/
def initialCellAfterInput : Fragment R :=
  ifLess I Hi CP CQ S (table.certificateCellFragment B Z S)
    (emitFixedUnitClause B Z S table.blank.val)

/-- Choose a clause after the left blank region. -/
def initialCellAfterOffset : Fragment R :=
  ifLess I Lo CP CQ S (initialCellRead lanes table) (initialCellAfterInput lanes table)

/-- Compare with the offset before considering the other regions. -/
def initialCellChoice : Fragment R :=
  ifLess I Off CP CQ S (emitFixedUnitClause B Z S table.blank.val)
    (initialCellAfterOffset lanes table)

/-- Emit one named initial-cell constraint and release its prepared base. -/
def initialCellFragment : Fragment R :=
  ((initialCellPrepare lanes qCount symbolCount).seq (initialCellChoice lanes table)).seq (clear B)

/-- Descend from width minus one to zero and prepend each cell's clause. -/
def initialCellsFragment : Fragment R :=
  (add W I S).seq (countdown I (initialCellFragment lanes table))

/-- Exact instruction count for base preparation. -/
def initialCellPrepareTime (states symbols width i : Nat) : Nat :=
  states + (5 * width + 2) + symbols + (symbols * (5 * i + 3) + 1)

/-- A width-uniform budget for reading and emitting an input cell. -/
def initialCellReadBound (length offset width maxBase : Nat) : Nat :=
  (5 * width + 2) + (7 * offset + 3) +
    (7 * length + width + 7 * maxBase +
      3 * max table.bitZero.val (max table.bitOne.val table.separator.val) + 13)

/-- A width-uniform budget for all region tests and the selected clause. -/
def initialCellChoiceBound (length offset width lower upper maxBase : Nat) : Nat :=
  ifEqualTime width offset + (ifEqualTime width lower + (ifEqualTime width upper +
    (initialCellReadBound table length offset width maxBase + table.certificateCellTime maxBase +
    fixedUnitClauseTime maxBase table.blank.val)))

/-- A width-uniform budget for preparing and emitting any one cell. -/
def initialCellTimeBound (length offset width lower upper : Nat) : Nat :=
  let maxBase := initialCellBase qCount symbolCount width width
  initialCellPrepareTime qCount symbolCount width width +
    initialCellChoiceBound table length offset width lower upper maxBase + (maxBase + 1)

/-- Budget for the initial width copy and its descending loop. -/
def initialCellsTimeBound (length offset width lower upper : Nat) : Nat :=
  (5 * width + 2) + (width * (initialCellTimeBound table length offset width lower upper + 1) + 1)

private theorem laneNe {a b : InitialCellLane} (h : a ≠ b) : lanes a ≠ lanes b :=
  lanes.injective.ne h

variable [DecidableEq R]

private theorem runsValues_initialCellPrepare (states symbols : Nat) (x : BinaryWord)
    (v : R → Nat) (hReady : InitialCellReady lanes v) :
    (initialCellPrepare lanes states symbols).RunsValues x
      (initialCellPrepareTime states symbols (v W) (v I)) v
      (setValue B (initialCellBase states symbols (v W) (v I)) v) := by
  let shifted := setValue B states v
  let withWidth := setValue B (states + v W) v
  let withFactor := setValue M symbols withWidth
  have hIncrement := runsValues_incrementBy B states x v
  rw [hReady.base, Nat.zero_add] at hIncrement
  have hWidth : shifted W = v W := setValue_other (laneNe lanes (by decide)) ..
  have hScratch : shifted S = 0 :=
    (setValue_other (laneNe lanes (by decide)) ..).trans hReady.scratch
  have hAdd := runsValues_add W B S x shifted
    (laneNe lanes (by decide)) (laneNe lanes (by decide)) (laneNe lanes (by decide)) hScratch
  simp only [hWidth, shifted, setValue_same, setValue_replace] at hAdd
  have hEmptyFactor : withWidth M = 0 := by simp [withWidth, setValue, hReady.work]
  have hLoad := runsValues_incrementBy M symbols x withWidth
  rw [hEmptyFactor, Nat.zero_add] at hLoad
  have hFactor : withFactor M = symbols := setValue_same ..
  have hPosition : withFactor I = v I := by simp [withFactor, withWidth, setValue]
  have hBase : withFactor B = states + v W := by simp [withFactor, withWidth, setValue]
  have hWork : withFactor S = 0 := by simp [withFactor, withWidth, setValue, hReady.scratch]
  have hClear : setValue M 0 withFactor = withWidth := by
    simpa only [withFactor, setValue_replace, hEmptyFactor] using setValue_current M withWidth
  have hMultiply := runsValues_multiply M I B S x withFactor
    (laneNe lanes (by decide)) (laneNe lanes (by decide)) (laneNe lanes (by decide))
    (laneNe lanes (by decide)) (laneNe lanes (by decide)) (laneNe lanes (by decide)) hWork
  simp only [hFactor, hPosition, hBase, hClear, withWidth, setValue_replace,
    Nat.mul_comm symbols (v I)] at hMultiply
  exact ((hIncrement.seq hAdd).seq hLoad).seq hMultiply

private theorem runsOutput_initialCellRead (x suffix : BinaryWord) (v : R → Nat)
    (width maxBase : Nat) (hLength : v Len = x.length)
    (hPosition : v I ≤ width) (hBase : v B ≤ maxBase) (hReady : InitialCellScratchZero lanes v) :
    ∃ cost ≤ initialCellReadBound table x.length (v Off) width maxBase,
      (initialCellRead lanes table).RunsOutput x cost v v suffix
        (true :: (CNFCode.encodeClause [.pos (v B +
          inputCellSymbol table.bitZero.val table.bitOne.val table.separator.val
            x[v I - v Off]?)] ++ suffix)) := by
  let seeded := setValue J (v I) v
  let relative := setValue J (v I - v Off) v
  have hCopy : (add I J S).RunsValues x (5 * v I + 2) v seeded := by
    simpa only [seeded, hReady.relative, Nat.zero_add] using
      runsValues_add I J S x v (laneNe lanes (by decide)) (laneNe lanes (by decide))
        (laneNe lanes (by decide)) hReady.scratch
  have hSubtract := runsValues_subtract Off J CP S x seeded
    (laneNe lanes (by decide)) (laneNe lanes (by decide))
    (laneNe lanes (by decide)) (laneNe lanes (by decide))
    (by simp [seeded, setValue, hReady.leftCopy]) (by simp [seeded, setValue, hReady.scratch])
  have hSeededOffset : seeded Off = v Off := by simp [seeded, setValue]
  simp only [hSeededOffset, seeded, setValue_same, setValue_replace] at hSubtract
  let cfg : Config R Unit := ⟨none, relative, none, suffix⟩
  have hDistinct : [Len, J, M, S, B, Z].Nodup :=
    List.Nodup.map lanes.injective
      (by decide : [InitialCellLane.length, .relative, .work, .scratch, .base, .literal].Nodup)
  have hRun := run_inputCell Len J M S B Z table.bitZero.val table.bitOne.val table.separator.val
    x cfg hDistinct (by simp [cfg, relative, setValue, hLength])
    (by simp [cfg, relative, setValue, hReady.work])
    (by simp [cfg, relative, setValue, hReady.scratch])
    (by simp [cfg, relative, setValue, hReady.literal]) rfl
  have hRelative : relative J = v I - v Off := setValue_same ..
  have hRelativeBase : relative B = v B := by simp [relative, setValue]
  have hRestore : setValue J 0 relative = v := by
    simpa only [relative, setValue_replace, hReady.relative] using setValue_current J v
  dsimp only [cfg] at hRun
  rw [hRelative, hRelativeBase, hRestore] at hRun
  let code := inputCellSymbol table.bitZero.val table.bitOne.val table.separator.val x[v I - v Off]?
  refine ⟨(5 * v I + 2) + (7 * v Off + 3) + inputCellTime x.length (v I - v Off) (v B) code,
    ?_, ?_⟩
  · have hTime := inputCellTime_le x.length (v I - v Off) (v B) code
    have hCode := inputCellSymbol_le table.bitZero.val table.bitOne.val table.separator.val
      x[v I - v Off]?
    change code ≤ _ at hCode
    unfold initialCellReadBound
    omega
  · exact ((hCopy.seq hSubtract).withOutput suffix).seq hRun

private theorem runsOutput_cellTest (right : R) (matching otherwise : Fragment R)
    (x suffix output : BinaryWord) (v : R → Nat) (width bound : Nat)
    (hPosition : v I ≤ width) (hRight : [right, CP, CQ, S].Nodup)
    (hReady : InitialCellScratchZero lanes v)
    (hMatch : v I < v right → ∃ cost ≤ bound, matching.RunsOutput x cost v v suffix output)
    (hOther : ¬ v I < v right → ∃ cost ≤ bound, otherwise.RunsOutput x cost v v suffix output) :
    ∃ cost ≤ ifEqualTime width (v right) + bound,
      (ifLess I right CP CQ S matching otherwise).RunsOutput x cost v v suffix output := by
  obtain ⟨cost, hCost, hRun⟩ := runsOutput_ifLess x v v suffix output bound (by simp) hRight
    hReady.leftCopy hReady.rightCopy hReady.scratch hMatch hOther
  refine ⟨cost, ?_, hRun⟩
  unfold ifEqualTime at *
  omega

private theorem fixedOffsetClauseTime_mono (offsets : CNF.Clause Nat) {base top : Nat}
    (hBase : base ≤ top) :
    fixedOffsetClauseTime base offsets ≤ fixedOffsetClauseTime top offsets := by
  induction offsets with
  | nil => rfl
  | cons offset rest ih =>
    simp only [fixedOffsetClauseTime, fixedOffsetLiteralTime]
    omega

private theorem runsOutput_initialCellChoice (x suffix : BinaryWord) (v : R → Nat)
    (capacity offset width maxBase : Nat) (hParams : InitialCellParameters lanes x capacity
      offset width v) (hPosition : v I ≤ width) (hBase : v B ≤ maxBase)
    (hNamed : v B = initialCellBase qCount symbolCount width (v I))
    (hReady : InitialCellScratchZero lanes v) :
    ∃ cost ≤ initialCellChoiceBound table x.length offset width (offset + x.length + 1)
      (offset + x.length + 1 + capacity) maxBase,
      (initialCellChoice lanes table).RunsOutput x cost v v suffix
        (initialCellOutput table x capacity offset width suffix (v I)) := by
  let blank := emitFixedUnitClause B Z S table.blank.val
  let blankOut := true :: (CNFCode.encodeClause [.pos (v B + table.blank.val)] ++ suffix)
  let certOut := true :: (CNFCode.encodeClause (table.certificateCellOffsets.map
    (CNF.Literal.map fun code ↦ v B + code)) ++ suffix)
  let readOut := true :: (CNFCode.encodeClause [.pos (v B +
    inputCellSymbol table.bitZero.val table.bitOne.val table.separator.val x[v I - v Off]?)] ++
    suffix)
  let readBound := initialCellReadBound table x.length (v Off) width maxBase
  let emitBound := readBound + table.certificateCellTime maxBase +
    fixedUnitClauseTime maxBase table.blank.val
  let cfg : Config R Unit := ⟨none, v, none, suffix⟩
  have hBlank : ∃ cost ≤ emitBound, blank.RunsOutput x cost v v suffix blankOut := by
    refine ⟨fixedUnitClauseTime (v B) table.blank.val, ?_, ?_⟩
    · unfold emitBound fixedUnitClauseTime
      omega
    · exact run_emitFixedUnitClause B Z S table.blank.val x cfg (laneNe lanes (by decide))
        (laneNe lanes (by decide)) (laneNe lanes (by decide))
        hReady.literal hReady.scratch rfl
  have hCert : ∃ cost ≤ emitBound,
      (table.certificateCellFragment B Z S).RunsOutput x cost v v suffix certOut := by
    refine ⟨table.certificateCellTime (v B), ?_, ?_⟩
    · have hMono := fixedOffsetClauseTime_mono table.certificateCellOffsets hBase
      unfold emitBound FiniteTable.certificateCellTime
      omega
    · exact table.run_certificateCell B Z S x cfg (laneNe lanes (by decide))
        (laneNe lanes (by decide)) (laneNe lanes (by decide))
        hReady.literal hReady.scratch rfl
  have hRead : ∃ cost ≤ emitBound,
      (initialCellRead lanes table).RunsOutput x cost v v suffix readOut := by
    obtain ⟨cost, hCost, hRun⟩ := runsOutput_initialCellRead lanes table x suffix v width
      maxBase hParams.length hPosition hBase hReady
    refine ⟨cost, ?_, hRun⟩
    unfold emitBound
    omega
  let pastInput := if v I < v Hi then certOut else blankOut
  have hPastInput : ∃ cost ≤ ifEqualTime width (v Hi) + emitBound,
      (initialCellAfterInput lanes table).RunsOutput x cost v v suffix pastInput := by
    apply runsOutput_cellTest lanes Hi (table.certificateCellFragment B Z S) blank
      x suffix pastInput v width emitBound hPosition (by simp) hReady
    · intro h
      simpa only [pastInput, ite_eq_left h] using hCert
    · intro h
      simpa only [pastInput, ite_eq_right h] using hBlank
  let pastOffset := if v I < v Lo then readOut else pastInput
  have hPastOffset : ∃ cost ≤ ifEqualTime width (v Lo) + (ifEqualTime width (v Hi) + emitBound),
      (initialCellAfterOffset lanes table).RunsOutput x cost v v suffix pastOffset := by
    apply runsOutput_cellTest lanes Lo (initialCellRead lanes table)
      (initialCellAfterInput lanes table) x suffix pastOffset v width _ hPosition (by simp) hReady
    · intro h
      obtain ⟨cost, hCost, hRun⟩ := hRead
      refine ⟨cost, by omega, ?_⟩
      simpa only [pastOffset, ite_eq_left h] using hRun
    · intro h
      simpa only [pastOffset, ite_eq_right h] using hPastInput
  let output := if v I < v Off then blankOut else pastOffset
  have hChoice : ∃ cost ≤ ifEqualTime width (v Off) +
      (ifEqualTime width (v Lo) + (ifEqualTime width (v Hi) + emitBound)),
      (initialCellChoice lanes table).RunsOutput x cost v v suffix output := by
    apply runsOutput_cellTest lanes Off blank (initialCellAfterOffset lanes table)
      x suffix output v width _ hPosition (by simp) hReady
    · intro h
      obtain ⟨cost, hCost, hRun⟩ := hBlank
      refine ⟨cost, by omega, ?_⟩
      simpa only [output, ite_eq_left h] using hRun
    · intro h
      simpa only [output, ite_eq_right h] using hPastOffset
  have hOut : output = initialCellOutput table x capacity offset width suffix (v I) := by
    simp only [output, pastOffset, pastInput, hParams.offset, hParams.lower, hParams.upper,
      initialCellOutput, initialCellOffsets, blankOut, certOut, readOut, hNamed]
    split
    · simp [CNF.Literal.map]
    · split
      · simp [CNF.Literal.map]
      · split
        · rfl
        · simp [CNF.Literal.map]
  simpa only [hOut, emitBound, readBound, hParams.offset, hParams.lower, hParams.upper,
    initialCellChoiceBound] using hChoice

/-- The cell fragment preserves every register and emits its selected numeric clause. -/
theorem runsOutput_initialCell (x suffix : BinaryWord) (capacity offset width : Nat)
    (v : R → Nat) (hParams : InitialCellParameters lanes x capacity offset width v)
    (hPosition : v I ≤ width) (hReady : InitialCellReady lanes v) :
    ∃ cost ≤ initialCellTimeBound table x.length offset width (offset + x.length + 1)
      (offset + x.length + 1 + capacity),
      (initialCellFragment lanes table).RunsOutput x cost v v suffix
        (initialCellOutput table x capacity offset width suffix (v I)) := by
  let base := initialCellBase qCount symbolCount width (v I)
  let maxBase := initialCellBase qCount symbolCount width width
  let named := setValue B base v
  have hPrepare := runsValues_initialCellPrepare lanes qCount symbolCount x v hReady
  rw [hParams.width] at hPrepare
  have hNamed : named B = base := setValue_same ..
  have hNamedPosition : named I = v I := by simp [named, setValue]
  have hNamedParams : InitialCellParameters lanes x capacity offset width named := by
    obtain ⟨hLen, hOff, hW, hLo, hHi⟩ := hParams
    constructor <;> simp [named, setValue, hLen, hOff, hW, hLo, hHi]
  have hNamedReady : InitialCellScratchZero lanes named := by
    obtain ⟨hRel, hWork, hLit, hCP, hCQ, hScratch⟩ := hReady.toInitialCellScratchZero
    constructor <;> simp [named, setValue, hRel, hWork, hLit, hCP, hCQ, hScratch]
  have hBase : base ≤ maxBase :=
    Nat.add_le_add_left (Nat.mul_le_mul_right symbolCount hPosition) _
  obtain ⟨cost, hCost, hChoice⟩ := runsOutput_initialCellChoice lanes table x suffix named
    capacity offset width maxBase hNamedParams (hNamedPosition.trans_le hPosition)
    (hNamed.trans_le hBase) (by rw [hNamedPosition]; exact hNamed) hNamedReady
  have hRestore : setValue B 0 named = v := by
    simpa only [named, setValue_replace, hReady.base] using setValue_current B v
  have hClear := runsValues_clear B x named
  rw [hNamed, hRestore] at hClear
  rw [hNamedPosition] at hChoice
  refine ⟨initialCellPrepareTime qCount symbolCount width (v I) + cost + (base + 1), ?_, ?_⟩
  · have hMul := Nat.mul_le_mul_left symbolCount (show 5 * v I + 3 ≤ 5 * width + 3 by omega)
    unfold initialCellTimeBound initialCellPrepareTime
    change _ ≤ _ + initialCellChoiceBound table x.length offset width (offset + x.length + 1)
      (offset + x.length + 1 + capacity) maxBase + (maxBase + 1)
    omega
  · exact ((hPrepare.withOutput suffix).seq hChoice).seq (hClear.withOutput _)

omit [DecidableEq R] in
/-- The selected offsets give exactly the named initial-cell clause. -/
theorem initialCellNames {width : Nat} (x : BinaryWord) (capacity offset : Nat) (i : Fin width) :
    [((initialCellOffsets table x capacity offset i.val).map
      (CNF.Literal.map fun code ↦ initialCellBase qCount symbolCount width i.val + code))] =
      CNF.mapAtoms indexedAtomName (table.initialCell x capacity offset i) := by
  by_cases hBefore : i.val < offset
  · simp [initialCellOffsets, FiniteTable.initialCell, hBefore, CNF.mapAtoms, CNF.Literal.map,
      initialCellBase, indexedAtomName, Tableau.Atom.name, Tableau.Atom.time, Tableau.Atom.offset,
      Nat.add_assoc]
  · by_cases hInput : i.val < offset + x.length + 1
    · rw [table.initialCell_inputNames x capacity offset i (by omega) (by omega)]
      simp [initialCellOffsets, hBefore, hInput, initialCellBase, CNF.Literal.map]
    · by_cases hCert : i.val < offset + x.length + 1 + capacity
      · rw [table.initialCell_certificateNames x capacity offset i (by omega) hCert]
        simp [initialCellOffsets, hBefore, hInput, hCert, initialCellBase]
      · simp only [initialCellOffsets, FiniteTable.initialCell, ite_eq_right hBefore,
          ite_eq_right hInput, ite_eq_right hCert]
        simp [CNF.mapAtoms, CNF.Literal.map, initialCellBase, indexedAtomName,
          Tableau.Atom.name, Tableau.Atom.time, Tableau.Atom.offset, Nat.add_assoc]

omit [DecidableEq R] in
/-- A single output update agrees with encoding the named cell formula. -/
theorem initialCellOutput_eq {width : Nat} (x : BinaryWord) (capacity offset : Nat)
    (i : Fin width) (suffix : BinaryWord) :
    initialCellOutput table x capacity offset width suffix i.val =
      (CNF.mapAtoms indexedAtomName (table.initialCell x capacity offset i)).reverse.foldl
        (fun out clause ↦ true :: (CNFCode.encodeClause clause ++ out)) suffix := by
  rw [← initialCellNames table x capacity offset i]
  rfl

/-- The output of the entire descending cell pass. -/
def initialCellsOutput (x : BinaryWord) (capacity offset width : Nat) (suffix : BinaryWord) :
    BinaryWord :=
  (List.range width).reverse.foldl (initialCellOutput table x capacity offset width) suffix

omit [DecidableEq R] in
/-- The descending pass prepends the exact named initial-cell formula in normal clause order. -/
theorem initialCellsOutput_eq (x : BinaryWord) (capacity offset width : Nat)
    (suffix : BinaryWord) :
    initialCellsOutput table x capacity offset width suffix =
      (CNF.mapAtoms indexedAtomName ((List.finRange width).flatMap
        (table.initialCell x capacity offset))).reverse.foldl
          (fun out clause ↦ true :: (CNFCode.encodeClause clause ++ out)) suffix := by
  rw [initialCellsOutput, ← foldFinDesc_values, Traversal.foldFinDesc_eq]
  simp only [initialCellOutput_eq, CNF.mapAtoms, List.map_flatMap, List.reverse_flatMap,
    List.foldl_flatMap, Function.comp_def]

/-- The executable pass emits every initial cell and restores the entire valuation. -/
theorem runsOutput_initialCells (x suffix : BinaryWord) (capacity offset width : Nat)
    (v : R → Nat) (hParams : InitialCellParameters lanes x capacity offset width v)
    (hPosition : v I = 0) (hReady : InitialCellReady lanes v) :
    ∃ cost ≤ initialCellsTimeBound table x.length offset width (offset + x.length + 1)
      (offset + x.length + 1 + capacity),
      (initialCellsFragment lanes table).RunsOutput x cost v v suffix
        ((CNF.mapAtoms indexedAtomName ((List.finRange width).flatMap
          (table.initialCell x capacity offset))).reverse.foldl
            (fun out clause ↦ true :: (CNFCode.encodeClause clause ++ out)) suffix) := by
  let bound := initialCellTimeBound table x.length offset width (offset + x.length + 1)
    (offset + x.length + 1 + capacity)
  let update := initialCellOutput table x capacity offset width
  have hBody (i : Nat) (hi : i < v W) (acc : BinaryWord) :
      ∃ cost ≤ bound, (initialCellFragment lanes table).RunsOutput x cost (setValue I i v)
        (setValue I i v) acc (update acc i) := by
    let current := setValue I i v
    have hCurrentParams : InitialCellParameters lanes x capacity offset width current := by
      obtain ⟨hLen, hOff, hWidth, hLo, hHi⟩ := hParams
      constructor <;> simp [current, setValue, hLen, hOff, hWidth, hLo, hHi]
    have hCurrentReady : InitialCellReady lanes current := by
      obtain ⟨⟨hRel, hWork, hLit, hCP, hCQ, hS⟩, hB⟩ := hReady
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
        simp [current, setValue, hRel, hWork, hLit, hCP, hCQ, hS, hB]
    have hCurrentPosition : current I = i := setValue_same ..
    have hCell := runsOutput_initialCell lanes table x acc capacity offset width current
      hCurrentParams (by rw [hCurrentPosition]; rw [hParams.width] at hi; omega) hCurrentReady
    simpa only [hCurrentPosition, current, bound, update] using hCell
  obtain ⟨cost, hCost, hRun⟩ := runsOutput_initializedCountdown W I S
    (initialCellFragment lanes table) x v bound update
    (laneNe lanes (by decide)) (laneNe lanes (by decide)) (laneNe lanes (by decide))
    hPosition hReady.scratch hBody suffix
  rw [hParams.width] at hCost hRun
  rw [← initialCellsOutput_eq table x capacity offset width suffix]
  exact ⟨cost, hCost, hRun⟩

omit [DecidableEq R] in
/-- Fixed table data and polynomially bounded input parameters give a polynomial pass. -/
theorem initialCellsTimeBound_polynomiallyBounded {length offset width lower upper : Nat → Nat}
    (hLength : PolynomiallyBounded length) (hOffset : PolynomiallyBounded offset)
    (hWidth : PolynomiallyBounded width) (hLower : PolynomiallyBounded lower)
    (hUpper : PolynomiallyBounded upper) :
    PolynomiallyBounded (fun n ↦ initialCellsTimeBound table
      (length n) (offset n) (width n) (lower n) (upper n)) := by
  let k := PolynomiallyBounded.const
  have hBase : PolynomiallyBounded
      (fun n ↦ initialCellBase qCount symbolCount (width n) (width n)) :=
    ((k qCount).add hWidth).add (hWidth.mul (k symbolCount))
  have hCopy := ((k 5).mul hWidth).add (k 2)
  have hPrepare := (((k qCount).add hCopy).add (k symbolCount)).add
    (((k symbolCount).mul (((k 5).mul hWidth).add (k 3))).add (k 1))
  have hRead := (hCopy.add (((k 7).mul hOffset).add (k 3))).add
    (((((k 7).mul hLength).add hWidth).add ((k 7).mul hBase)).add
      (k (3 * max table.bitZero.val (max table.bitOne.val table.separator.val))) |>.add (k 13))
  have hEmit := (hRead.add (table.certificateCellTime_polynomiallyBounded hBase)).add
    ((((k 7).mul hBase).add (k (3 * table.blank.val))).add (k 8))
  have comparison {f : Nat → Nat} (hf : PolynomiallyBounded f) :
      PolynomiallyBounded (fun n ↦ ifEqualTime (width n) (f n)) :=
    (((k 6).mul (hWidth.add hf)).add (k 6))
  have hChoice := (comparison hOffset).add
    ((comparison hLower).add ((comparison hUpper).add hEmit))
  have hCell := (hPrepare.add hChoice).add (hBase.add (k 1))
  exact hCopy.add ((hWidth.mul (hCell.add (k 1))).add (k 1))

end PvsNP.CookLevin
