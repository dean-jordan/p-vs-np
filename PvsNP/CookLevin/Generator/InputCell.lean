module

public import PvsNP.CookLevin.Generator.AcceptingBlock
public import PvsNP.CookLevin.Generator.FiniteTable
public import PvsNP.TuringMachine.Registers.ForwardLookup

/-! # Emitting a fixed cell of the initial tableau row -/

@[expose] public section

namespace PvsNP.RegisterMachine.Fragment

variable {R K : Type}

/-- Select the symbol code for the instance bit or its following separator. -/
def inputCellSymbol (zeroCode oneCode separatorCode : Nat) : Option Bool → Nat
  | none => separatorCode
  | some false => zeroCode
  | some true => oneCode

/-- Emit a framed positive unit clause for the sum of a persistent base and a fixed code. -/
abbrev emitFixedUnitClause (base literal scratch : R) (code : Nat) : Fragment R :=
  (emitBit false).seq (((incrementBy literal code).seq (add base literal scratch)).seq
    ((emitFramedLiteral literal true).seq (emitBit true)))

/-- The instruction count including both clause separators. -/
def fixedUnitClauseTime (base code : Nat) : Nat := 7 * base + 3 * code + 8

/-- Read an instance position and emit its initial-cell clause. At the input length the
selected symbol is the separator. A larger index also returns the separator. -/
abbrev inputCell (length index work scratch base literal : R)
    (zeroCode oneCode separatorCode : Nat) : Fragment R :=
  forwardLookup length index work scratch fun b ↦
    emitFixedUnitClause base literal scratch (inputCellSymbol zeroCode oneCode separatorCode b)

/-- The total time at a known lookup result. -/
def inputCellTime (length index base code : Nat) : Nat :=
  forwardLookupCost length index + fixedUnitClauseTime base code

theorem inputCellTime_le (length index base code : Nat) :
    inputCellTime length index base code ≤ 7 * length + index + 7 * base + 3 * code + 13 := by
  have hLookup := forwardLookupCost_le length index
  unfold inputCellTime fixedUnitClauseTime
  omega

theorem inputCellTime_polynomiallyBounded {length index base code : Nat → Nat}
    (hLength : PolynomiallyBounded length) (hIndex : PolynomiallyBounded index)
    (hBase : PolynomiallyBounded base) (hCode : PolynomiallyBounded code) :
    PolynomiallyBounded (fun n ↦ inputCellTime (length n) (index n) (base n) (code n)) :=
  (forwardLookupCost_polynomiallyBounded hLength hIndex).add
    ((((PolynomiallyBounded.const 7).mul hBase).add
      ((PolynomiallyBounded.const 3).mul hCode)).add (PolynomiallyBounded.const 8))

theorem inputCellSymbol_le (zeroCode oneCode separatorCode : Nat) (b : Option Bool) :
    inputCellSymbol zeroCode oneCode separatorCode b ≤
      max zeroCode (max oneCode separatorCode) := by
  cases b with
  | none => exact (Nat.le_max_right oneCode separatorCode).trans (Nat.le_max_right _ _)
  | some b =>
    cases b
    · exact Nat.le_max_left _ _
    · exact (Nat.le_max_left oneCode separatorCode).trans (Nat.le_max_right _ _)

variable [DecidableEq R]

/-- Emit precisely the framed unit clause while restoring the literal and scratch lanes. -/
theorem run_emitFixedUnitClause (base literal scratch : R) (code : Nat)
    (x : BinaryWord) (cfg : Config R K) (hBL : base ≠ literal) (hBS : base ≠ scratch)
    (hLS : literal ≠ scratch) (hLiteral : cfg.values literal = 0)
    (hScratch : cfg.values scratch = 0) (hCursor : cfg.cursor = none) :
    let fragment := emitFixedUnitClause base literal scratch code
    fragment.run x (fixedUnitClauseTime (cfg.values base) code) (fragment.enter cfg) =
      some ⟨some none, cfg.values, none,
        true :: (CNFCode.encodeClause [.pos (cfg.values base + code)] ++ cfg.output)⟩ := by
  let initial := emitBit (R := R) false
  let name := (incrementBy literal code).seq (add base literal scratch)
  let clause := (emitFramedLiteral literal true).seq (emitBit true)
  let marked : initial.Cfg := ⟨some none, cfg.values, none, false :: cfg.output⟩
  have hMarked : initial.run x 1 (initial.enter cfg) = some marked :=
    run_emitBit false x cfg hCursor
  let offset := setValue literal code cfg.values
  have hInc : (incrementBy literal code).RunsValues x code cfg.values offset := by
    simpa only [offset, hLiteral, Nat.zero_add] using
      runsValues_incrementBy literal code x cfg.values
  have hOffsetBase : offset base = cfg.values base := setValue_other hBL _ _
  have hOffsetScratch : offset scratch = 0 := (setValue_other hLS.symm _ _).trans hScratch
  let number := cfg.values base + code
  let computed := setValue literal number cfg.values
  have hNamed : setValue literal (offset literal + offset base) offset = computed := by
    funext r
    by_cases h : r = literal
    · subst r
      simp only [offset, setValue_same, computed, number, Nat.add_comm]
      rw [setValue_other hBL]
    · simp [computed, offset, setValue, h]
  have hAdd : (add base literal scratch).RunsValues x (5 * cfg.values base + 2)
      offset computed := by
    rw [← hOffsetBase, ← hNamed]
    exact runsValues_add base literal scratch x offset hBL hBS hLS hOffsetScratch
  let prepared : name.Cfg := ⟨some none, computed, none, marked.output⟩
  have hPrepared : name.run x (code + (5 * cfg.values base + 2)) (name.enter marked) =
      some prepared := (hInc.seq hAdd) marked.output
  have hPreparedName : prepared.values literal = number := setValue_same _ _ _
  have hRestored : (fun r ↦ if r = literal then 0 else prepared.values r) = cfg.values := by
    funext r
    by_cases h : r = literal
    · subst r
      simp [hLiteral]
    · simp [prepared, computed, setValue, h]
  let framed : (emitFramedLiteral literal true).Cfg :=
    ⟨some none, cfg.values, none, true :: (CNFCode.encodeLiteral (.pos number) ++ marked.output)⟩
  have hFramed : (emitFramedLiteral literal true).run x (2 * number + 4)
      ((emitFramedLiteral literal true).enter prepared) = some framed := by
    simpa only [hPreparedName, hRestored, ite_true] using
      run_emitFramedLiteral literal true x prepared rfl
  have hClause := run_seq hFramed rfl (run_emitBit true x framed rfl) rfl
  have hRun := run_seq hMarked rfl (run_seq hPrepared rfl hClause rfl) rfl
  have hTime : fixedUnitClauseTime (cfg.values base) code =
      1 + ((code + (5 * cfg.values base + 2)) + ((2 * number + 4) + 1)) := by
    unfold fixedUnitClauseTime number
    omega
  rw [hTime]
  simpa only [emitFixedUnitClause, Config.map, Option.map_some, Option.map_none,
    framed, marked, number, CNFCode.encodeClause_cons, CNFCode.encodeClause_nil,
    List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using hRun

/-- Emit the unit clause selected by the ordinary input index. Only that index is consumed. -/
theorem run_inputCell (length index work scratch base literal : R)
    (zeroCode oneCode separatorCode : Nat) (x : BinaryWord) (cfg : Config R K)
    (hDistinct : [length, index, work, scratch, base, literal].Nodup)
    (hLength : cfg.values length = x.length) (hWork : cfg.values work = 0)
    (hScratch : cfg.values scratch = 0) (hLiteral : cfg.values literal = 0)
    (hCursor : cfg.cursor = none) :
    let code := inputCellSymbol zeroCode oneCode separatorCode x[cfg.values index]?
    let fragment := inputCell length index work scratch base literal zeroCode oneCode separatorCode
    fragment.run x (inputCellTime x.length (cfg.values index) (cfg.values base) code)
        (fragment.enter cfg) = some
      ⟨some none, setValue index 0 cfg.values, none,
        true :: (CNFCode.encodeClause [.pos (cfg.values base + code)] ++ cfg.output)⟩ := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or,
    not_false_eq_true, List.nodup_nil, and_true] at hDistinct
  rcases hDistinct with ⟨⟨_, hLW, hLS, _, _⟩, ⟨hIW, hIS, hIB, hIL⟩, ⟨hWS, _, _⟩,
    ⟨hSB, hSL⟩, hBL⟩
  let branches (b : Option Bool) := emitFixedUnitClause base literal scratch
    (inputCellSymbol zeroCode oneCode separatorCode b)
  let before := setValue index 0 cfg.values
  let branchCfg : Config R Unit := ⟨none, before, none, cfg.output⟩
  have hBase : branchCfg.values base = cfg.values base := setValue_other (Ne.symm hIB) _ _
  have hLit : branchCfg.values literal = 0 := (setValue_other (Ne.symm hIL) _ _).trans hLiteral
  have hScr : branchCfg.values scratch = 0 := (setValue_other (Ne.symm hIS) _ _).trans hScratch
  have hBody := run_emitFixedUnitClause base literal scratch
    (inputCellSymbol zeroCode oneCode separatorCode x[cfg.values index]?) x branchCfg
    hBL (Ne.symm hSB) (Ne.symm hSL) hLit hScr rfl
  dsimp only at hBody
  rw [hBase] at hBody
  have h := run_forwardLookup length index work scratch branches x cfg.values cfg.output
    hLW hLS hIW hWS hLength hWork hScratch hBody
  simpa only [inputCell, inputCellTime, enter, hCursor] using h

end PvsNP.RegisterMachine.Fragment

namespace PvsNP.CookLevin.FiniteTable

open RegisterMachine.Fragment (inputCellSymbol)

/-- In the input and separator region, the initial clause uses exactly the name emitted by
the input-cell fragment. -/
theorem initialCell_inputNames {qCount symbolCount certificateCount width : Nat}
    (table : FiniteTable qCount symbolCount certificateCount) (x : BinaryWord)
    (capacity offset : Nat) (i : Fin width) (hStart : offset ≤ i.val)
    (hEnd : i.val ≤ offset + x.length) :
    CNF.mapAtoms indexedAtomName (table.initialCell x capacity offset i) =
      [[.pos (qCount + width + i.val * symbolCount +
        inputCellSymbol table.bitZero.val table.bitOne.val table.separator.val
          x[i.val - offset]?)]] := by
  have hPrefix : ((table.fixedPrefix x)[i.val - offset]?).getD table.blank =
      (x[i.val - offset]?).elim table.separator table.bit := by
    unfold fixedPrefix
    by_cases hIn : i.val - offset < x.length
    · have hMap : i.val - offset < (x.map table.bit).length := by simpa using hIn
      rw [List.getElem?_append_left hMap, List.getElem?_map, List.getElem?_eq_getElem hIn]
      rfl
    · have hAtEnd : i.val - offset = x.length := by omega
      have hMap : (x.map table.bit).length ≤ i.val - offset := by simp [hAtEnd]
      rw [List.getElem?_append_right hMap, hAtEnd, List.length_map, Nat.sub_self,
        List.getElem?_eq_none (Nat.le_refl _)]
      rfl
  simp only [initialCell, ite_eq_right (Nat.not_lt.mpr hStart),
    ite_eq_left (show i.val < offset + x.length + 1 by omega), hPrefix]
  cases h : x[i.val - offset]? with
  | none =>
    simp [CNF.mapAtoms, CNF.Literal.map, indexedAtomName, Tableau.Atom.name, Tableau.Atom.time,
      Tableau.Atom.offset, inputCellSymbol, Nat.add_assoc]
  | some b =>
    cases b <;>
      simp [CNF.mapAtoms, CNF.Literal.map, indexedAtomName, Tableau.Atom.name, Tableau.Atom.time,
        Tableau.Atom.offset, bit, inputCellSymbol, Nat.add_assoc]

end PvsNP.CookLevin.FiniteTable
