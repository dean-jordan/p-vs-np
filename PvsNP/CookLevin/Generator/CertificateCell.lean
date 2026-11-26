module

public import PvsNP.CookLevin.Generator.AcceptingBlock
public import PvsNP.CookLevin.Generator.FiniteTable
public import PvsNP.TuringMachine.Registers.ValueRuns

/-! # Emitting the initial certificate-cell clauses -/

@[expose] public section

namespace PvsNP.RegisterMachine.Fragment

variable {R K : Type}

/-- The sign bit for encoding a literal with a fixed offset. -/
def fixedOffsetPositive : CNF.Literal Nat → Bool
  | .pos _ => true
  | .neg _ => false

/-- Add the fixed literal offset to the persistent base, then emit the framed literal. -/
abbrev emitFixedOffsetLiteral (base literal scratch : R) (offset : CNF.Literal Nat) :
    Fragment R :=
  ((incrementBy literal offset.atom).seq (add base literal scratch)).seq
    (emitFramedLiteral literal (fixedOffsetPositive offset))

/-- Reverse emission preserves the order of the fixed offsets in the encoded clause. -/
def emitFixedOffsetClause (base literal scratch : R) : CNF.Clause Nat → Fragment R
  | [] => emitBit false
  | offset :: rest =>
    (emitFixedOffsetClause base literal scratch rest).seq
      (emitFixedOffsetLiteral base literal scratch offset)

/-- Emit a clause and the enclosing formula's clause frame. -/
abbrev emitFramedFixedOffsetClause (base literal scratch : R) (offsets : CNF.Clause Nat) :
    Fragment R :=
  (emitFixedOffsetClause base literal scratch offsets).seq (emitBit true)

/-- Instruction count for one framed literal with a fixed offset. -/
def fixedOffsetLiteralTime (base offset : Nat) : Nat := 7 * base + 3 * offset + 6

/-- Instruction count for the clause terminator and framed literals. -/
def fixedOffsetClauseTime (base : Nat) : CNF.Clause Nat → Nat
  | [] => 1
  | offset :: rest => fixedOffsetClauseTime base rest + fixedOffsetLiteralTime base offset.atom

theorem fixedOffsetClauseTime_polynomiallyBounded {base : Nat → Nat}
    (hBase : PolynomiallyBounded base) (offsets : CNF.Clause Nat) :
    PolynomiallyBounded (fun n ↦ fixedOffsetClauseTime (base n) offsets) := by
  induction offsets with
  | nil => exact PolynomiallyBounded.const 1
  | cons offset rest ih =>
    exact ih.add (((PolynomiallyBounded.const 7).mul hBase).add
      (PolynomiallyBounded.const (3 * offset.atom)) |>.add (PolynomiallyBounded.const 6))

variable [DecidableEq R]

/-- Emitting one signed literal leaves the base and both temporary registers intact. -/
theorem run_emitFixedOffsetLiteral (base literal scratch : R) (offset : CNF.Literal Nat)
    (x : BinaryWord) (cfg : Config R K) (hBL : base ≠ literal) (hBS : base ≠ scratch)
    (hLS : literal ≠ scratch) (hLiteral : cfg.values literal = 0)
    (hScratch : cfg.values scratch = 0) (hCursor : cfg.cursor = none) :
    let fragment := emitFixedOffsetLiteral base literal scratch offset
    fragment.run x (fixedOffsetLiteralTime (cfg.values base) offset.atom) (fragment.enter cfg) =
      some ⟨some none, cfg.values, none, true :: (CNFCode.encodeLiteral
        (offset.map (fun code ↦ cfg.values base + code)) ++ cfg.output)⟩ := by
  let name := (incrementBy literal offset.atom).seq (add base literal scratch)
  let loaded := setValue literal offset.atom cfg.values
  let number := cfg.values base + offset.atom
  let computed := setValue literal number cfg.values
  have hInc : (incrementBy literal offset.atom).RunsValues x offset.atom cfg.values loaded := by
    simpa only [loaded, hLiteral, Nat.zero_add] using
      runsValues_incrementBy literal offset.atom x cfg.values
  have hLoadedBase : loaded base = cfg.values base := setValue_other hBL _ _
  have hLoadedScratch : loaded scratch = 0 :=
    (setValue_other hLS.symm _ _).trans hScratch
  have hNamed : setValue literal (loaded literal + loaded base) loaded = computed := by
    funext r
    by_cases h : r = literal
    · subst r
      simp only [hLoadedBase, loaded, computed, number, setValue_same, Nat.add_comm]
    · simp [computed, loaded, setValue, h]
  have hAdd : (add base literal scratch).RunsValues x (5 * cfg.values base + 2)
      loaded computed := by
    rw [← hLoadedBase, ← hNamed]
    exact runsValues_add base literal scratch x loaded hBL hBS hLS hLoadedScratch
  let prepared : name.Cfg := ⟨some none, computed, none, cfg.output⟩
  have hPrepared : name.run x (offset.atom + (5 * cfg.values base + 2)) (name.enter cfg) =
      some prepared := by
    simpa only [enter, hCursor] using (hInc.seq hAdd) cfg.output
  have hPreparedName : prepared.values literal = number := setValue_same _ _ _
  have hRestored : (fun r ↦ if r = literal then 0 else prepared.values r) = cfg.values := by
    funext r
    by_cases h : r = literal
    · subst r
      simp [hLiteral]
    · simp [prepared, computed, setValue, h]
  have hSign : (if fixedOffsetPositive offset then CNF.Literal.pos number
      else .neg number) = offset.map (fun code ↦ cfg.values base + code) := by
    cases offset <;> rfl
  have hFramed := run_emitFramedLiteral literal (fixedOffsetPositive offset) x prepared rfl
  rw [hPreparedName, hRestored, hSign] at hFramed
  have hTime : fixedOffsetLiteralTime (cfg.values base) offset.atom =
      (offset.atom + (5 * cfg.values base + 2)) + (2 * number + 4) := by
    unfold fixedOffsetLiteralTime number
    omega
  rw [hTime]
  exact run_seq hPrepared rfl hFramed rfl

/-- Prepend precisely the encoded fixed-offset clause. -/
theorem run_emitFixedOffsetClause (base literal scratch : R) (offsets : CNF.Clause Nat)
    (x : BinaryWord) (cfg : Config R K) (hBL : base ≠ literal) (hBS : base ≠ scratch)
    (hLS : literal ≠ scratch) (hLiteral : cfg.values literal = 0)
    (hScratch : cfg.values scratch = 0) (hCursor : cfg.cursor = none) :
    let fragment := emitFixedOffsetClause base literal scratch offsets
    fragment.run x (fixedOffsetClauseTime (cfg.values base) offsets) (fragment.enter cfg) =
      some ⟨some none, cfg.values, none, CNFCode.encodeClause
        (offsets.map (CNF.Literal.map fun code ↦ cfg.values base + code)) ++ cfg.output⟩ := by
  induction offsets with
  | nil =>
    simpa only [emitFixedOffsetClause, fixedOffsetClauseTime, List.map_nil,
      CNFCode.encodeClause_nil, List.singleton_append] using run_emitBit false x cfg hCursor
  | cons offset rest ih =>
    let tail := emitFixedOffsetClause base literal scratch rest
    let tailResult : tail.Cfg := ⟨some none, cfg.values, none, CNFCode.encodeClause
      (rest.map (CNF.Literal.map fun code ↦ cfg.values base + code)) ++ cfg.output⟩
    have hTail : tail.run x (fixedOffsetClauseTime (cfg.values base) rest) (tail.enter cfg) =
        some tailResult := ih
    have hHead := run_emitFixedOffsetLiteral base literal scratch offset x tailResult
      hBL hBS hLS hLiteral hScratch rfl
    dsimp only at hHead
    have h := run_seq hTail rfl hHead rfl
    simpa only [tail, emitFixedOffsetClause, fixedOffsetClauseTime, Config.map, Option.map_some,
      Option.map_none, tailResult, List.map_cons, CNFCode.encodeClause_cons, List.cons_append,
      List.append_assoc] using h

/-- Prepend a framed clause for the literals in their specified order, preserving all registers. -/
theorem run_emitFramedFixedOffsetClause (base literal scratch : R) (offsets : CNF.Clause Nat)
    (x : BinaryWord) (cfg : Config R K) (hBL : base ≠ literal) (hBS : base ≠ scratch)
    (hLS : literal ≠ scratch) (hLiteral : cfg.values literal = 0)
    (hScratch : cfg.values scratch = 0) (hCursor : cfg.cursor = none) :
    let fragment := emitFramedFixedOffsetClause base literal scratch offsets
    fragment.run x (fixedOffsetClauseTime (cfg.values base) offsets + 1) (fragment.enter cfg) =
      some ⟨some none, cfg.values, none, true :: (CNFCode.encodeClause
        (offsets.map (CNF.Literal.map fun code ↦ cfg.values base + code)) ++ cfg.output)⟩ := by
  let raw := emitFixedOffsetClause base literal scratch offsets
  let finished : raw.Cfg := ⟨some none, cfg.values, none, CNFCode.encodeClause
    (offsets.map (CNF.Literal.map fun code ↦ cfg.values base + code)) ++ cfg.output⟩
  have hRaw : raw.run x (fixedOffsetClauseTime (cfg.values base) offsets) (raw.enter cfg) =
      some finished := run_emitFixedOffsetClause base literal scratch offsets x cfg
        hBL hBS hLS hLiteral hScratch hCursor
  exact run_seq hRaw rfl (run_emitBit true x finished rfl) rfl

end PvsNP.RegisterMachine.Fragment

namespace PvsNP.CookLevin.FiniteTable

open RegisterMachine.Fragment

variable {qCount symbolCount certificateCount width : Nat}
variable (table : FiniteTable qCount symbolCount certificateCount)

/-- The offsets are the blank symbol followed by certificate letters in enumeration order. -/
def certificateCellOffsets : CNF.Clause Nat :=
  .pos table.blank.val :: (List.finRange certificateCount).map fun c ↦
    .pos (table.certificate c).val

/-- Emit the framed clause of permitted symbols at a certificate slot. -/
abbrev certificateCellFragment {R : Type} (base literal scratch : R) : RegisterMachine.Fragment R :=
  emitFramedFixedOffsetClause base literal scratch table.certificateCellOffsets

/-- The exact cost including the formula's clause frame. -/
def certificateCellTime (base : Nat) : Nat :=
  fixedOffsetClauseTime base table.certificateCellOffsets + 1

theorem certificateCellTime_polynomiallyBounded {base : Nat → Nat}
    (hBase : PolynomiallyBounded base) :
    PolynomiallyBounded (fun n ↦ table.certificateCellTime (base n)) :=
  (fixedOffsetClauseTime_polynomiallyBounded hBase table.certificateCellOffsets).add
    (PolynomiallyBounded.const 1)

/-- Emit exactly the certificate cell's framed clause in front of the existing output. -/
theorem run_certificateCell {R K : Type} [DecidableEq R] (base literal scratch : R)
    (x : BinaryWord) (cfg : RegisterMachine.Config R K)
    (hBL : base ≠ literal) (hBS : base ≠ scratch) (hLS : literal ≠ scratch)
    (hLiteral : cfg.values literal = 0) (hScratch : cfg.values scratch = 0)
    (hCursor : cfg.cursor = none) :
    let fragment := table.certificateCellFragment base literal scratch
    fragment.run x (table.certificateCellTime (cfg.values base)) (fragment.enter cfg) =
      some ⟨some none, cfg.values, none, true :: (CNFCode.encodeClause
        (table.certificateCellOffsets.map (CNF.Literal.map fun code ↦ cfg.values base + code)) ++
        cfg.output)⟩ :=
  run_emitFramedFixedOffsetClause base literal scratch table.certificateCellOffsets x cfg
    hBL hBS hLS hLiteral hScratch hCursor

/-- The initial clause in the certificate region has exactly the fixed-offset names. -/
theorem initialCell_certificateNames (x : BinaryWord) (capacity offset : Nat) (i : Fin width)
    (hStart : offset + x.length + 1 ≤ i.val) (hEnd : i.val < offset + x.length + 1 + capacity) :
    CNF.mapAtoms indexedAtomName (table.initialCell x capacity offset i) =
      [table.certificateCellOffsets.map
        (CNF.Literal.map fun code ↦ qCount + width + i.val * symbolCount + code)] := by
  have hBefore : ¬ i.val < offset := by omega
  simp only [initialCell, ite_eq_right hBefore, ite_eq_right (Nat.not_lt.mpr hStart),
    ite_eq_left hEnd]
  simp [CNF.mapAtoms, certificateCellOffsets, CNF.Literal.map, indexedAtomName, Tableau.Atom.name,
    Tableau.Atom.time, Tableau.Atom.offset, Nat.add_assoc, Function.comp_def]

end PvsNP.CookLevin.FiniteTable
