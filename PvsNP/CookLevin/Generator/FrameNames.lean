module

public import PvsNP.CookLevin.Generator.AcceptingBlock
public import PvsNP.CookLevin.VariableNames

/-! # Signed tableau names with register offsets -/

@[expose] public section

namespace PvsNP.RegisterMachine.Fragment

variable {R K : Type}

/-- Compute `base + offset` in the temporary index and emit its framed literal. -/
abbrev emitOffsetLiteral (base offset index scratch : R) (positive : Bool) : Fragment R :=
  ((add base index scratch).seq (add offset index scratch)).seq (emitFramedLiteral index positive)

/-- Count the two additions and the framed unary literal. -/
def offsetLiteralTime (base offset : Nat) : Nat := 7 * (base + offset) + 8

theorem offsetLiteralTime_polynomiallyBounded {base offset : Nat → Nat}
    (hBase : PolynomiallyBounded base) (hOffset : PolynomiallyBounded offset) :
    PolynomiallyBounded (fun n ↦ offsetLiteralTime (base n) (offset n)) :=
  ((PolynomiallyBounded.const 7).mul (hBase.add hOffset)).add (PolynomiallyBounded.const 8)

variable [DecidableEq R]

/-- Emit a literal from two persistent registers, restoring all the register values. -/
theorem run_emitOffsetLiteral (base offset index scratch : R) (positive : Bool)
    (x : BinaryWord) (cfg : Config R K) (hDistinct : [base, offset, index, scratch].Nodup)
    (hIndex : cfg.values index = 0) (hScratch : cfg.values scratch = 0)
    (hCursor : cfg.cursor = none) :
    (emitOffsetLiteral base offset index scratch positive).run x
        (offsetLiteralTime (cfg.values base) (cfg.values offset))
        ((emitOffsetLiteral base offset index scratch positive).enter cfg) = some
      ⟨some none, cfg.values, none, true :: (CNFCode.encodeLiteral
        (if positive then .pos (cfg.values base + cfg.values offset)
          else .neg (cfg.values base + cfg.values offset)) ++ cfg.output)⟩ := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or,
    not_false_eq_true, List.nodup_nil, and_true] at hDistinct
  rcases hDistinct with ⟨⟨_, hBaseIndex, hBaseScratch⟩, ⟨hOffsetIndex, hOffsetScratch⟩,
    hIndexScratch⟩
  let initialAdd := add base index scratch
  let offsetAdd := add offset index scratch
  let first : initialAdd.Cfg :=
    ⟨some none, addValues base index cfg.values, cfg.cursor, cfg.output⟩
  have hFirst : initialAdd.run x (5 * cfg.values base + 2) (initialAdd.enter cfg) = some first :=
    run_add base index scratch x cfg hBaseIndex hBaseScratch hIndexScratch hScratch
  have hFirstScratch : first.values scratch = 0 := by
    simp [first, addValues, Ne.symm hIndexScratch, hScratch]
  have hFirstOffset : first.values offset = cfg.values offset := by
    simp [first, addValues, hOffsetIndex]
  have hFirstIndex : first.values index = cfg.values base := by
    simp [first, addValues, hIndex]
  let second : offsetAdd.Cfg :=
    ⟨some none, addValues offset index first.values, cfg.cursor, cfg.output⟩
  have hSecond : offsetAdd.run x (5 * cfg.values offset + 2) (offsetAdd.enter first) =
      some second := by
    simpa only [hFirstOffset] using
      run_add offset index scratch x first hOffsetIndex hOffsetScratch hIndexScratch hFirstScratch
  let prepared : (initialAdd.seq offsetAdd).Cfg :=
    ⟨some none, second.values, cfg.cursor, cfg.output⟩
  have hPrepared : (initialAdd.seq offsetAdd).run x
        ((5 * cfg.values base + 2) + (5 * cfg.values offset + 2))
        ((initialAdd.seq offsetAdd).enter cfg) = some prepared :=
    run_seq hFirst rfl hSecond rfl
  have hNumber : prepared.values index = cfg.values base + cfg.values offset := by
    change addValues offset index first.values index = _
    simp [addValues, hFirstIndex, hFirstOffset]
  have hRestored : (fun r ↦ if r = index then 0 else prepared.values r) = cfg.values := by
    funext r
    by_cases hr : r = index
    · subst r
      simp [hIndex]
    · simp [prepared, second, first, addValues, hr]
  have hEmit := run_emitFramedLiteral index positive x prepared hCursor
  rw [hNumber, hRestored] at hEmit
  have hTime : offsetLiteralTime (cfg.values base) (cfg.values offset) =
      (5 * cfg.values base + 2) + (5 * cfg.values offset + 2) +
        (2 * (cfg.values base + cfg.values offset) + 4) := by
    unfold offsetLiteralTime
    omega
  rw [hTime]
  exact run_seq hPrepared rfl hEmit rfl

/-- Use a signed register label as a literal offset. -/
def emitSignedOffsetLiteral (base index scratch : R) : CNF.Literal R → Fragment R
  | .pos offset => emitOffsetLiteral base offset index scratch true
  | .neg offset => emitOffsetLiteral base offset index scratch false

/-- Emit a fixed clause in reverse order, starting with the clause terminator. The
register labels in the literals select the offsets to add to the common base. -/
def emitOffsetClause (base index scratch : R) : CNF.Clause R → Fragment R
  | [] => emitBit false
  | literal :: rest =>
    (emitOffsetClause base index scratch rest).seq
      (emitSignedOffsetLiteral base index scratch literal)

/-- Count the clause terminator and every framed register-offset literal. -/
def offsetClauseTime (base : Nat) (values : R → Nat) : CNF.Clause R → Nat
  | [] => 1
  | literal :: rest =>
    offsetClauseTime base values rest + offsetLiteralTime base (values literal.atom)

omit [DecidableEq R] in
theorem offsetClauseTime_le (base maxOffset : Nat) (values : R → Nat)
    (literals : CNF.Clause R) (hOffset : ∀ l ∈ literals, values l.atom ≤ maxOffset) :
    offsetClauseTime base values literals ≤
      literals.length * offsetLiteralTime base maxOffset + 1 := by
  induction literals with
  | nil => simp [offsetClauseTime]
  | cons literal rest ih =>
    have hHead : offsetLiteralTime base (values literal.atom) ≤
        offsetLiteralTime base maxOffset := by
      have h := hOffset literal (List.mem_cons_self ..)
      unfold offsetLiteralTime
      omega
    have hTail := ih (fun l hl ↦ hOffset l (List.mem_cons_of_mem literal hl))
    simp only [offsetClauseTime, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

private theorem run_clauseLiteral (base index scratch : R) (literal : CNF.Literal R)
    (x : BinaryWord) (cfg : Config R K) (hDistinct : [base, literal.atom, index, scratch].Nodup)
    (hIndex : cfg.values index = 0) (hScratch : cfg.values scratch = 0)
    (hCursor : cfg.cursor = none) :
    let fragment := emitSignedOffsetLiteral base index scratch literal
    fragment.run x (offsetLiteralTime (cfg.values base) (cfg.values literal.atom))
        (fragment.enter cfg) = some
      ⟨some none, cfg.values, none, true :: (CNFCode.encodeLiteral
        (literal.map fun offset ↦ cfg.values base + cfg.values offset) ++ cfg.output)⟩ := by
  cases literal with
  | pos offset =>
    exact run_emitOffsetLiteral base offset index scratch true x cfg
      hDistinct hIndex hScratch hCursor
  | neg offset =>
    exact run_emitOffsetLiteral base offset index scratch false x cfg
      hDistinct hIndex hScratch hCursor

/-- Prepend the exact binary clause code using the common base and the selected offsets. -/
theorem run_emitOffsetClause (base index scratch : R) (literals : CNF.Clause R)
    (x : BinaryWord) (cfg : Config R K)
    (hDistinct : ∀ l ∈ literals, [base, l.atom, index, scratch].Nodup)
    (hIndex : cfg.values index = 0) (hScratch : cfg.values scratch = 0)
    (hCursor : cfg.cursor = none) :
    let fragment := emitOffsetClause base index scratch literals
    fragment.run x (offsetClauseTime (cfg.values base) cfg.values literals) (fragment.enter cfg) =
      some ⟨some none, cfg.values, none, CNFCode.encodeClause
        (literals.map (CNF.Literal.map fun offset ↦ cfg.values base + cfg.values offset)) ++
          cfg.output⟩ := by
  induction literals with
  | nil =>
    simpa only [emitOffsetClause, offsetClauseTime, List.map_nil, CNFCode.encodeClause_nil,
      List.singleton_append] using run_emitBit false x cfg hCursor
  | cons literal rest ih =>
    let tailResult : (emitOffsetClause base index scratch rest).Cfg :=
      ⟨some none, cfg.values, none, CNFCode.encodeClause
        (rest.map (CNF.Literal.map fun offset ↦ cfg.values base + cfg.values offset)) ++ cfg.output⟩
    have hTail : (emitOffsetClause base index scratch rest).run x
          (offsetClauseTime (cfg.values base) cfg.values rest)
          ((emitOffsetClause base index scratch rest).enter cfg) = some tailResult :=
      ih (fun l hl ↦ hDistinct l (List.mem_cons_of_mem literal hl))
    have hHead := run_clauseLiteral base index scratch literal x tailResult
      (hDistinct literal (List.mem_cons_self ..)) hIndex hScratch rfl
    dsimp only at hHead
    have h := run_seq hTail rfl hHead rfl
    simpa only [emitOffsetClause, offsetClauseTime, Config.map, Option.map_some, Option.map_none,
      tailResult, List.map_cons, CNFCode.encodeClause_cons, List.cons_append, List.append_assoc]
      using h

/-- Prepend a framed formula clause, including its leading true bit. -/
abbrev emitFramedOffsetClause (base index scratch : R) (literals : CNF.Clause R) : Fragment R :=
  (emitOffsetClause base index scratch literals).seq (emitBit true)

/-- The formula's clause frame costs one additional instruction. -/
theorem run_emitFramedOffsetClause (base index scratch : R) (literals : CNF.Clause R)
    (x : BinaryWord) (cfg : Config R K)
    (hDistinct : ∀ l ∈ literals, [base, l.atom, index, scratch].Nodup)
    (hIndex : cfg.values index = 0) (hScratch : cfg.values scratch = 0)
    (hCursor : cfg.cursor = none) :
    let fragment := emitFramedOffsetClause base index scratch literals
    fragment.run x (offsetClauseTime (cfg.values base) cfg.values literals + 1)
        (fragment.enter cfg) = some
      ⟨some none, cfg.values, none, true :: (CNFCode.encodeClause
        (literals.map (CNF.Literal.map fun offset ↦ cfg.values base + cfg.values offset)) ++
          cfg.output)⟩ := by
  let raw := emitOffsetClause base index scratch literals
  let finished : raw.Cfg := ⟨some none, cfg.values, none, CNFCode.encodeClause
    (literals.map (CNF.Literal.map fun offset ↦ cfg.values base + cfg.values offset)) ++ cfg.output⟩
  have hRaw : raw.run x (offsetClauseTime (cfg.values base) cfg.values literals) (raw.enter cfg) =
      some finished := run_emitOffsetClause base index scratch literals x cfg
        hDistinct hIndex hScratch hCursor
  exact run_seq hRaw rfl (run_emitBit true x finished rfl) rfl

end PvsNP.RegisterMachine.Fragment
