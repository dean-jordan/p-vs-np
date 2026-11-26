module

public import PvsNP.CookLevin.Generator.EmitLiteral
public import PvsNP.CookLevin.Generator.NameRegister
public import PvsNP.TuringMachine.Registers.BasicFragments

/-! # The accepting unit clause of the tableau serialization -/

@[expose] public section

namespace PvsNP.RegisterMachine.Fragment

variable {R K : Type}

/-- Prepend one output bit. -/
abbrev emitBit (bit : Bool) : Fragment R where
  Label := Unit
  entry := some ()
  code _ := .emit bit none

/-- Emit a unary index, sign and literal frame, clearing the index register. -/
abbrev emitFramedLiteral (index : R) (positive : Bool) : Fragment R where
  Label := Fin 5
  entry := some 0
  code label := match label.val with
    | 0 => .emit false (some 1)
    | 1 => .dec index (some 3) (some 2)
    | 2 => .emit true (some 1)
    | 3 => .emit positive (some 4)
    | _ => .emit true none

private def framedLiteralRules (index : R) (positive : Bool) :
    CookLevin.EmitLiteralRules (emitFramedLiteral index positive).close index positive where
  entry := some 0
  test := some 1
  one := some 2
  sign := some 3
  frame := some 4
  next := none
  writeTerminator := rfl
  readIndex := rfl
  writeOne := rfl
  writeSign := rfl
  writePrefix := rfl

variable [DecidableEq R]

/-- Prepending a bit takes exactly one instruction. -/
theorem run_emitBit (bit : Bool) (x : BinaryWord) (cfg : Config R K)
    (hCursor : cfg.cursor = none) :
    (emitBit bit).run x 1 ((emitBit bit).enter cfg) =
      some ⟨some none, cfg.values, none, bit :: cfg.output⟩ := by
  change RegisterMachine.run (emitBit bit).close x 1 ((emitBit bit).enter cfg) = _
  rw [RegisterMachine.run_succ,
    step_emit (cfg := (emitBit bit).enter cfg) rfl (by rfl) hCursor,
    Option.bind_some, run_zero]
  simp only [enter, hCursor]

/-- The framed-literal fragment prepends the encoded literal and returns the index to zero. -/
theorem run_emitFramedLiteral (index : R) (positive : Bool) (x : BinaryWord)
    (cfg : Config R K) (hCursor : cfg.cursor = none) :
    (emitFramedLiteral index positive).run x (2 * cfg.values index + 4)
        ((emitFramedLiteral index positive).enter cfg) = some
      ⟨some none, fun r ↦ if r = index then 0 else cfg.values r, none,
        true :: (CNFCode.encodeLiteral
          (if positive then .pos (cfg.values index) else .neg (cfg.values index)) ++
            cfg.output)⟩ := by
  simpa only [run, enter, hCursor, framedLiteralRules] using
    CookLevin.run_emitLiteral (framedLiteralRules index positive) x
      (cfg := (emitFramedLiteral index positive).enter cfg) rfl hCursor

/-- Start the formula with its final accepting unit clause in reverse emission order. -/
abbrev acceptingBlock (time stride index multiplier scratch : R) (accept : Nat) : Fragment R :=
  let terminators : Fragment R := (emitBit false).seq (emitBit false)
  let name := (incrementBy index accept).seq (accumulateName time stride index multiplier scratch)
  let clause := (emitFramedLiteral index true).seq (emitBit true)
  (terminators.seq name).seq clause

/-- The exact cost of the accepting clause, including both list terminators. -/
def acceptingBlockTime (accept time stride : Nat) : Nat :=
  2 + (accept + accumulateNameTime time stride) + (2 * (time * stride + accept) + 4 + 1)

theorem acceptingBlockTime_polynomiallyBounded (accept : Nat) {time stride : Nat → Nat}
    (hTime : PolynomiallyBounded time) (hStride : PolynomiallyBounded stride) :
    PolynomiallyBounded (fun n ↦ acceptingBlockTime accept (time n) (stride n)) := by
  have hName := (hTime.mul hStride).add (PolynomiallyBounded.const accept)
  exact ((PolynomiallyBounded.const 2).add ((PolynomiallyBounded.const accept).add
    (accumulateNameTime_polynomiallyBounded hTime hStride))).add
      ((((PolynomiallyBounded.const 2).mul hName).add (PolynomiallyBounded.const 4)).add
        (PolynomiallyBounded.const 1))

/-- Emit the final accepting unit clause and formula terminator. All registers are restored,
and the fragment exits with unmarked input and the original output suffix. -/
theorem run_acceptingBlock (x : BinaryWord) (time stride index multiplier scratch : R)
    (accept : Nat) (cfg : Config R K)
    (hDistinct : [time, stride, index, multiplier, scratch].Nodup)
    (hIndex : cfg.values index = 0) (hMultiplier : cfg.values multiplier = 0)
    (hScratch : cfg.values scratch = 0) (hCursor : cfg.cursor = none) :
    let block := acceptingBlock time stride index multiplier scratch accept
    block.run x (acceptingBlockTime accept (cfg.values time) (cfg.values stride))
        (block.enter cfg) = some
      ⟨some none, cfg.values, none,
        true :: (CNFCode.encodeClause [.pos (cfg.values time * cfg.values stride + accept)] ++
          false :: cfg.output)⟩ := by
  have hLanes := hDistinct
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or,
    not_false_eq_true, List.nodup_nil, and_true] at hLanes
  rcases hLanes with ⟨⟨_, hTimeIndex, _, _⟩, ⟨hStrideIndex, _, _⟩,
    ⟨hIndexMultiplier, hIndexScratch⟩, _⟩
  let terminators : Fragment R := (emitBit false).seq (emitBit false)
  let name := (incrementBy index accept).seq (accumulateName time stride index multiplier scratch)
  let clause := (emitFramedLiteral index true).seq (emitBit true)
  let number := cfg.values time * cfg.values stride + accept
  let marked : terminators.Cfg := ⟨some none, cfg.values, none, false :: false :: cfg.output⟩
  have hMarked : terminators.run x 2 (terminators.enter cfg) = some marked := by
    let first : (emitBit (R := R) false).Cfg := ⟨some none, cfg.values, none, false :: cfg.output⟩
    exact run_seq (run_emitBit false x cfg hCursor) rfl (run_emitBit false x first rfl) rfl
  let offset : (incrementBy index accept).Cfg :=
    ⟨some none, addRegisterValue index accept cfg.values, none, marked.output⟩
  have hInc : (incrementBy index accept).run x accept ((incrementBy index accept).enter marked) =
      some offset := run_incrementBy index accept x marked
  have hOffsetTime : offset.values time = cfg.values time := by
    simp [offset, addRegisterValue, hTimeIndex]
  have hOffsetStride : offset.values stride = cfg.values stride := by
    simp [offset, addRegisterValue, hStrideIndex]
  have hOffsetMultiplier : offset.values multiplier = 0 := by
    simp [offset, addRegisterValue, Ne.symm hIndexMultiplier, hMultiplier]
  have hOffsetScratch : offset.values scratch = 0 := by
    simp [offset, addRegisterValue, Ne.symm hIndexScratch, hScratch]
  let namedValues : R → Nat := fun r ↦ if r = index then number else cfg.values r
  have hComputedValues : (fun r ↦ if r = index then
        offset.values index + offset.values time * offset.values stride else offset.values r) =
      namedValues := by
    funext r
    by_cases hr : r = index
    · subst r
      have hOffsetIndex : offset.values index = accept := by
        simp [offset, addRegisterValue, hIndex]
      simp [namedValues, hOffsetIndex, hOffsetTime, hOffsetStride, number, Nat.add_comm]
    · simp [namedValues, offset, addRegisterValue, hr]
  let accumulated : (accumulateName time stride index multiplier scratch).Cfg :=
    ⟨some none, namedValues, none, marked.output⟩
  have hAcc : (accumulateName time stride index multiplier scratch).run x
        (accumulateNameTime (cfg.values time) (cfg.values stride))
        ((accumulateName time stride index multiplier scratch).enter offset) =
        some accumulated := by
    have h := run_accumulateName x time stride index multiplier scratch offset hDistinct
      hOffsetMultiplier hOffsetScratch
    dsimp only at h
    rw [hComputedValues, hOffsetTime, hOffsetStride] at h
    exact h
  let named : name.Cfg := ⟨some none, namedValues, none, marked.output⟩
  have hNamed : name.run x (accept + accumulateNameTime (cfg.values time) (cfg.values stride))
      (name.enter marked) = some named := run_seq hInc rfl hAcc rfl
  let prepared : (terminators.seq name).Cfg := ⟨some none, namedValues, none, marked.output⟩
  have hPrepared : (terminators.seq name).run x
      (2 + (accept + accumulateNameTime (cfg.values time) (cfg.values stride)))
      ((terminators.seq name).enter cfg) = some prepared := run_seq hMarked rfl hNamed rfl
  have hPreparedIndex : prepared.values index = number := by simp [prepared, namedValues]
  have hRestored : (fun r ↦ if r = index then 0 else prepared.values r) = cfg.values := by
    funext r
    by_cases hr : r = index
    · subst r
      simp [hIndex]
    · simp [prepared, namedValues, hr]
  let framed : (emitFramedLiteral index true).Cfg :=
    ⟨some none, cfg.values, none, true :: (CNFCode.encodeLiteral (.pos number) ++ marked.output)⟩
  have hFramed : (emitFramedLiteral index true).run x (2 * number + 4)
      ((emitFramedLiteral index true).enter prepared) = some framed := by
    simpa only [hPreparedIndex, hRestored, ite_true] using
      run_emitFramedLiteral index true x prepared rfl
  let emitted : (emitBit (R := R) true).Cfg :=
    ⟨some none, cfg.values, none, true :: framed.output⟩
  have hEmitted : (emitBit true).run x 1 ((emitBit true).enter framed) = some emitted :=
    run_emitBit true x framed rfl
  let finished : clause.Cfg := ⟨some none, cfg.values, none, emitted.output⟩
  have hFinished : clause.run x (2 * number + 4 + 1) (clause.enter prepared) = some finished :=
    run_seq hFramed rfl hEmitted rfl
  have hResult := run_seq hPrepared rfl hFinished rfl
  simpa only [acceptingBlock, acceptingBlockTime, Config.map, Option.map_some, Option.map_none,
    finished, emitted, framed, marked,
    number, CNFCode.encodeClause_cons, CNFCode.encodeClause_nil, List.cons_append,
    List.append_assoc, List.singleton_append, List.nil_append] using hResult

end PvsNP.RegisterMachine.Fragment
