module

public import PvsNP.SAT.BinaryEncoding
public import PvsNP.TuringMachine.Registers.Program

/-! # A register program for emitting a framed literal -/

@[expose] public section

namespace PvsNP.CookLevin

open RegisterMachine

variable {R L : Type} [DecidableEq R]

/-- Start with the index terminator, emit one `1` per decrement, then the sign and the
literal's prefix bit. The index register is zero at the successor label. -/
structure EmitLiteralRules (program : L → Instruction R L) (index : R) (positive : Bool) where
  entry : L
  test : L
  one : L
  sign : L
  frame : L
  next : L
  writeTerminator : program entry = .emit false test
  readIndex : program test = .dec index sign one
  writeOne : program one = .emit true test
  writeSign : program sign = .emit positive frame
  writePrefix : program frame = .emit true next

variable {program : L → Instruction R L} {index : R} {positive : Bool}
  (rules : EmitLiteralRules program index positive) (x : BinaryWord)

private def cleared (index : R) (values : R → Nat) : R → Nat :=
  fun r ↦ if r = index then 0 else values r

private theorem run_ones {cfg : Config R L} (hPC : cfg.pc = some rules.test)
    (hCursor : cfg.cursor = none) :
    run program x (2 * cfg.values index + 1) cfg = some
      { cfg with
        pc := some rules.sign
        values := cleared index cfg.values
        output := List.replicate (cfg.values index) true ++ cfg.output } := by
  generalize hAmount : cfg.values index = n
  induction n generalizing cfg with
  | zero =>
    have hValues : cleared index cfg.values = cfg.values := by
      funext r
      by_cases h : r = index <;> simp [cleared, h, hAmount]
    rw [hValues]
    simp only [Nat.mul_zero, List.replicate_zero, List.nil_append, run_succ,
      step_dec_zero (x := x) hPC rules.readIndex hAmount, Option.bind_some, run_zero]
  | succ n ih =>
    have hPos : 0 < cfg.values index := hAmount ▸ Nat.succ_pos n
    let lowered := { cfg with pc := some rules.one, values := decrementValues index cfg.values }
    let mid := { lowered with pc := some rules.test, output := true :: cfg.output }
    have hPair : run program x 2 cfg = some mid := by
      rw [run_succ, step_dec_pos hPC rules.readIndex hPos, Option.bind_some]
      change run program x 1 lowered = some mid
      rw [run_succ, step_emit (cfg := lowered) (x := x) rfl rules.writeOne hCursor,
        Option.bind_some, run_zero]
    have hCount : mid.values index = n := by simp [mid, lowered, decrementValues, hAmount]
    have hValues : cleared index mid.values = cleared index cfg.values := by
      funext r
      by_cases h : r = index <;> simp [mid, lowered, cleared, decrementValues, h]
    have hOut : List.replicate n true ++ true :: cfg.output =
        List.replicate (n + 1) true ++ cfg.output := by
      rw [List.replicate_succ', List.append_assoc]
      rfl
    rw [show 2 * (n + 1) + 1 = 2 + (2 * n + 1) by omega, run_add, hPair,
      Option.bind_some, ih (cfg := mid) rfl hCursor hCount, hValues]
    exact congrArg some (congrArg (fun content ↦
      { cfg with pc := some rules.sign, values := cleared index cfg.values, output := content })
      hOut)

private theorem encodeIndex_eq_replicate (n : Nat) :
    CNFCode.encodeIndex n = List.replicate n true ++ [false] := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [CNFCode.encodeIndex, ih, List.replicate_succ, List.cons_append]

/-- Emit exactly the prefix and code of one literal, in `2 * index + 4` instructions. -/
theorem run_emitLiteral {cfg : Config R L} (hPC : cfg.pc = some rules.entry)
    (hCursor : cfg.cursor = none) :
    run program x (2 * cfg.values index + 4) cfg = some
      { cfg with
        pc := some rules.next
        values := fun r ↦ if r = index then 0 else cfg.values r
        output := true :: (CNFCode.encodeLiteral
          (if positive then .pos (cfg.values index) else .neg (cfg.values index)) ++
            cfg.output) } := by
  let marked := { cfg with pc := some rules.test, output := false :: cfg.output }
  have hFirst : run program x 1 cfg = some marked := by
    simp only [run_succ, step_emit (x := x) hPC rules.writeTerminator hCursor,
      Option.bind_some, run_zero, marked]
  have hOnes := run_ones rules x (cfg := marked) rfl hCursor
  let finishedIndex := { marked with
    pc := some rules.sign
    values := cleared index cfg.values
    output := List.replicate (cfg.values index) true ++ false :: cfg.output }
  have hIndex : run program x (2 * cfg.values index + 1) marked = some finishedIndex := hOnes
  have hSign : run program x 2 finishedIndex = some
      { finishedIndex with
        pc := some rules.next
        output := true :: positive :: finishedIndex.output } := by
    let withSign := { finishedIndex with
      pc := some rules.frame
      output := positive :: finishedIndex.output }
    rw [run_succ, step_emit (cfg := finishedIndex) (x := x) rfl rules.writeSign hCursor,
      Option.bind_some]
    change run program x 1 withSign = _
    rw [run_succ, step_emit (cfg := withSign) (x := x) rfl rules.writePrefix hCursor,
      Option.bind_some, run_zero]
  rw [show 2 * cfg.values index + 4 = 1 + (2 * cfg.values index + 1 + 2) by omega,
    run_add, hFirst, Option.bind_some, run_add, hIndex, Option.bind_some, hSign]
  cases positive <;> simp [finishedIndex, marked, CNFCode.encodeLiteral,
    encodeIndex_eq_replicate, List.append_assoc] <;> rfl

end PvsNP.CookLevin
