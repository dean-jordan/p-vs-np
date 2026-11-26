module

public import PvsNP.TuringMachine.Registers.Decision
public import PvsNP.TuringMachine.Registers.PackedPairScan

/-! # Cook decision for canonical packed pairs -/

public section

namespace PvsNP

open RegisterMachine RegisterMachine.Fragment

private abbrev emitPackedValidity : Fragment (Fin 3) where
  Label := Option Bool
  entry := some none
  code
    | none => .dec 2 (some (some false)) (some (some true))
    | some answer => .emit answer none

private theorem run_emitPackedValidity (x : BinaryWord) (values : Fin 3 → Nat) :
    emitPackedValidity.run x 2
      (emitPackedValidity.enter (⟨none, values, none, []⟩ : Config (Fin 3) Unit)) =
      some ⟨some none, decrementValues 2 values, none, [decide (0 < values 2)]⟩ := by
  let program := emitPackedValidity.close
  let start := emitPackedValidity.enter (⟨none, values, none, []⟩ : Config (Fin 3) Unit)
  let tested (answer : Bool) : emitPackedValidity.Cfg :=
    ⟨some (some (some answer)), decrementValues 2 values, none, []⟩
  let answer := decide (0 < values 2)
  have hStep : step program x start = some (tested answer) := by
    by_cases hZero : values 2 = 0
    · have hDecrement : decrementValues 2 values = values := by
        funext lane
        by_cases hLane : lane = 2 <;> simp [decrementValues, hLane, hZero]
      have hRead := step_dec_zero (program := program) (x := x) (cfg := start) rfl rfl hZero
      simpa only [tested, answer, start, enter, hZero, Nat.lt_irrefl, decide_false, hDecrement]
        using hRead
    · have hPos := Nat.pos_of_ne_zero hZero
      have hRead := step_dec_pos (program := program) (x := x) (cfg := start) rfl rfl hPos
      simpa only [tested, answer, start, enter, decide_eq_true hPos] using hRead
  have hEmit : step program x (tested answer) =
      some ⟨some none, decrementValues 2 values, none, [answer]⟩ :=
    step_emit (label := some (some answer)) rfl rfl rfl
  change RegisterMachine.run program x 2 start = _
  simp only [RegisterMachine.run, hStep, hEmit, Option.bind_some]
  rfl

private abbrev packedSyntaxProgram : Fragment (Fin 3) :=
  (packedPairScan 0 1 2).seq emitPackedValidity

private theorem run_packedSyntaxProgram (x : BinaryWord) :
    ∃ steps ≤ 2 * x.length + 5, ∃ cfg,
      RegisterMachine.run packedSyntaxProgram.close x steps
        (Config.initial packedSyntaxProgram.entry) = some cfg ∧ cfg.pc = none ∧
      cfg.output = [(decodePackedPair x).isSome] := by
  let values : Fin 3 → Nat := fun _ ↦ 0
  obtain ⟨ticks, hTime, after, hScan, hCounts, _⟩ := runsValues_packedPairScan
    (0 : Fin 3) 1 2 (by decide) (by decide) (by decide) x values
  have hValid : decide (0 < after 2) = (decodePackedPair x).isSome := by
    cases hPair : decodePackedPair x with
    | none =>
      rw [hPair] at hCounts
      simp [hCounts, values]
    | some pair =>
      obtain ⟨u, v⟩ := pair
      rw [hPair] at hCounts
      change after 2 = values 2 + 1 ∧ _ at hCounts
      simp [hCounts.1, values]
  have hSeq := run_seq (hScan []) rfl (run_emitPackedValidity x after) rfl
  have hHalt := run_close hSeq rfl rfl
  refine ⟨ticks + 2 + 1, by omega, _, hHalt, rfl, ?_⟩
  exact congrArg (fun answer ↦ [answer]) hValid

/-- The canonical packed instance and certificate syntax is decidable in Cook's `P`. -/
theorem packedPairSyntax_mem_P : {w : BinaryWord | ∃ x y, w = packedPair x y} ∈ P := by
  have hLanguage : {w : BinaryWord | (decodePackedPair w).isSome = true} =
      {w : BinaryWord | ∃ x y, w = packedPair x y} := by
    ext w
    change (decodePackedPair w).isSome = true ↔ ∃ x y, w = packedPair x y
    rw [Option.isSome_iff_exists]
    constructor
    · rintro ⟨⟨x, y⟩, h⟩
      exact ⟨x, y, decodePackedPair_eq_some_iff.mp h⟩
    · rintro ⟨x, y, h⟩
      exact ⟨(x, y), decodePackedPair_eq_some_iff.mpr h⟩
  rw [← hLanguage]
  have hBound : PolynomiallyBounded (fun n ↦ 2 * n + 5) :=
    ((PolynomiallyBounded.const 2).mul PolynomiallyBounded.id).add
      (PolynomiallyBounded.const 5)
  exact mem_P_of_boolean_run packedSyntaxProgram.entry packedSyntaxProgram.close
    hBound run_packedSyntaxProgram

end PvsNP
