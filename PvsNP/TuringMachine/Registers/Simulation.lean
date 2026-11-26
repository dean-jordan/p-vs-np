module

public import PvsNP.TuringMachine.Registers.Arithmetic
public import PvsNP.TuringMachine.Registers.Control
public import PvsNP.TuringMachine.Registers.DecrementCorrectness
public import PvsNP.TuringMachine.Registers.InputLayout

/-! # Single-instruction simulation on Cook's tape -/

@[expose] public section

namespace PvsNP.RegisterMachine

variable {R L : Type} [Finite R] [Finite L] [DecidableEq R]

/-- The tape at a program label contains the original input, packed register values, and
the output. At halt only the output remains, in canonical position. -/
def Matches (entry : L) (program : L → Instruction R L) (x : BinaryWord) (work : Nat)
    (cfg : Config R L) (tapeCfg : (control entry program).Config) : Prop :=
  let M := control entry program
  match cfg.pc with
  | none => tapeCfg = ⟨.inr true, M.wordTape cfg.output⟩
  | some label => ∃ (left : List (Symbol R)) (cells : List (R → Bool)),
      cells.length ≤ work ∧ Represents cells cfg.values ∧
      InputLayout x.reverse (bits cfg.output.reverse) cfg.cursor left ∧
      tapeCfg = ⟨.inl (ControlState.label label), M.tapeFromLists left (.home :: trackTape cells)⟩

theorem Matches.halted {entry : L} {program : L → Instruction R L} {x : BinaryWord} {work : Nat}
    {cfg : Config R L} {c : (control entry program).Config}
    (h : Matches entry program x work cfg c) (hPC : cfg.pc = none) :
    c = ⟨.inr true, (control entry program).wordTape cfg.output⟩ := by
  simpa only [Matches, hPC] using h

theorem matches_start (entry : L) (program : L → Instruction R L) (x : BinaryWord) :
    Matches entry program x 0 (Config.initial entry)
      ((control entry program).run (x.length + 4) ((control entry program).start x)) := by
  refine ⟨bits x.reverse ++ [.start], [], Nat.le_refl _, ?_, InputLayout.unmarked, ?_⟩
  · exact (represents_nil_iff _).mpr fun _ ↦ rfl
  · unfold bits
    rw [List.map_reverse]
    exact run_setup (controlSetupRules entry program) x

/-- Each successful register instruction is implemented by counted tape sweeps.
The work bound allows one new packed cell after the instruction. -/
theorem Matches.step {entry : L} {program : L → Instruction R L} {x : BinaryWord} {work : Nat}
    {cfg cfg' : Config R L} {tapeCfg : (control entry program).Config}
    (h : Matches entry program x work cfg tapeCfg) (hOut : cfg.output.length ≤ work)
    (hStep : step program x cfg = some cfg') :
    ∃ ticks ≤ 2 * x.length + 3 * work + 6,
      Matches entry program x (work + 1) cfg' ((control entry program).run ticks tapeCfg) := by
  cases hPC : cfg.pc with
  | none => simp [RegisterMachine.step, hPC] at hStep
  | some label =>
    simp only [Matches, hPC] at h
    obtain ⟨left, cells, hCells, hValues, hInput, rfl⟩ := h
    cases hInstr : program label with
    | inc lane next =>
      rw [step_inc hPC hInstr, Option.some.injEq] at hStep
      subst cfg'
      have hSize := hValues.value_le_length lane
      refine ⟨2 * cfg.values lane + 4, by omega, left, incrementCells lane cells,
        Nat.le_trans (length_incrementCells_le lane cells) (Nat.succ_le_succ hCells),
        hValues.increment lane, hInput, ?_⟩
      exact run_increment .initial (controlIncrementRules entry program label next lane hInstr)
        left hValues
    | dec lane zero next =>
      have hRun := run_decrement .initial
        (controlDecrementRules entry program label zero next lane hInstr) left hValues
      dsimp only at hRun
      by_cases hz : cfg.values lane = 0
      · rw [step_dec_zero hPC hInstr hz, Option.some.injEq] at hStep
        subst cfg'
        refine ⟨2, by omega, left, cells, by omega, hValues, hInput, ?_⟩
        simp only [ite_eq_left hz, decrementCells_of_value_zero lane hValues hz] at hRun
        exact hRun
      · rw [step_dec_pos hPC hInstr (Nat.pos_of_ne_zero hz), Option.some.injEq] at hStep
        subst cfg'
        have hSize := hValues.value_le_length lane
        refine ⟨2 * cfg.values lane + 4, by omega, left, decrementCells lane cells, ?_,
          hValues.decrement lane, hInput, ?_⟩
        · rw [length_decrementCells]
          omega
        · simp only [ite_eq_right hz] at hRun
          exact hRun
    | readFirst next =>
      cases hCursor : cfg.cursor with
      | some i =>
        simp only [step_at hPC, hInstr, Instruction.execute, hCursor, reduceCtorEq] at hStep
      | none =>
        rw [step_readFirst hPC hInstr hCursor, Option.some.injEq] at hStep
        subst cfg'
        rw [hCursor] at hInput
        cases hInput
        obtain ⟨left, hRead, hRun⟩ := run_cursor_first .initial
          (controlReadFirstRules entry program label next hInstr) x.reverse
          (bits cfg.output.reverse) (trackTape cells)
        exact ⟨4, by omega, left, cells, by omega, hValues, hRead, hRun⟩
    | readNext next =>
      cases hCursor : cfg.cursor with
      | none =>
        simp only [step_at hPC, hInstr, Instruction.execute, hCursor, reduceCtorEq] at hStep
      | some i =>
        rw [step_readNext hPC hInstr hCursor, Option.some.injEq] at hStep
        subst cfg'
        rw [hCursor] at hInput
        have hPos : i < x.length := by simpa only [List.length_reverse] using hInput.index_lt
        obtain ⟨left, hRead, hRun⟩ := hInput.run_next .initial
          (controlReadNextRules entry program label next hInstr) (trackTape cells)
        exact ⟨2 * i + 6, by omega, left, cells, by omega, hValues, hRead, hRun⟩
    | resetInput next =>
      cases hCursor : cfg.cursor with
      | none =>
        simp only [step_at hPC, hInstr, Instruction.execute, hCursor, reduceCtorEq] at hStep
      | some i =>
        rw [step_resetInput hPC hInstr hCursor, Option.some.injEq] at hStep
        subst cfg'
        rw [hCursor] at hInput
        have hPos : i < x.length := by simpa only [List.length_reverse] using hInput.index_lt
        cases hInput with
        | marked near tail b hWord =>
          refine ⟨2 * near.length + 4, by omega, _, cells, by omega, hValues,
            InputLayout.unmarked, ?_⟩
          simpa only [hWord, List.map_append, List.map_cons, List.append_assoc,
            List.cons_append] using run_control_resetInput entry program label next near b
              (bits tail ++ .start :: bits cfg.output.reverse) (trackTape cells) hInstr
    | emit bit next =>
      cases hCursor : cfg.cursor with
      | some i =>
        simp only [step_at hPC, hInstr, Instruction.execute, hCursor, reduceCtorEq] at hStep
      | none =>
        rw [step_emit hPC hInstr hCursor, Option.some.injEq] at hStep
        subst cfg'
        rw [hCursor] at hInput
        cases hInput
        refine ⟨2 * (x.length + cfg.output.length) + 6, by omega,
          bits x.reverse ++ .start :: bits (bit :: cfg.output).reverse, cells, by omega,
          hValues, ?_, ?_⟩
        · change InputLayout x.reverse (bits (bit :: cfg.output).reverse) cfg.cursor _
          rw [hCursor]
          exact InputLayout.unmarked
        · simpa only [List.length_reverse, List.reverse_cons] using
            run_control_emitBit entry program label next x cfg.output.reverse bit
              (trackTape cells) hInstr
    | halt =>
      cases hCursor : cfg.cursor with
      | some i =>
        simp only [step_at hPC, hInstr, Instruction.execute, hCursor, reduceCtorEq] at hStep
      | none =>
        rw [step_halt hPC hInstr hCursor, Option.some.injEq] at hStep
        subst cfg'
        rw [hCursor] at hInput
        cases hInput
        refine ⟨2 * cells.length + x.length + cfg.output.length + 5, by omega, ?_⟩
        simpa only [Matches, List.length_reverse, List.reverse_reverse] using
          run_control_finish entry program label x cfg.output.reverse cells hInstr

end PvsNP.RegisterMachine
