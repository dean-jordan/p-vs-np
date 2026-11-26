module

public import PvsNP.SAT.AdvanceCursor
public import PvsNP.SAT.ReleaseCursor
public import PvsNP.SAT.ResetCursor

/-! # Verification of the single-tape CNF checker

The proof counts every transition of the delimiter check and the parser. At
most one shuttle is used for each formula bit. Malformed pairs reject during
setup, and malformed or incomplete formulas reject when parsing ends.
-/

@[expose] public section

namespace PvsNP.SATMachine

open SATCursor (Control Config)

private def assignmentTape (assignment : BinaryWord) (control : Control) (cursor : Nat) :
    List Symbol :=
  match control with
  | .index _ _ _ => bits (assignment.take cursor) ++ markFirst (assignment.drop cursor)
  | _ => bits assignment

private def parserConfig (cfg : Config) (left : List Symbol) (word assignment : BinaryWord) :
    verifierMachine.Config :=
  phaseConfig (.parse cfg.control) left
    (bits word ++ .delimiter :: assignmentTape assignment cfg.control cfg.cursor)

private theorem cursor_step_le (assignment : BinaryWord) (cfg : Config) (bit : Bool)
    (h : cfg.cursor ≤ assignment.length) :
    (SATCursor.step assignment cfg bit).cursor ≤ assignment.length := by
  rcases hStep : SATCursor.transition cfg.control bit assignment[cfg.cursor]? with ⟨next, action⟩
  cases action <;> simp [SATCursor.step, hStep, SATCursor.Action.apply, h]

private theorem read_cursor (assignment : BinaryWord) (cursor : Nat) :
    (assignment.drop cursor).head? = assignment[cursor]? := by
  rw [List.head?_eq_getElem?, List.getElem?_drop, Nat.add_zero]

private theorem advance_assignmentTape (assignment : BinaryWord) (cursor : Nat)
    (h : cursor ≤ assignment.length) :
    (match assignment.drop cursor with
    | [] => bits (assignment.take cursor) ++ markFirst []
    | a :: tail => bits (assignment.take cursor ++ [a]) ++ markFirst tail) =
      bits (assignment.take (min (cursor + 1) assignment.length)) ++
        markFirst (assignment.drop (min (cursor + 1) assignment.length)) := by
  cases hDrop : assignment.drop cursor with
  | nil =>
    have hc : cursor = assignment.length := Nat.le_antisymm h (List.drop_eq_nil_iff.mp hDrop)
    rw [← hc, Nat.min_eq_right (Nat.le_succ _), hDrop]
  | cons a tail =>
    have hlt : cursor < assignment.length := by
      by_contra! hn
      have hEmpty : assignment.drop cursor = [] := List.drop_eq_nil_of_le hn
      rw [hDrop] at hEmpty
      cases hEmpty
    have hRead : assignment[cursor]? = some a := by
      rw [← read_cursor, hDrop]
      rfl
    rw [Nat.min_eq_left (Nat.succ_le_of_lt hlt), List.take_add_one, hRead,
      List.drop_add_one_eq_tail_drop, hDrop]
    rfl

private theorem run_one (cfg : verifierMachine.Config) :
    verifierMachine.run 1 cfg = verifierMachine.tick cfg := rfl

private theorem run_bit (cfg : Config) (left : List Symbol) (bit : Bool)
    (rest assignment : BinaryWord) (hCursor : cfg.cursor ≤ assignment.length) :
    ∃ t ≤ 2 * (rest.length + assignment.length) + 7,
      verifierMachine.run t (parserConfig cfg left (bit :: rest) assignment) =
      parserConfig (SATCursor.step assignment cfg bit) (.bit bit :: left) rest assignment := by
  obtain ⟨q, cursor⟩ := cfg
  cases q with
  | formula f =>
    cases bit
    · refine ⟨1, by omega, ?_⟩
      rw [run_one]
      exact tick_right (.parse (.formula f)) (.parse (.finished f)) left
        (bits rest ++ .delimiter :: bits assignment) (.bit false) (.bit false) rfl
    · refine ⟨1, by omega, ?_⟩
      rw [run_one]
      exact tick_right (.parse (.formula f)) (.parse (.clause f false)) left
        (bits rest ++ .delimiter :: bits assignment) (.bit true) (.bit true) rfl
  | clause f c =>
    cases bit
    · refine ⟨1, by omega, ?_⟩
      rw [run_one]
      exact tick_right (.parse (.clause f c)) (.parse (.formula (f && c))) left
        (bits rest ++ .delimiter :: bits assignment) (.bit false) (.bit false) rfl
    · refine ⟨1, by omega, ?_⟩
      rw [run_one]
      exact tick_right (.parse (.clause f c)) (.parse (.sign f c)) left
        (bits rest ++ .delimiter :: bits assignment) (.bit true) (.bit true) rfl
  | finished f =>
    refine ⟨1, by omega, ?_⟩
    rw [run_one]
    exact tick_right (.parse (.finished f)) (.parse .invalid) left
      (bits rest ++ .delimiter :: bits assignment) (.bit bit) (.bit bit) rfl
  | invalid =>
    refine ⟨1, by omega, ?_⟩
    rw [run_one]
    exact tick_right (.parse .invalid) (.parse .invalid) left
      (bits rest ++ .delimiter :: bits assignment) (.bit bit) (.bit bit) rfl
  | sign f c =>
    exact ⟨2 * rest.length + 5, by omega, run_reset f c bit left rest assignment⟩
  | index f c sign =>
    have hTake : (assignment.take cursor).length ≤ assignment.length := by simp
    cases bit with
    | false =>
      refine ⟨2 * (rest.length + (assignment.take cursor).length) + 5, by omega, ?_⟩
      have hr := run_release f c sign left rest (assignment.take cursor) (assignment.drop cursor)
      simpa only [parserConfig, SATCursor.step, SATCursor.transition, SATCursor.Action.apply,
        assignmentTape, List.map_cons, List.cons_append, List.take_append_drop, read_cursor]
        using hr
    | true =>
      obtain ⟨t, ht, hr⟩ := run_advance f c sign left rest
        (assignment.take cursor) (assignment.drop cursor)
      have updated := congrArg
        (fun tail ↦ phaseConfig (.parse (.index f c sign)) (.bit true :: left)
          (bits rest ++ .delimiter :: tail))
        (advance_assignmentTape assignment cursor hCursor)
      exact ⟨t, by omega, hr.trans updated⟩

private theorem run_delimiter (cfg : Config) (left : List Symbol) (assignment : BinaryWord) :
    (verifierMachine.run 1 (parserConfig cfg left [] assignment)).state =
      .inr cfg.control.result := by
  have ht := verifierMachine.tick_tapeFromLists_cons (.inr (.parse cfg.control)) left
    (assignmentTape assignment cfg.control cfg.cursor) .delimiter
    (q' := .inr cfg.control.result) (b := .delimiter) (dir := .right) rfl
  exact congrArg Machine.Config.state ht

private theorem run_parser (cfg : Config) (left : List Symbol) (word assignment : BinaryWord)
    (hCursor : cfg.cursor ≤ assignment.length) (limit : Nat)
    (hLength : word.length + assignment.length ≤ limit) :
    ∃ t ≤ word.length * (2 * limit + 7) + 1,
      (verifierMachine.run t (parserConfig cfg left word assignment)).state =
        .inr (SATCursor.run assignment cfg word).control.result := by
  induction word generalizing cfg left with
  | nil => exact ⟨1, by simp, run_delimiter cfg left assignment⟩
  | cons bit rest ih =>
    have hRest : rest.length + assignment.length ≤ limit := by
      simp only [List.length_cons] at hLength
      omega
    obtain ⟨t, ht, hStep⟩ := run_bit cfg left bit rest assignment hCursor
    obtain ⟨u, hu, hRun⟩ := ih (SATCursor.step assignment cfg bit) (.bit bit :: left)
      (cursor_step_le assignment cfg bit hCursor) hRest
    refine ⟨t + u, ?_, ?_⟩
    · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
    · rw [Machine.run_add, hStep, hRun, SATCursor.run_cons]

/-- A uniform quadratic time bound in the length of the complete pair input. -/
def verifierTimeBound (n : Nat) : Nat := 2 * n + 4 + n * (2 * n + 7) + 1

theorem verifierTimeBound_polynomiallyBounded : PolynomiallyBounded verifierTimeBound := by
  let n := PolynomiallyBounded.id
  let twice := (PolynomiallyBounded.const 2).mul n
  exact ((twice.add (PolynomiallyBounded.const 4)).add
    (n.mul (twice.add (PolynomiallyBounded.const 7)))).add (PolynomiallyBounded.const 1)

/-- The machine halts with the checker's Boolean result within the uniform bound. -/
theorem verifierMachine_halt (pair : VerifierWord) :
    ∃ t ≤ verifierTimeBound pair.length,
      (verifierMachine.run t (verifierMachine.start pair)).state =
        .inr (SATAssignment.checkEncoded pair) := by
  cases decoded : decodePair pair with
  | none =>
    obtain ⟨t, ht, hRun⟩ := withInputSetup_malformed
      (Phase.parse SATCursor.initial.control) verifierProgram pair decoded
    refine ⟨t, ?_, ?_⟩
    · unfold verifierTimeBound
      omega
    · simpa only [SATAssignment.checkEncoded, decoded] using hRun
  | some p =>
    obtain ⟨word, assignment⟩ := p
    have prepared := withInputSetup_valid (Phase.parse SATCursor.initial.control)
      verifierProgram word assignment
    have heq : pair = encodePair word assignment := decodePair_eq_some_iff.mp decoded
    have hStart : verifierMachine.run (2 * pair.length + 4) (verifierMachine.start pair) =
        parserConfig SATCursor.initial [.leftEnd] word assignment := by
      rw [heq]
      rw [input_encodePair] at prepared
      exact prepared
    have hLength : word.length + assignment.length ≤ pair.length := by
      rw [heq, length_encodePair]
      omega
    obtain ⟨t, ht, hRun⟩ := run_parser SATCursor.initial [.leftEnd] word assignment
      (Nat.zero_le _) pair.length hLength
    have hMul := Nat.mul_le_mul_right (2 * pair.length + 7)
      (show word.length ≤ pair.length by omega)
    refine ⟨2 * pair.length + 4 + t, ?_, ?_⟩
    · unfold verifierTimeBound
      omega
    · rw [Machine.run_add, hStart, hRun]
      change Sum.inr (SATCursor.checkWord word assignment) = _
      rw [SATCursor.checkWord_eq]
      simp only [SATAssignment.checkEncoded, decoded]

theorem verifierMachine_polyTime : verifierMachine.PolyTime := by
  refine verifierMachine.polyTime_iff_polynomiallyBounded.mpr
    ⟨verifierTimeBound, verifierTimeBound_polynomiallyBounded, fun pair ↦ ?_⟩
  obtain ⟨t, ht, hb⟩ := verifierMachine_halt pair
  exact ⟨t, ht, SATAssignment.checkEncoded pair, hb⟩

theorem verifierMachine_decides :
    verifierMachine.Decides {pair : VerifierWord | SATAssignment.checkEncoded pair = true} := by
  intro pair
  obtain ⟨t, _, hRun⟩ := verifierMachine_halt pair
  change SATAssignment.checkEncoded pair = true ↔ verifierMachine.Accepts pair
  constructor
  · intro h
    exact ⟨t, h ▸ hRun⟩
  · rintro ⟨u, hu⟩
    exact verifierMachine.halt_result_unique _ hRun hu

/-- Cook's whole-input checker language has a polynomial-time decider. -/
theorem checkEncoded_mem_POver :
    {pair : VerifierWord | SATAssignment.checkEncoded pair = true} ∈ POver VerifierSymbol :=
  ⟨verifierMachine, verifierMachine_polyTime, verifierMachine_decides⟩

/-- Binary CNF satisfiability belongs to NP in the reference Cook model. -/
theorem cnfSAT_mem_NP : CNFSAT ∈ NP :=
  SATAssignment.mem_NP_of_checkEncoded_mem_P checkEncoded_mem_POver

end PvsNP.SATMachine
