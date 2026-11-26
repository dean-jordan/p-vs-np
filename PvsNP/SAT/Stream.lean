module

public import PvsNP.SAT.Assignment

/-! # Streaming check of a binary CNF formula

The grammar uses finite control to track the formula, clauses, signs, and
terminators. A unary index uses a cursor that advances on each `1` and reads
the certificate on the terminating `0`.
-/

@[expose] public section

namespace PvsNP.SATStream

open CNF (Clause Formula Literal)
open CNFCode (encode encodeClause encodeIndex encodeLiteral)
open SATAssignment (checkFormula evalLiteral)

/-- The control stage, accumulated truth flags, and unary index cursor. -/
inductive State where
  | formula (allTrue : Bool)
  | clause (allTrue clauseTrue : Bool)
  | sign (allTrue clauseTrue : Bool)
  | index (allTrue clauseTrue positive : Bool) (cursor : Nat)
  | finished (allTrue : Bool)
  | invalid
  deriving DecidableEq

/-- Interpret the sign bit together with the cursor as a literal. -/
def signedLiteral (positive : Bool) (cursor : Nat) : Literal Nat :=
  if positive then .pos cursor else .neg cursor

/-- Process one formula bit. A unary `1` advances the cursor by one. -/
def step (assignment : BinaryWord) : State → Bool → State
  | .formula allTrue, false => .finished allTrue
  | .formula allTrue, true => .clause allTrue false
  | .clause allTrue clauseTrue, false => .formula (allTrue && clauseTrue)
  | .clause allTrue clauseTrue, true => .sign allTrue clauseTrue
  | .sign allTrue clauseTrue, positive => .index allTrue clauseTrue positive 0
  | .index allTrue clauseTrue positive cursor, false =>
    .clause allTrue (clauseTrue || evalLiteral assignment (signedLiteral positive cursor))
  | .index allTrue clauseTrue positive cursor, true =>
    .index allTrue clauseTrue positive (cursor + 1)
  | .finished _, _ | .invalid, _ => .invalid

/-- Run the stream, applying one transition to each successive input bit. -/
def run (assignment : BinaryWord) (state : State) (bits : BinaryWord) : State :=
  bits.foldl (step assignment) state

@[simp] theorem run_nil (assignment : BinaryWord) (state : State) :
    run assignment state [] = state := rfl

theorem run_cons (assignment : BinaryWord) (state : State) (bit : Bool) (rest : BinaryWord) :
    run assignment state (bit :: rest) = run assignment (step assignment state bit) rest := rfl

theorem run_append (assignment : BinaryWord) (state : State) (front suffix : BinaryWord) :
    run assignment state (front ++ suffix) = run assignment (run assignment state front) suffix :=
  List.foldl_append

/-- The current unary cursor, or zero before and after an index. -/
def State.cursor : State → Nat
  | .index _ _ _ position => position
  | _ => 0

private theorem cursor_step_le (assignment : BinaryWord) (state : State) (bit : Bool) :
    (step assignment state bit).cursor ≤ state.cursor + 1 := by
  cases state <;> cases bit <;> simp [step, State.cursor]

/-- The cursor advances at most once per processed bit. -/
theorem cursor_run_le (assignment : BinaryWord) (state : State) (bits : BinaryWord) :
    (run assignment state bits).cursor ≤ state.cursor + bits.length := by
  induction bits generalizing state with
  | nil => simp
  | cons bit rest ih =>
    rw [run_cons]
    have hRun := ih (step assignment state bit)
    have hStep := cursor_step_le assignment state bit
    simp only [List.length_cons]
    omega

private theorem run_invalid (assignment bits : BinaryWord) :
    run assignment .invalid bits = .invalid := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => exact ih

private theorem run_finished_cons (assignment : BinaryWord) (allTrue bit : Bool)
    (rest : BinaryWord) : run assignment (.finished allTrue) (bit :: rest) = .invalid :=
  run_invalid assignment rest

theorem run_encodeIndex (assignment : BinaryWord) (allTrue clauseTrue positive : Bool)
    (cursor n : Nat) (suffix : BinaryWord) :
    run assignment (.index allTrue clauseTrue positive cursor) (encodeIndex n ++ suffix) =
      run assignment
        (.clause allTrue
          (clauseTrue || evalLiteral assignment (signedLiteral positive (cursor + n)))) suffix := by
  induction n generalizing cursor with
  | zero => simp only [encodeIndex, List.cons_append, List.nil_append, run_cons, step, Nat.add_zero]
  | succ n ih =>
    simpa only [encodeIndex, List.cons_append, run_cons, step, Nat.succ_add, Nat.add_succ] using
      ih (cursor + 1)

theorem run_encodeLiteral (assignment : BinaryWord) (allTrue clauseTrue : Bool)
    (literal : Literal Nat) (suffix : BinaryWord) :
    run assignment (.sign allTrue clauseTrue) (encodeLiteral literal ++ suffix) =
      run assignment (.clause allTrue (clauseTrue || evalLiteral assignment literal)) suffix := by
  cases literal <;>
    simp only [encodeLiteral, List.cons_append, run_cons, step, run_encodeIndex, Nat.zero_add,
      signedLiteral, Bool.false_eq_true, ↓reduceIte]

theorem run_encodeClause (assignment : BinaryWord) (allTrue clauseTrue : Bool)
    (clause : Clause Nat) (suffix : BinaryWord) :
    run assignment (.clause allTrue clauseTrue) (encodeClause clause ++ suffix) =
      run assignment (.formula (allTrue && (clauseTrue || clause.any (evalLiteral assignment))))
        suffix := by
  induction clause generalizing clauseTrue with
  | nil =>
    simp only [CNFCode.encodeClause_nil, List.cons_append, List.nil_append, run_cons, step,
      List.any_nil, Bool.or_false]
  | cons literal clause ih =>
    simp only [CNFCode.encodeClause_cons, List.cons_append, run_cons, step, List.append_assoc,
      run_encodeLiteral, List.any_cons, ← Bool.or_assoc]
    exact ih _

/-- A complete code consumes exactly its own prefix and reaches the matching truth flag. -/
theorem run_encode (assignment : BinaryWord) (allTrue : Bool) (F : Formula Nat)
    (suffix : BinaryWord) :
    run assignment (.formula allTrue) (encode F ++ suffix) =
      run assignment (.finished (allTrue && checkFormula F assignment)) suffix := by
  induction F generalizing allTrue with
  | nil =>
    simp only [CNFCode.encode_nil, List.cons_append, List.nil_append, run_cons, step,
      checkFormula, List.all_nil, Bool.and_true]
  | cons clause F ih =>
    simp only [CNFCode.encode_cons, List.cons_append, run_cons, step, List.append_assoc,
      run_encodeClause, Bool.false_or, checkFormula, List.all_cons, ← Bool.and_assoc]
    exact ih _

private theorem index_prefix_of_finished (assignment : BinaryWord)
    (allTrue clauseTrue positive : Bool) (cursor : Nat) (bits : BinaryWord) {result : Bool}
    (h : run assignment (.index allTrue clauseTrue positive cursor) bits = .finished result) :
    ∃ n suffix,
      bits = encodeIndex n ++ suffix ∧
      run assignment
        (.clause allTrue
          (clauseTrue || evalLiteral assignment (signedLiteral positive (cursor + n))))
        suffix = .finished result := by
  induction bits generalizing cursor with
  | nil => cases h
  | cons bit bits ih =>
    cases bit with
    | false =>
      refine ⟨0, bits, rfl, ?_⟩
      simpa only [Nat.add_zero, run_cons, step] using h
    | true =>
      obtain ⟨n, suffix, hBits, hRun⟩ := ih (cursor + 1) h
      refine ⟨n + 1, suffix, ?_, ?_⟩
      · simpa only [encodeIndex, List.cons_append] using congrArg (List.cons true) hBits
      · simpa only [Nat.succ_add, Nat.add_succ] using hRun

private theorem literal_prefix_of_finished (assignment : BinaryWord) (allTrue clauseTrue : Bool)
    (bits : BinaryWord) {result : Bool}
    (h : run assignment (.sign allTrue clauseTrue) bits = .finished result) :
    ∃ literal suffix clauseTrue',
      bits = encodeLiteral literal ++ suffix ∧
      run assignment (.clause allTrue clauseTrue') suffix = .finished result := by
  cases bits with
  | nil => cases h
  | cons positive bits =>
    obtain ⟨n, suffix, hBits, hRun⟩ :=
      index_prefix_of_finished assignment allTrue clauseTrue positive 0 bits h
    have hCode : encodeLiteral (signedLiteral positive n) = positive :: encodeIndex n := by
      cases positive <;> rfl
    refine ⟨signedLiteral positive n, suffix, _, ?_, hRun⟩
    simpa only [hCode, List.cons_append] using congrArg (List.cons positive) hBits

private theorem clause_prefix_of_finished (assignment : BinaryWord) (allTrue clauseTrue : Bool)
    (bits : BinaryWord) {result : Bool}
    (h : run assignment (.clause allTrue clauseTrue) bits = .finished result) :
    ∃ clause suffix allTrue',
      bits = encodeClause clause ++ suffix ∧
      run assignment (.formula allTrue') suffix = .finished result := by
  generalize hLen : bits.length = n
  induction n using Nat.strongRecOn generalizing bits clauseTrue with
  | ind n ih =>
    cases bits with
    | nil => cases h
    | cons bit bits =>
      cases bit with
      | false =>
        exact ⟨[], bits, allTrue && clauseTrue, by simp, h⟩
      | true =>
        obtain ⟨literal, tail, clauseTrue', hBits, hRun⟩ :=
          literal_prefix_of_finished assignment allTrue clauseTrue bits h
        have hLt : tail.length < n := by
          simp only [List.length_cons] at hLen
          have hLen' := congrArg List.length hBits
          simp only [List.length_append] at hLen'
          omega
        obtain ⟨clause, suffix, allTrue', hTail, hEnd⟩ :=
          ih tail.length hLt clauseTrue' tail hRun rfl
        refine ⟨literal :: clause, suffix, allTrue', ?_, hEnd⟩
        rw [hBits, hTail, CNFCode.encodeClause_cons, List.cons_append, List.append_assoc]

private theorem formula_code_of_finished (assignment : BinaryWord) (allTrue : Bool)
    (bits : BinaryWord) {result : Bool}
    (h : run assignment (.formula allTrue) bits = .finished result) :
    ∃ F, bits = encode F := by
  generalize hLen : bits.length = n
  induction n using Nat.strongRecOn generalizing bits allTrue with
  | ind n ih =>
    cases bits with
    | nil => cases h
    | cons bit bits =>
      cases bit with
      | false =>
        cases bits with
        | nil => exact ⟨[], CNFCode.encode_nil.symm⟩
        | cons next rest =>
          change run assignment (.finished allTrue) (next :: rest) = .finished result at h
          rw [run_finished_cons] at h
          cases h
      | true =>
        obtain ⟨clause, tail, allTrue', hBits, hRun⟩ :=
          clause_prefix_of_finished assignment allTrue false bits h
        have hLt : tail.length < n := by
          simp only [List.length_cons] at hLen
          have hLen' := congrArg List.length hBits
          simp only [List.length_append] at hLen'
          omega
        obtain ⟨F, hTail⟩ := ih tail.length hLt allTrue' tail hRun rfl
        refine ⟨clause :: F, ?_⟩
        rw [hBits, hTail, CNFCode.encode_cons]

/-- The stream finishes exactly on a complete formula code and computes its truth value. -/
theorem run_finished_iff (assignment : BinaryWord) (allTrue : Bool) (bits : BinaryWord)
    (result : Bool) :
    run assignment (.formula allTrue) bits = .finished result ↔
      ∃ F, CNFCode.decode bits = some F ∧ (allTrue && checkFormula F assignment) = result := by
  have hEncode (F : Formula Nat) :
      run assignment (.formula allTrue) (encode F) =
        .finished (allTrue && checkFormula F assignment) := by
    simpa only [List.append_nil, run_nil] using run_encode assignment allTrue F []
  constructor
  · intro h
    obtain ⟨F, rfl⟩ := formula_code_of_finished assignment allTrue bits h
    exact ⟨F, CNFCode.decode_encode F, State.finished.inj ((hEncode F).symm.trans h)⟩
  · rintro ⟨F, hCodec, rfl⟩
    rw [CNFCode.decode_eq_some_iff.mp hCodec]
    exact hEncode F

/-- Return the truth flag of a complete stream and reject every other result. -/
def checkWord (word assignment : BinaryWord) : Bool :=
  match run assignment (.formula true) word with
  | .finished result => result
  | _ => false

/-- Streaming accepts exactly the words accepted by the decoded checker. -/
theorem checkWord_eq (word assignment : BinaryWord) :
    checkWord word assignment = SATAssignment.checkWord word assignment := by
  cases hDecoder : CNFCode.decode word with
  | none =>
    cases hRun : run assignment (.formula true) word with
    | finished result =>
      obtain ⟨F, h, _⟩ := (run_finished_iff assignment true word result).mp hRun
      rw [hDecoder] at h
      cases h
    | _ => simp [checkWord, SATAssignment.checkWord, hRun, hDecoder]
  | some F =>
    have hRun := (run_finished_iff assignment true word (checkFormula F assignment)).mpr
      ⟨F, hDecoder, Bool.true_and _⟩
    simp [checkWord, SATAssignment.checkWord, hRun, hDecoder]

end PvsNP.SATStream
