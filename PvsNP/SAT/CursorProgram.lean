module

public import PvsNP.SAT.Stream

import Mathlib.Basic.Finite.Prod

/-! # Finite control for the streaming CNF checker

The parser flags are finite. A separate read-only certificate cursor carries
the position in the unary index. At the end of the certificate, the cursor
stays at the blank and every further read also supplies `false`.
-/

@[expose] public section

namespace PvsNP.SATCursor

/-- Parser flags and grammar stage, without the certificate position. -/
inductive Control where
  | formula (allTrue : Bool)
  | clause (allTrue clauseTrue : Bool)
  | sign (allTrue clauseTrue : Bool)
  | index (allTrue clauseTrue positive : Bool)
  | finished (allTrue : Bool)
  | invalid
  deriving DecidableEq

private def Control.code : Control → Fin 6 × Bool × Bool × Bool
  | .formula f => ⟨0, f, false, false⟩
  | .clause f c => ⟨1, f, c, false⟩
  | .sign f c => ⟨2, f, c, false⟩
  | .index f c p => ⟨3, f, c, p⟩
  | .finished f => ⟨4, f, false, false⟩
  | .invalid => ⟨5, false, false, false⟩

private theorem Control.code_injective : Function.Injective Control.code := by
  intro a b h
  cases a <;> cases b <;> simp_all [Control.code]

instance : Finite Control := Finite.of_injective Control.code Control.code_injective

/-- What to do with the certificate marker after consuming a formula bit. -/
inductive Action where
  | stay
  | reset
  | advance
  | release
  deriving DecidableEq

/-- A cursor reaching the end of the certificate reads the end blank thereafter. -/
def Action.apply (length cursor : Nat) : Action → Nat
  | .stay => cursor
  | .advance => min (cursor + 1) length
  | .reset | .release => 0

/-- Determine the literal truth flag from the sign and one certificate read. -/
def literalValue (positive : Bool) (value : Option Bool) : Bool :=
  if positive then value.getD false else !(value.getD false)

/-- One transition consumes one formula bit. Only the end of a unary index
uses the supplied certificate symbol. Its marker can then be released. -/
def transition : Control → Bool → Option Bool → Control × Action
  | .formula f, false, _ => (.finished f, .stay)
  | .formula f, true, _ => (.clause f false, .stay)
  | .clause f c, false, _ => (.formula (f && c), .stay)
  | .clause f c, true, _ => (.sign f c, .stay)
  | .sign f c, p, _ => (.index f c p, .reset)
  | .index f c p, true, _ => (.index f c p, .advance)
  | .index f c p, false, value => (.clause f (c || literalValue p value), .release)
  | .finished _, _, _ | .invalid, _, _ => (.invalid, .stay)

/-- Terminal observation after the formula word has been consumed. -/
def Control.result : Control → Bool
  | .finished result => result
  | _ => false

/-- Separate the finite grammar state from the physical certificate position. -/
structure Config where
  control : Control
  cursor : Nat

/-- Drop the unary counter from the reference checker's control state. -/
def Control.ofStream : SATStream.State → Control
  | .formula f => .formula f
  | .clause f c => .clause f c
  | .sign f c => .sign f c
  | .index f c p _ => .index f c p
  | .finished f => .finished f
  | .invalid => .invalid

/-- Interpret the cursor as a physical position saturated at the end blank. -/
def Config.ofStream (length : Nat) (state : SATStream.State) : Config :=
  ⟨Control.ofStream state, min state.cursor length⟩

/-- Before the first formula bit the checker is between clauses. -/
def initial : Config := ⟨.formula true, 0⟩

/-- Consume one formula bit and perform its certificate cursor operation. -/
def step (assignment : BinaryWord) (cfg : Config) (bit : Bool) : Config :=
  let (control, action) := transition cfg.control bit assignment[cfg.cursor]?
  ⟨control, action.apply assignment.length cfg.cursor⟩

/-- Run the instruction program for one step per formula bit. -/
def run (assignment : BinaryWord) (cfg : Config) (word : BinaryWord) : Config :=
  word.foldl (step assignment) cfg

theorem run_cons (assignment : BinaryWord) (cfg : Config) (bit : Bool) (word : BinaryWord) :
    run assignment cfg (bit :: word) = run assignment (step assignment cfg bit) word := rfl

theorem run_append (assignment : BinaryWord) (cfg : Config) (word rest : BinaryWord) :
    run assignment cfg (word ++ rest) = run assignment (run assignment cfg word) rest :=
  List.foldl_append

/-- Saturating at the first blank preserves all certificate reads. -/
theorem read_saturated (assignment : BinaryWord) (i : Nat) :
    assignment[min i assignment.length]? = assignment[i]? := by
  by_cases inBounds : i ≤ assignment.length
  · rw [Nat.min_eq_left inBounds]
  · have h := Nat.le_of_lt (Nat.lt_of_not_ge inBounds)
    rw [Nat.min_eq_right h, List.getElem?_eq_none h, List.getElem?_eq_none (Nat.le_refl _)]

/-- One cursor advance corresponds to one increment of the reference counter. -/
theorem advance_saturated (i length : Nat) :
    Action.advance.apply length (min i length) = min (i + 1) length := by
  change min (min i length + 1) length = min (i + 1) length
  omega

private theorem eval_signed (assignment : BinaryWord) (p : Bool) (i : Nat) :
    SATAssignment.evalLiteral assignment (SATStream.signedLiteral p i) =
      literalValue p assignment[i]? := by
  cases p <;> rfl

/-- The abstract cursor program simulates one reference streaming step. -/
theorem step_ofStream (assignment : BinaryWord) (state : SATStream.State) (bit : Bool) :
    step assignment (Config.ofStream assignment.length state) bit =
      Config.ofStream assignment.length (SATStream.step assignment state bit) := by
  have hAdvance (i : Nat) :
      min (min i assignment.length + 1) assignment.length = min (i + 1) assignment.length :=
    advance_saturated i assignment.length
  cases state <;> cases bit <;>
    simp [step, Config.ofStream, Control.ofStream, SATStream.step, SATStream.State.cursor,
      transition, Action.apply, read_saturated, eval_signed, hAdvance]

/-- Each bit's simulation composes over the entire input word. -/
theorem run_ofStream (assignment : BinaryWord) (state : SATStream.State) (word : BinaryWord) :
    run assignment (Config.ofStream assignment.length state) word =
      Config.ofStream assignment.length (SATStream.run assignment state word) := by
  induction word generalizing state with
  | nil => rfl
  | cons bit rest ih => rw [run_cons, SATStream.run_cons, step_ofStream, ih]

/-- Read the acceptance flag after the final word symbol. -/
def checkWord (word assignment : BinaryWord) : Bool := (run assignment initial word).control.result

/-- The finite-control checker accepts exactly the same pairs as the reference. -/
theorem checkWord_eq (word assignment : BinaryWord) :
    checkWord word assignment = SATAssignment.checkWord word assignment := by
  rw [← SATStream.checkWord_eq]
  change (run assignment (Config.ofStream assignment.length (.formula true)) word).control.result =
    SATStream.checkWord word assignment
  rw [run_ofStream]
  unfold SATStream.checkWord
  cases SATStream.run assignment (.formula true) word <;> rfl

end PvsNP.SATCursor
