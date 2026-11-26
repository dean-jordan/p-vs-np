module

public import PvsNP.SAT.BinaryEncoding

/-!
# Reverse CNF serialization

Emitting each bit to the left of the preceding bits requires visiting the
formula and each clause in reverse order. Fold the emission operation over
this order, beginning with each list terminator.
-/

@[expose] public section

namespace PvsNP.CookLevin.Serialization

open CNF (Clause Formula Literal)

variable {σ : Type} (emit : σ → Bool → σ)

/-- Emit a fixed number of unary digits into the accumulator. -/
def emitOnes (acc : σ) : Nat → σ
  | 0 => acc
  | n + 1 => emitOnes (emit acc true) n

/-- Emit a unary index with its terminator first. -/
def emitIndex (acc : σ) (index : Nat) : σ :=
  emitOnes emit (emit acc false) index

/-- Emit a literal's index, then its sign bit. -/
def emitLiteral (acc : σ) : Literal Nat → σ
  | .pos index => emit (emitIndex emit acc index) true
  | .neg index => emit (emitIndex emit acc index) false

/-- Emit the clause terminator, then its literals from last to first. -/
def emitClause (acc : σ) (clause : Clause Nat) : σ :=
  clause.reverse.foldl (fun acc lit ↦ emit (emitLiteral emit acc lit) true) (emit acc false)

/-- Emit the formula terminator, then its clauses from last to first. -/
def emitFormula (acc : σ) (formula : Formula Nat) : σ :=
  formula.reverse.foldl (fun acc clause ↦ emit (emitClause emit acc clause) true) (emit acc false)

private theorem emitOnes_eq_foldl (acc : σ) (index : Nat) :
    emitOnes emit acc index = (List.replicate index true).foldl emit acc := by
  induction index generalizing acc with
  | zero => rfl
  | succ n ih => simp [emitOnes, List.replicate_succ, ih]

private theorem reverse_encodeIndex (index : Nat) :
    (CNFCode.encodeIndex index).reverse = false :: List.replicate index true := by
  induction index with
  | zero => rfl
  | succ n ih => simp [CNFCode.encodeIndex, ih, List.replicate_succ']

theorem emitIndex_eq_foldl (acc : σ) (index : Nat) :
    emitIndex emit acc index = (CNFCode.encodeIndex index).reverse.foldl emit acc := by
  simp [emitIndex, reverse_encodeIndex, emitOnes_eq_foldl]

theorem emitLiteral_eq_foldl (acc : σ) (lit : Literal Nat) :
    emitLiteral emit acc lit = (CNFCode.encodeLiteral lit).reverse.foldl emit acc := by
  cases lit <;> simp [emitLiteral, emitIndex_eq_foldl, CNFCode.encodeLiteral]

theorem emitClause_eq_foldl (acc : σ) (clause : Clause Nat) :
    emitClause emit acc clause = (CNFCode.encodeClause clause).reverse.foldl emit acc := by
  induction clause with
  | nil => simp [emitClause]
  | cons lit clause ih =>
    calc
      emitClause emit acc (lit :: clause) =
          emit (emitLiteral emit (emitClause emit acc clause) lit) true := by
        simp [emitClause]
      _ = (CNFCode.encodeClause (lit :: clause)).reverse.foldl emit acc := by
        simp [CNFCode.encodeClause_cons, ih, emitLiteral_eq_foldl]

/-- The streaming fold emits exactly the reversed binary encoding. -/
theorem emitFormula_eq_foldl (acc : σ) (formula : Formula Nat) :
    emitFormula emit acc formula = (CNFCode.encode formula).reverse.foldl emit acc := by
  induction formula with
  | nil => simp [emitFormula]
  | cons clause formula ih =>
    calc
      emitFormula emit acc (clause :: formula) =
          emit (emitClause emit (emitFormula emit acc formula) clause) true := by
        simp [emitFormula]
      _ = (CNFCode.encode (clause :: formula)).reverse.foldl emit acc := by
        simp [CNFCode.encode_cons, ih, emitClause_eq_foldl]

/-- A prepend-only emitter leaves the original formula code ahead of its existing suffix. -/
theorem emitFormula_prepend (suffix : List Bool) (formula : Formula Nat) :
    emitFormula (fun acc bit ↦ bit :: acc) suffix formula = CNFCode.encode formula ++ suffix := by
  rw [emitFormula_eq_foldl, List.foldl_flip_cons_eq_append', List.reverse_reverse]

/-- The bits in chronological emission order. -/
def schedule (formula : Formula Nat) : List Bool :=
  (emitFormula (fun acc bit ↦ bit :: acc) [] formula).reverse

theorem schedule_eq_reverse_encode (formula : Formula Nat) :
    schedule formula = (CNFCode.encode formula).reverse := by
  simp [schedule, emitFormula_prepend]

/-- Exactly one bit emission is required per bit of the formula code. -/
@[simp] theorem length_schedule (formula : Formula Nat) :
    (schedule formula).length = (CNFCode.encode formula).length := by
  simp [schedule_eq_reverse_encode]

end PvsNP.CookLevin.Serialization
