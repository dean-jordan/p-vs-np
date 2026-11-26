module

public import PvsNP.CookLevin.Generator.FiniteTable
public import PvsNP.CookLevin.Generator.FrameNames
public import PvsNP.TuringMachine.Registers.OutputRuns

/-! # Emitting the tableau's local transition update clauses -/

@[expose] public section

namespace PvsNP.CookLevin

open RegisterMachine RegisterMachine.Fragment

/-- Two persistent registers provide the base and offset of a tableau atom name. -/
structure UpdateNameLanes (R : Type) where
  base : R
  offset : R

namespace UpdateNameLanes

variable {R : Type} (lanes : UpdateNameLanes R)

/-- Register distinctness for emitting one literal. -/
abbrev Disjoint (index scratch : R) : Prop := [lanes.base, lanes.offset, index, scratch].Nodup

/-- The numeric atom name carried by the two registers. -/
def name (values : R → Nat) : Nat := values lanes.base + values lanes.offset

/-- Prepend the signed literal and its clause frame. -/
abbrev fragment (index scratch : R) (positive : Bool) : Fragment R :=
  emitOffsetLiteral lanes.base lanes.offset index scratch positive

/-- The exact cost of emitting this literal. -/
def time (values : R → Nat) : Nat := offsetLiteralTime (values lanes.base) (values lanes.offset)

theorem time_polynomiallyBounded {values : Nat → R → Nat}
    (hValues : ∀ r, PolynomiallyBounded (fun n ↦ values n r)) :
    PolynomiallyBounded (fun n ↦ lanes.time (values n)) :=
  offsetLiteralTime_polynomiallyBounded (hValues lanes.base) (hValues lanes.offset)

theorem runsOutput_fragment [DecidableEq R] (index scratch : R) (positive : Bool)
    (x : BinaryWord) (values : R → Nat) (suffix : BinaryWord)
    (hLanes : lanes.Disjoint index scratch)
    (hIndex : values index = 0) (hScratch : values scratch = 0) :
    (lanes.fragment index scratch positive).RunsOutput x (lanes.time values) values values suffix
      (true :: (CNFCode.encodeLiteral
        (if positive then .pos (lanes.name values) else .neg (lanes.name values)) ++ suffix)) :=
  run_emitOffsetLiteral lanes.base lanes.offset index scratch positive x
    (⟨none, values, none, suffix⟩ : Config R Unit) hLanes hIndex hScratch rfl

end UpdateNameLanes

/-- The old state, head position, and scanned symbol shared by the three clauses. -/
structure UpdateGuardLanes (R : Type) where
  state : UpdateNameLanes R
  head : UpdateNameLanes R
  read : UpdateNameLanes R

namespace UpdateGuardLanes

variable {R : Type} (guards : UpdateGuardLanes R)

/-- Per-literal distinctness permits different names to share operands. -/
structure Disjoint (index scratch : R) : Prop where
  state : guards.state.Disjoint index scratch
  head : guards.head.Disjoint index scratch
  read : guards.read.Disjoint index scratch

/-- A clause negating the shared guard and asserting the given conclusion. -/
def clause (conclusion : UpdateNameLanes R) (values : R → Nat) : CNF.Clause Nat :=
  [.neg (guards.state.name values), .neg (guards.head.name values),
    .neg (guards.read.name values), .pos (conclusion.name values)]

/-- Emit a single guarded clause in reverse order, including its formula frame. -/
def fragment (conclusion : UpdateNameLanes R) (index scratch : R) : Fragment R :=
  let last := conclusion.fragment index scratch true
  let read := guards.read.fragment index scratch false
  let head := guards.head.fragment index scratch false
  let state := guards.state.fragment index scratch false
  (((((emitBit false).seq last).seq read).seq head).seq state).seq (emitBit true)

/-- The exact cost of one guarded clause, including its terminator and frame. -/
def time (conclusion : UpdateNameLanes R) (values : R → Nat) : Nat :=
  1 + conclusion.time values + guards.read.time values + guards.head.time values +
    guards.state.time values + 1

theorem time_polynomiallyBounded (conclusion : UpdateNameLanes R) {values : Nat → R → Nat}
    (hValues : ∀ r, PolynomiallyBounded (fun n ↦ values n r)) :
    PolynomiallyBounded (fun n ↦ guards.time conclusion (values n)) := by
  have hConclusion := conclusion.time_polynomiallyBounded hValues
  have hRead := guards.read.time_polynomiallyBounded hValues
  have hHead := guards.head.time_polynomiallyBounded hValues
  have hState := guards.state.time_polynomiallyBounded hValues
  exact (((((PolynomiallyBounded.const 1).add hConclusion).add hRead).add hHead).add hState).add
    (PolynomiallyBounded.const 1)

private theorem runsOutput_bit [DecidableEq R] (bit : Bool) (x : BinaryWord) (values : R → Nat)
    (suffix : BinaryWord) : (emitBit bit).RunsOutput x 1 values values suffix (bit :: suffix) :=
  run_emitBit bit x (⟨none, values, none, suffix⟩ : Config R Unit) rfl

/-- The guarded clause is prepended exactly, and every lane retains its value. -/
theorem runsOutput_fragment [DecidableEq R] (conclusion : UpdateNameLanes R)
    (index scratch : R) (x : BinaryWord) (values : R → Nat) (suffix : BinaryWord)
    (hGuards : guards.Disjoint index scratch) (hConclusion : conclusion.Disjoint index scratch)
    (hIndex : values index = 0) (hScratch : values scratch = 0) :
    (guards.fragment conclusion index scratch).RunsOutput x (guards.time conclusion values)
      values values suffix (true :: (CNFCode.encodeClause (guards.clause conclusion values) ++
        suffix)) := by
  have hEnd := runsOutput_bit false x values suffix
  have hLast := hEnd.seq
    (conclusion.runsOutput_fragment index scratch true x values _ hConclusion hIndex hScratch)
  have hRead := hLast.seq
    (guards.read.runsOutput_fragment index scratch false x values _ hGuards.read hIndex hScratch)
  have hHead := hRead.seq
    (guards.head.runsOutput_fragment index scratch false x values _ hGuards.head hIndex hScratch)
  have hState := hHead.seq
    (guards.state.runsOutput_fragment index scratch false x values _ hGuards.state hIndex hScratch)
  have hRun := hState.seq (runsOutput_bit true x values _)
  simpa only [fragment, time, clause, ite_true, Bool.false_eq_true, ite_false,
    CNFCode.encodeClause_cons, CNFCode.encodeClause_nil, List.cons_append, List.append_assoc,
    List.singleton_append, List.nil_append] using hRun

end UpdateGuardLanes

/-- Operands for the three implications of one tableau transition. -/
structure UpdateClauseLanes (R : Type) where
  guards : UpdateGuardLanes R
  nextState : UpdateNameLanes R
  nextHead : UpdateNameLanes R
  written : UpdateNameLanes R
  index : R
  scratch : R

namespace UpdateClauseLanes

variable {R : Type} (lanes : UpdateClauseLanes R)

/-- Each of the six atom names has distinct operands and temporary registers. -/
structure Disjoint : Prop where
  guards : lanes.guards.Disjoint lanes.index lanes.scratch
  nextState : lanes.nextState.Disjoint lanes.index lanes.scratch
  nextHead : lanes.nextHead.Disjoint lanes.index lanes.scratch
  written : lanes.written.Disjoint lanes.index lanes.scratch

/-- The three implications in the tableau's clause order. -/
def formula (values : R → Nat) : CNF.Formula Nat :=
  [lanes.guards.clause lanes.nextState values, lanes.guards.clause lanes.nextHead values,
    lanes.guards.clause lanes.written values]

/-- Emit the written-symbol, head, and state clauses in reverse order. -/
def fragment : Fragment R :=
  let written := lanes.guards.fragment lanes.written lanes.index lanes.scratch
  let head := lanes.guards.fragment lanes.nextHead lanes.index lanes.scratch
  let state := lanes.guards.fragment lanes.nextState lanes.index lanes.scratch
  (written.seq head).seq state

/-- The exact cost of the three clauses. -/
def time (values : R → Nat) : Nat :=
  lanes.guards.time lanes.written values + lanes.guards.time lanes.nextHead values +
    lanes.guards.time lanes.nextState values

theorem time_polynomiallyBounded {values : Nat → R → Nat}
    (hValues : ∀ r, PolynomiallyBounded (fun n ↦ values n r)) :
    PolynomiallyBounded (fun n ↦ lanes.time (values n)) :=
  ((lanes.guards.time_polynomiallyBounded lanes.written hValues).add
    (lanes.guards.time_polynomiallyBounded lanes.nextHead hValues)).add
      (lanes.guards.time_polynomiallyBounded lanes.nextState hValues)

/-- The fragment prepends the three framed clauses and restores all registers. -/
theorem runsOutput_fragment [DecidableEq R] (x : BinaryWord) (values : R → Nat)
    (suffix : BinaryWord)
    (hLanes : lanes.Disjoint) (hIndex : values lanes.index = 0)
    (hScratch : values lanes.scratch = 0) :
    lanes.fragment.RunsOutput x (lanes.time values) values values suffix
      ((lanes.formula values).reverse.foldl
        (fun out clause ↦ true :: (CNFCode.encodeClause clause ++ out)) suffix) := by
  have hWritten := lanes.guards.runsOutput_fragment lanes.written lanes.index lanes.scratch
    x values suffix hLanes.guards hLanes.written hIndex hScratch
  have hHead := hWritten.seq (lanes.guards.runsOutput_fragment lanes.nextHead
    lanes.index lanes.scratch x values _ hLanes.guards hLanes.nextHead hIndex hScratch)
  exact hHead.seq (lanes.guards.runsOutput_fragment lanes.nextState
    lanes.index lanes.scratch x values _ hLanes.guards hLanes.nextState hIndex hScratch)

/-- The six carried names agree with the atoms of the indexed transition. -/
structure Names (values : R → Nat) {qCount symbolCount width : Nat}
    (rule : Tableau.Rule (Fin qCount) (Fin symbolCount) width)
    (t : Nat) (q : Fin qCount) (i : Fin width) (a : Fin symbolCount) : Prop where
  state : lanes.guards.state.name values =
    indexedAtomName (width := width) (symbolCount := symbolCount) (.state t q)
  head : lanes.guards.head.name values =
    indexedAtomName (qCount := qCount) (symbolCount := symbolCount) (.head t i)
  read : lanes.guards.read.name values = indexedAtomName (qCount := qCount) (.cell t i a)
  nextState : lanes.nextState.name values =
    indexedAtomName (width := width) (symbolCount := symbolCount) (.state (t + 1) (rule q i a).1)
  nextHead : lanes.nextHead.name values =
    indexedAtomName (qCount := qCount) (symbolCount := symbolCount) (.head (t + 1) (rule q i a).2.1)
  written : lanes.written.name values =
    indexedAtomName (qCount := qCount) (.cell (t + 1) i (rule q i a).2.2)

/-- The fragment's formula agrees with the indexed tableau's local update formula. -/
theorem formula_eq_localUpdate (values : R → Nat) {qCount symbolCount width : Nat}
    (rule : Tableau.Rule (Fin qCount) (Fin symbolCount) width)
    (t : Nat) (q : Fin qCount) (i : Fin width) (a : Fin symbolCount)
    (hNames : lanes.Names values rule t q i a) :
    lanes.formula values = CNF.mapAtoms indexedAtomName (Tableau.localUpdate rule t q i a) := by
  simp [formula, UpdateGuardLanes.clause, Tableau.localUpdate, CNF.guard, CNF.mapAtoms,
    CNF.Literal.complement, CNF.Literal.map, hNames.state, hNames.head, hNames.read,
    hNames.nextState, hNames.nextHead, hNames.written]

/-- Emit exactly the three named local-update clauses of the indexed rule. -/
theorem runsOutput_localUpdate [DecidableEq R] (x : BinaryWord) (values : R → Nat)
    (suffix : BinaryWord) {qCount symbolCount width : Nat}
    (rule : Tableau.Rule (Fin qCount) (Fin symbolCount) width)
    (t : Nat) (q : Fin qCount) (i : Fin width) (a : Fin symbolCount)
    (hNames : lanes.Names values rule t q i a) (hLanes : lanes.Disjoint)
    (hIndex : values lanes.index = 0) (hScratch : values lanes.scratch = 0) :
    lanes.fragment.RunsOutput x (lanes.time values) values values suffix
      ((CNF.mapAtoms indexedAtomName (Tableau.localUpdate rule t q i a)).reverse.foldl
        (fun out clause ↦ true :: (CNFCode.encodeClause clause ++ out)) suffix) := by
  rw [← lanes.formula_eq_localUpdate values rule t q i a hNames]
  exact lanes.runsOutput_fragment x values suffix hLanes hIndex hScratch

end UpdateClauseLanes

end PvsNP.CookLevin
