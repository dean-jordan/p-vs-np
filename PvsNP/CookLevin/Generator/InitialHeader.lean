module

public import PvsNP.CookLevin.Generator.InputCell
public import PvsNP.TuringMachine.Registers.OutputRuns

/-! # Initial head and state constraints -/

@[expose] public section

namespace PvsNP.CookLevin

open RegisterMachine Fragment

variable {R : Type}

/-- Emit the head clause and then the state clause in chronological order. -/
abbrev initialHeaderFragment (offset zero literal scratch : R) (states initial : Nat) :
    Fragment R :=
  (emitFixedUnitClause offset literal scratch states).seq
    (emitFixedUnitClause zero literal scratch initial)

/-- The two framed singleton clauses are prepended in their formula order. -/
def initialHeaderOutput (states initial offset : Nat) (suffix : BinaryWord) : BinaryWord :=
  let head := true :: (CNFCode.encodeClause [.pos (states + offset)] ++ suffix)
  true :: (CNFCode.encodeClause [.pos initial] ++ head)

def initialHeaderTime (states initial offset : Nat) : Nat :=
  fixedUnitClauseTime offset states + fixedUnitClauseTime 0 initial

theorem initialHeaderTime_polynomiallyBounded (states initial : Nat) {offset : Nat → Nat}
    (hOffset : PolynomiallyBounded offset) :
    PolynomiallyBounded (fun n ↦ initialHeaderTime states initial (offset n)) := by
  let lit := PolynomiallyBounded.const
  exact ((((lit 7).mul hOffset).add (lit (3 * states))).add (lit 8)).add
    (lit (fixedUnitClauseTime 0 initial))

/-- Both unit clauses preserve the entry valuation. -/
theorem run_initialHeaderFragment [DecidableEq R] (offset zero literal scratch : R)
    (states initial : Nat) (x suffix : BinaryWord) (v : R → Nat)
    (hLanes : [offset, zero, literal, scratch].Nodup)
    (hZero : v zero = 0) (hLiteral : v literal = 0) (hScratch : v scratch = 0) :
    (initialHeaderFragment offset zero literal scratch states initial).RunsOutput x
      (initialHeaderTime states initial (v offset)) v v suffix
      (initialHeaderOutput states initial (v offset) suffix) := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or,
    not_false_eq_true, List.nodup_nil, and_true] at hLanes
  obtain ⟨⟨_, hol, hos⟩, ⟨hzl, hzs⟩, hls⟩ := hLanes
  let cfg : Config R Unit := ⟨none, v, none, suffix⟩
  have hHead : (emitFixedUnitClause offset literal scratch states).RunsOutput x
      (fixedUnitClauseTime (v offset) states) v v suffix
      (true :: (CNFCode.encodeClause [.pos (states + v offset)] ++ suffix)) := by
    simpa only [RunsOutput, cfg, Nat.add_comm] using
      run_emitFixedUnitClause offset literal scratch states x cfg hol hos hls hLiteral hScratch rfl
  let marked : Config R Unit :=
    ⟨none, v, none, true :: (CNFCode.encodeClause [.pos (states + v offset)] ++ suffix)⟩
  have hState : (emitFixedUnitClause zero literal scratch initial).RunsOutput x
      (fixedUnitClauseTime 0 initial) v v marked.output
      (initialHeaderOutput states initial (v offset) suffix) := by
    simpa only [RunsOutput, marked, initialHeaderOutput, hZero, Nat.zero_add] using
      run_emitFixedUnitClause zero literal scratch initial x marked hzl hzs hls
        hLiteral hScratch rfl
  exact hHead.seq hState

/-- The head and state names are those at time zero in the indexed formula. -/
theorem initialHeaderOutput_eq {states symbols certificates width : Nat}
    (table : FiniteTable states symbols certificates) (head : Fin width) (suffix : BinaryWord) :
    initialHeaderOutput states table.initial.val head.val suffix =
      ([[.pos (.state 0 table.initial)], [.pos (.head 0 head)]] :
        CNF.Formula (Tableau.Atom (Fin states) (Fin symbols) width)).reverse.foldl
        (fun out clause ↦ true ::
          (CNFCode.encodeClause (clause.map (CNF.Literal.map indexedAtomName)) ++ out)) suffix := by
  simp [initialHeaderOutput, indexedAtomName, Tableau.Atom.name, Tableau.Atom.time,
    Tableau.Atom.offset, CNF.Literal.map]

end PvsNP.CookLevin
