module

public import PvsNP.CookLevin.Generator.FiniteTable
public import PvsNP.CookLevin.Generator.PreparedField
public import PvsNP.TuringMachine.Registers.LessThan

/-! # Emitting one neighboring certificate blank constraint -/

@[expose] public section

namespace PvsNP.CookLevin

open RegisterMachine RegisterMachine.Fragment

/-- Persistent operands and work lanes of a certificate gap test. -/
inductive GapClauseLane where
  | left | right | lower | upper | atomBase | leftOffset | rightOffset
  | successor | index | leftCopy | rightCopy | scratch
  deriving DecidableEq

variable {R : Type} (lanes : GapClauseLane ↪ R)

local notation "I" => lanes GapClauseLane.left
local notation "J" => lanes GapClauseLane.right
local notation "Lo" => lanes GapClauseLane.lower
local notation "Hi" => lanes GapClauseLane.upper
local notation "Base" => lanes GapClauseLane.atomBase
local notation "LitI" => lanes GapClauseLane.leftOffset
local notation "LitJ" => lanes GapClauseLane.rightOffset
local notation "Succ" => lanes GapClauseLane.successor
local notation "Index" => lanes GapClauseLane.index
local notation "CopyI" => lanes GapClauseLane.leftCopy
local notation "CopyJ" => lanes GapClauseLane.rightCopy
local notation "Scratch" => lanes GapClauseLane.scratch

/-- The two-literal clause that excludes a certificate symbol after a blank. -/
def gapClause (v : R → Nat) : CNF.Clause Nat :=
  [.neg (v Base + v LitI), .pos (v Base + v LitJ)]

/-- The pair is adjacent and lies within the certificate interval. -/
abbrev gapQualifies (v : R → Nat) : Prop := v Lo ≤ v I ∧ v J = v I + 1 ∧ v J < v Hi

/-- The gap test contributes at most one clause. -/
def gapFormula (v : R → Nat) : CNF.Formula Nat :=
  if gapQualifies lanes v then [gapClause lanes v] else []

/-- Prepend the gap clause when the pair qualifies. -/
def gapClauseOutput (v : R → Nat) (suffix : BinaryWord) : BinaryWord :=
  if gapQualifies lanes v then true :: (CNFCode.encodeClause (gapClause lanes v) ++ suffix)
  else suffix

/-- The unconditional, framed two-literal clause. -/
abbrev gapRawFragment : Fragment R :=
  emitFramedOffsetClause Base Index Scratch [.neg LitI, .pos LitJ]

/-- The final comparison checks the exclusive upper bound. -/
abbrev gapUpperTest : Fragment R := ifLess J Hi CopyI CopyJ Scratch (gapRawFragment lanes) skip

/-- Skip the clause below the inclusive lower bound. -/
abbrev gapLowerTest : Fragment R := ifLess I Lo CopyI CopyJ Scratch skip (gapUpperTest lanes)

/-- Test adjacency before either interval bound. -/
abbrev gapTests : Fragment R :=
  ifOrdering Succ J CopyI CopyJ Scratch (· == .eq) (gapLowerTest lanes) skip

/-- Copy and increment the left coordinate, clearing the temporary at the shared exit. -/
abbrev gapFragment : Fragment R :=
  (((add I Succ Scratch).seq (incrementBy Succ 1)).seq (gapTests lanes)).seq (clear Succ)

/-- Exact cost of the unconditional clause. -/
def gapRawTime (v : R → Nat) : Nat :=
  1 + offsetLiteralTime (v Base) (v LitJ) + offsetLiteralTime (v Base) (v LitI) + 1

/-- Budget for all three tests and the possible clause emission. -/
def gapTestsTimeBound (v : R → Nat) (successor : Nat) : Nat :=
  ifEqualTime successor (v J) +
    (ifEqualTime (v I) (v Lo) + (ifEqualTime (v J) (v Hi) + gapRawTime lanes v))

/-- Budget for preparing the successor, running the tests, and clearing it. -/
def gapClauseTimeBound (v : R → Nat) : Nat :=
  (5 * v I + 2 + 1) + gapTestsTimeBound lanes v (v I + 1) + (v I + 1 + 1)

theorem gapClauseTimeBound_polynomiallyBounded {v : Nat → R → Nat}
    (hValues : ∀ r, PolynomiallyBounded (fun n ↦ v n r)) :
    PolynomiallyBounded (fun n ↦ gapClauseTimeBound lanes (v n)) := by
  let constant := PolynomiallyBounded.const
  have comparison {a b : Nat → Nat} (ha : PolynomiallyBounded a) (hb : PolynomiallyBounded b) :
      PolynomiallyBounded (fun n ↦ ifEqualTime (a n) (b n)) :=
    ((constant 6).mul (ha.add hb)).add (constant 6)
  have raw := (((constant 1).add (offsetLiteralTime_polynomiallyBounded
    (hValues Base) (hValues LitJ))).add (offsetLiteralTime_polynomiallyBounded
      (hValues Base) (hValues LitI))).add (constant 1)
  have successor := (hValues I).add (constant 1)
  have tests := (comparison successor (hValues J)).add
    ((comparison (hValues I) (hValues Lo)).add ((comparison (hValues J) (hValues Hi)).add raw))
  have prepare := (((constant 5).mul (hValues I)).add (constant 2)).add (constant 1)
  exact (prepare.add tests).add (successor.add (constant 1))

/-- The scratch for the comparisons and emission starts at zero. -/
def GapClauseScratchZero (v : R → Nat) : Prop :=
  v Index = 0 ∧ v CopyI = 0 ∧ v CopyJ = 0 ∧ v Scratch = 0

variable [DecidableEq R]

/-- Emit the unconditional gap clause in its exact unary and binary framing. -/
theorem runsOutput_gapRawFragment (x suffix : BinaryWord) (v : R → Nat)
    (hIndex : v Index = 0) (hScratch : v Scratch = 0) :
    (gapRawFragment lanes).RunsOutput x (gapRawTime lanes v) v v suffix
      (true :: (CNFCode.encodeClause (gapClause lanes v) ++ suffix)) := by
  let literals : CNF.Clause R := [.neg LitI, .pos LitJ]
  have hDistinct : ∀ l ∈ literals, [Base, l.atom, Index, Scratch].Nodup := by
    intro l hl
    simp only [literals, List.mem_cons, List.mem_nil_iff, or_false] at hl
    rcases hl with rfl | rfl <;> simp [CNF.Literal.atom]
  exact run_emitFramedOffsetClause Base Index Scratch literals x
    (⟨none, v, none, suffix⟩ : Config R Unit) hDistinct hIndex hScratch rfl

private theorem runsOutput_gapTests (x suffix : BinaryWord) (v : R → Nat)
    (hSuccessor : v Succ = v I + 1) (hWork : GapClauseScratchZero lanes v) :
    ∃ cost ≤ gapTestsTimeBound lanes v (v Succ),
      (gapTests lanes).RunsOutput x cost v v suffix (gapClauseOutput lanes v suffix) := by
  obtain ⟨hIndex, hCopyI, hCopyJ, hScratch⟩ := hWork
  let rawOutput := true :: (CNFCode.encodeClause (gapClause lanes v) ++ suffix)
  let upperOutput := if v J < v Hi then rawOutput else suffix
  let lowerOutput := if v I < v Lo then suffix else upperOutput
  have hUpper : ∃ cost ≤ ifEqualTime (v J) (v Hi) + gapRawTime lanes v,
      (gapUpperTest lanes).RunsOutput x cost v v suffix upperOutput := by
    apply runsOutput_ifLess x v v suffix upperOutput (gapRawTime lanes v)
      (by simp) (by simp) hCopyI hCopyJ hScratch
    · intro h
      refine ⟨_, Nat.le_refl _, ?_⟩
      simpa only [upperOutput, ite_eq_left h, rawOutput] using
        runsOutput_gapRawFragment lanes x suffix v hIndex hScratch
    · intro h
      refine ⟨0, Nat.zero_le _, ?_⟩
      simpa only [upperOutput, ite_eq_right h] using runsOutput_skip x v suffix
  have hLower : ∃ cost ≤ ifEqualTime (v I) (v Lo) +
      (ifEqualTime (v J) (v Hi) + gapRawTime lanes v),
      (gapLowerTest lanes).RunsOutput x cost v v suffix lowerOutput := by
    apply runsOutput_ifLess x v v suffix lowerOutput
      (ifEqualTime (v J) (v Hi) + gapRawTime lanes v) (by simp) (by simp) hCopyI hCopyJ hScratch
    · intro h
      refine ⟨0, Nat.zero_le _, ?_⟩
      simpa only [lowerOutput, ite_eq_left h] using runsOutput_skip x v suffix
    · intro h
      simpa only [lowerOutput, ite_eq_right h] using hUpper
  apply runsOutput_ifOrdering (· == .eq) x v v suffix (gapClauseOutput lanes v suffix)
    (ifEqualTime (v I) (v Lo) + (ifEqualTime (v J) (v Hi) + gapRawTime lanes v))
    (by simp) (by simp) hCopyI hCopyJ hScratch
  · intro h
    have hEq : v Succ = v J := by simpa only [beq_iff_eq, Nat.compare_eq_eq] using h
    have hAdjacent := hEq.symm.trans hSuccessor
    have hOutput : lowerOutput = gapClauseOutput lanes v suffix := by
      by_cases hLt : v I < v Lo
      · simp [lowerOutput, gapClauseOutput, gapQualifies, hLt, Nat.not_le.mpr hLt]
      · simp [lowerOutput, upperOutput, rawOutput, gapClauseOutput, gapQualifies, hLt,
          Nat.le_of_not_gt hLt, hAdjacent]
    simpa only [hOutput] using hLower
  · intro h
    have hNotAdjacent : v J ≠ v I + 1 := fun hEq ↦
      h (beq_iff_eq.mpr (Nat.compare_eq_eq.mpr (hSuccessor.trans hEq.symm)))
    refine ⟨0, Nat.zero_le _, ?_⟩
    simpa [gapClauseOutput, gapQualifies, hNotAdjacent] using runsOutput_skip x v suffix

private theorem runsValues_gapPrepare (x : BinaryWord) (v : R → Nat)
    (hSuccessor : v Succ = 0) (hScratch : v Scratch = 0) :
    ((add I Succ Scratch).seq (incrementBy Succ 1)).RunsValues x (5 * v I + 2 + 1)
      v (setValue Succ (v I + 1) v) := by
  let copied := setValue Succ (v I) v
  have hCopy : (add I Succ Scratch).RunsValues x (5 * v I + 2) v copied := by
    simpa only [hSuccessor, Nat.zero_add, copied] using
      runsValues_add I Succ Scratch x v (by simp) (by simp) (by simp) hScratch
  have hIncrement := runsValues_incrementBy Succ 1 x copied
  simpa only [copied, setValue_same, setValue_replace] using hCopy.seq hIncrement

/-- Emit the gap constraint exactly on adjacent pairs inside the interval. -/
theorem runsOutput_gapFragment (x suffix : BinaryWord) (v : R → Nat)
    (hSuccessor : v Succ = 0) (hWork : GapClauseScratchZero lanes v) :
    ∃ cost ≤ gapClauseTimeBound lanes v,
      (gapFragment lanes).RunsOutput x cost v v suffix (gapClauseOutput lanes v suffix) := by
  let prepared := setValue Succ (v I + 1) v
  have hPrepare := runsValues_gapPrepare lanes x v hSuccessor hWork.2.2.2
  have hSuccessorValue : prepared Succ = v I + 1 := setValue_same ..
  have hPreparedI : prepared I = v I := setValue_other (by simp) ..
  have hPreparedWork : GapClauseScratchZero lanes prepared := by
    simpa [GapClauseScratchZero, prepared, setValue] using hWork
  obtain ⟨testCost, hTestCost, hTest⟩ := runsOutput_gapTests lanes x suffix prepared
    (hSuccessorValue.trans (congrArg (· + 1) hPreparedI.symm)) hPreparedWork
  have hTestBound : testCost ≤ gapTestsTimeBound lanes v (v I + 1) := by
    simpa [gapTestsTimeBound, gapRawTime, prepared, setValue] using hTestCost
  have hOutput : gapClauseOutput lanes prepared suffix = gapClauseOutput lanes v suffix := by
    simp [gapClauseOutput, gapQualifies, gapClause, prepared, setValue]
  rw [hOutput] at hTest
  have hClear := runsValues_clear Succ x prepared
  have hRestore : setValue Succ 0 prepared = v := by
    rw [show prepared = setValue Succ (v I + 1) v from rfl, setValue_replace,
      ← hSuccessor, setValue_current]
  rw [hSuccessorValue, hRestore] at hClear
  refine ⟨(5 * v I + 2 + 1) + testCost + (v I + 1 + 1), ?_, ?_⟩
  · unfold gapClauseTimeBound
    omega
  · exact ((hPrepare.withOutput suffix).seq hTest).seq (hClear.withOutput _)

omit [DecidableEq R] in
/-- The register condition and atom names agree with the indexed initial gap formula. -/
theorem gapFormula_eq_initialGap {qCount symbolCount certificateCount width : Nat}
    (table : FiniteTable qCount symbolCount certificateCount) (x : BinaryWord)
    (capacity offset : Nat) (i j : Fin width) (v : R → Nat)
    (hI : v I = i.val) (hJ : v J = j.val)
    (hLower : v Lo = offset + x.length + 1) (hUpper : v Hi = offset + x.length + 1 + capacity)
    (hBase : v Base = qCount + width)
    (hLitI : v LitI = i.val * symbolCount + table.blank.val)
    (hLitJ : v LitJ = j.val * symbolCount + table.blank.val) :
    gapFormula lanes v = CNF.mapAtoms indexedAtomName (table.initialGap x capacity offset i j) := by
  simp only [gapFormula, gapQualifies, FiniteTable.initialGap, hI, hJ, hLower, hUpper]
  split
  · simp [gapClause, CNF.mapAtoms, CNF.Literal.map, indexedAtomName, Tableau.Atom.name,
      Tableau.Atom.time, Tableau.Atom.offset, hBase, hLitI, hLitJ]
  · rfl

omit [DecidableEq R] in
theorem gapClauseOutput_eq (v : R → Nat) (suffix : BinaryWord) :
    gapClauseOutput lanes v suffix = (gapFormula lanes v).reverse.foldl
      (fun out clause ↦ true :: (CNFCode.encodeClause clause ++ out)) suffix := by
  unfold gapClauseOutput gapFormula
  split <;> rfl

/-- Run the concrete leaf against the indexed `initialGap` specification. -/
theorem runsOutput_initialGap {qCount symbolCount certificateCount width : Nat}
    (table : FiniteTable qCount symbolCount certificateCount) (x suffix : BinaryWord)
    (capacity offset : Nat) (i j : Fin width) (v : R → Nat)
    (hI : v I = i.val) (hJ : v J = j.val)
    (hLower : v Lo = offset + x.length + 1) (hUpper : v Hi = offset + x.length + 1 + capacity)
    (hBase : v Base = qCount + width)
    (hLitI : v LitI = i.val * symbolCount + table.blank.val)
    (hLitJ : v LitJ = j.val * symbolCount + table.blank.val)
    (hSuccessor : v Succ = 0) (hWork : GapClauseScratchZero lanes v) :
    ∃ cost ≤ gapClauseTimeBound lanes v,
      (gapFragment lanes).RunsOutput x cost v v suffix
        ((CNF.mapAtoms indexedAtomName (table.initialGap x capacity offset i j)).reverse.foldl
          (fun out clause ↦ true :: (CNFCode.encodeClause clause ++ out)) suffix) := by
  rw [← gapFormula_eq_initialGap lanes table x capacity offset i j v
    hI hJ hLower hUpper hBase hLitI hLitJ, ← gapClauseOutput_eq]
  exact runsOutput_gapFragment lanes x suffix v hSuccessor hWork

end PvsNP.CookLevin
