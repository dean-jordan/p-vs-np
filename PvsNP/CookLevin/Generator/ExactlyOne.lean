module

public import PvsNP.CookLevin.Generator.FrameNames
public import PvsNP.CookLevin.Generator.Traversal
public import PvsNP.TuringMachine.Registers.Conditional
public import PvsNP.TuringMachine.Registers.OutputRuns

/-! # A finite program for an exactly-one field

The field names form the consecutive interval starting at `base`. The
program emits the negative ordered pairs by descending loops, skipping equal
indices, and then emits the positive clause in reverse literal order.
-/

@[expose] public section

namespace PvsNP.CookLevin

open RegisterMachine Fragment

/-- Registers used by one exactly-one block. -/
inductive ExactlyOneLane where
  | base | count | left | right | index | additionScratch | leftCopy | rightCopy | comparisonScratch
  deriving DecidableEq

variable {R : Type} (lanes : ExactlyOneLane ↪ R)

local notation "B" => lanes ExactlyOneLane.base
local notation "N" => lanes ExactlyOneLane.count
local notation "I" => lanes ExactlyOneLane.left
local notation "J" => lanes ExactlyOneLane.right
local notation "Z" => lanes ExactlyOneLane.index
local notation "A" => lanes ExactlyOneLane.additionScratch
local notation "P" => lanes ExactlyOneLane.leftCopy
local notation "Q" => lanes ExactlyOneLane.rightCopy
local notation "S" => lanes ExactlyOneLane.comparisonScratch

/-- The two negative literals in one clause, emitted rightmost first. -/
abbrev negativePair : Fragment R :=
  emitFramedOffsetClause B Z A [.neg I, .neg J]

/-- Skip a negative pair when the two indices coincide. -/
abbrev pairIfDistinct : Fragment R := ifEqual I J P Q S skip (negativePair lanes)

/-- Initialize a fresh right counter and emit all pairs for the current left index. -/
abbrev pairsForLeft : Fragment R := (add N J A).seq (countdown J (pairIfDistinct lanes))

/-- Enumerate the negative clauses. -/
abbrev exactlyOnePairs : Fragment R := (add N I A).seq (countdown I (pairsForLeft lanes))

/-- Emit the positive clause after the negative clauses have been generated. -/
abbrev exactlyOnePositive : Fragment R :=
  ((emitBit false).seq ((add N I A).seq (countdown I (emitOffsetLiteral B I Z A true)))).seq
    (emitBit true)

/-- A complete exactly-one block, preserving its input registers and all scratch lanes. -/
abbrev exactlyOneField : Fragment R := (exactlyOnePairs lanes).seq (exactlyOnePositive lanes)

/-- Exact output update for one (possibly diagonal) negative pair. -/
def negativePairOutput (base left : Nat) (suffix : BinaryWord) (right : Nat) : BinaryWord :=
  if right = left then suffix
  else true :: (CNFCode.encodeClause [.neg (base + left), .neg (base + right)] ++ suffix)

/-- Output model for all the pairs of a fixed left index. -/
def pairsForLeftOutput (base count : Nat) (suffix : BinaryWord) (left : Nat) : BinaryWord :=
  (List.range count).reverse.foldl (negativePairOutput base left) suffix

/-- Prepend the positive literal for a field index. -/
def positiveLiteralOutput (base : Nat) (suffix : BinaryWord) (i : Nat) : BinaryWord :=
  true :: (CNFCode.encodeLiteral (.pos (base + i)) ++ suffix)

/-- Output model for the entire field, in the order used by the emitting program. -/
def exactlyOneFieldOutput (base count : Nat) (suffix : BinaryWord) : BinaryWord :=
  let negative := (List.range count).reverse.foldl (pairsForLeftOutput base count) suffix
  let positive := (List.range count).reverse.foldl (positiveLiteralOutput base) (false :: negative)
  true :: positive

/-- Uniform budget for comparing and potentially emitting one pair. -/
def pairTimeBound (base count : Nat) : Nat :=
  ifEqualTime count count + (1 + offsetLiteralTime base count + offsetLiteralTime base count + 1)

/-- Uniform budget for initializing and traversing the right counter. -/
def pairsForLeftTimeBound (base count : Nat) : Nat :=
  (5 * count + 2) + (count * (pairTimeBound base count + 1) + 1)

/-- Budget for the two passes over the ordered pairs and the positive clause. -/
def exactlyOneFieldTimeBound (base count : Nat) : Nat :=
  (5 * count + 2 + (count * (pairsForLeftTimeBound base count + 1) + 1)) +
    (1 + (5 * count + 2) + (count * (offsetLiteralTime base count + 1) + 1) + 1)

/-- All of the scratch lanes are available for the next clause. -/
def ExactlyOneScratchZero (values : R → Nat) : Prop :=
  values Z = 0 ∧ values A = 0 ∧ values P = 0 ∧ values Q = 0 ∧ values S = 0

private theorem separate {a b : ExactlyOneLane} (h : a ≠ b) : lanes a ≠ lanes b :=
  fun heq ↦ h (lanes.injective heq)

variable [DecidableEq R]

private theorem bitRun (x : BinaryWord) (bit : Bool) (values : R → Nat) (suffix : BinaryWord) :
    (emitBit bit).RunsOutput x 1 values values suffix (bit :: suffix) :=
  run_emitBit bit x (⟨none, values, none, suffix⟩ : Config R Unit) rfl

private theorem pairRun (x suffix : BinaryWord) (v : R → Nat) (bound : Nat)
    (hWork : ExactlyOneScratchZero lanes v) (hi : v I ≤ bound) (hj : v J ≤ bound) :
    ∃ cost ≤ pairTimeBound (v B) bound,
      (pairIfDistinct lanes).RunsOutput x cost v v suffix
        (negativePairOutput (v B) (v I) suffix (v J)) := by
  obtain ⟨hIndex, hAdd, hLeft, hRight, hCompare⟩ := hWork
  let cfg : Config R Unit := ⟨none, v, none, suffix⟩
  have hIL := separate lanes (by decide : ExactlyOneLane.left ≠ .leftCopy)
  have hIS := separate lanes (by decide : ExactlyOneLane.left ≠ .comparisonScratch)
  have hJL := separate lanes (by decide : ExactlyOneLane.right ≠ .leftCopy)
  have hJR := separate lanes (by decide : ExactlyOneLane.right ≠ .rightCopy)
  have hJS := separate lanes (by decide : ExactlyOneLane.right ≠ .comparisonScratch)
  have hLR := separate lanes (by decide : ExactlyOneLane.leftCopy ≠ .rightCopy)
  have hLS := separate lanes (by decide : ExactlyOneLane.leftCopy ≠ .comparisonScratch)
  have hRS := separate lanes (by decide : ExactlyOneLane.rightCopy ≠ .comparisonScratch)
  by_cases hEq : v I = v J
  · refine ⟨ifEqualTime (v I) (v J) + 0, ?_, ?_⟩
    · unfold pairTimeBound ifEqualTime
      omega
    · have hRun := run_ifEqual_eq (equal := (skip : Fragment R))
        (different := negativePair lanes) x hIL hIS hJL hJR hJS hLR hLS hRS cfg
        hLeft hRight hCompare hEq (runsOutput_skip x v suffix) rfl
      simpa only [RunsOutput, cfg, pairIfDistinct, negativePairOutput, ite_eq_left hEq.symm] using
        hRun
  · let literals : CNF.Clause R := [.neg I, .neg J]
    have hLanes (l : CNF.Literal R) (hl : l ∈ literals) : [B, l.atom, Z, A].Nodup := by
      simp only [literals, List.mem_cons, List.mem_nil_iff, or_false] at hl
      rcases hl with rfl | rfl <;> simp [CNF.Literal.atom]
    have hRun := run_emitFramedOffsetClause B Z A literals x cfg hLanes hIndex hAdd rfl
    have hBranch := run_ifEqual_ne (equal := (skip : Fragment R))
      (different := negativePair lanes) x hIL hIS hJL hJR hJS hLR hLS hRS cfg
      hLeft hRight hCompare hEq hRun rfl
    refine ⟨ifEqualTime (v I) (v J) + (offsetClauseTime (v B) v literals + 1), ?_, ?_⟩
    · have hOffset (l : CNF.Literal R) (hl : l ∈ literals) : v l.atom ≤ bound := by
        simp only [literals, List.mem_cons, List.mem_nil_iff, or_false] at hl
        rcases hl with rfl | rfl
        · exact hi
        · exact hj
      have hc := offsetClauseTime_le (v B) bound v literals hOffset
      simp only [literals, List.length_cons, List.length_nil] at hc
      simp only [literals]
      unfold pairTimeBound ifEqualTime
      omega
    · simpa only [RunsOutput, cfg, pairIfDistinct, literals, negativePairOutput,
        ite_eq_right (Ne.symm hEq), List.map_cons, List.map_nil, CNF.Literal.map] using hBranch

private theorem pairsForLeftRun (x suffix : BinaryWord) (v : R → Nat)
    (hWork : ExactlyOneScratchZero lanes v) (hi : v I ≤ v N) (hj : v J = 0) :
    ∃ cost ≤ pairsForLeftTimeBound (v B) (v N),
      (pairsForLeft lanes).RunsOutput x cost v v suffix
        (pairsForLeftOutput (v B) (v N) suffix (v I)) := by
  have hBody (j : Nat) (hBound : j < v N) (acc : BinaryWord) :
      ∃ ticks ≤ pairTimeBound (v B) (v N),
        (pairIfDistinct lanes).RunsOutput x ticks (setValue J j v) (setValue J j v) acc
          (negativePairOutput (v B) (v I) acc j) := by
    have hb : setValue J j v B = v B := by simp [setValue]
    have hI : setValue J j v I = v I := by simp [setValue]
    have hJ : setValue J j v J = j := setValue_same ..
    have hWork' : ExactlyOneScratchZero lanes (setValue J j v) := by
      simpa [ExactlyOneScratchZero, setValue] using hWork
    simpa only [hb, hI, hJ] using pairRun lanes x acc (setValue J j v) (v N) hWork'
      (by simpa only [hI] using hi) (by simpa only [hJ] using Nat.le_of_lt hBound)
  exact runsOutput_initializedCountdown N J A (pairIfDistinct lanes) x v
    (pairTimeBound (v B) (v N)) (negativePairOutput (v B) (v I))
    (separate lanes (by decide)) (separate lanes (by decide)) (separate lanes (by decide))
    hj hWork.2.1 hBody suffix

private theorem exactlyOnePairsRun (x suffix : BinaryWord) (v : R → Nat)
    (hWork : ExactlyOneScratchZero lanes v) (hi : v I = 0) (hj : v J = 0) :
    ∃ cost ≤ 5 * v N + 2 + (v N * (pairsForLeftTimeBound (v B) (v N) + 1) + 1),
      (exactlyOnePairs lanes).RunsOutput x cost v v suffix
        ((List.range (v N)).reverse.foldl (pairsForLeftOutput (v B) (v N)) suffix) := by
  have hBody (i : Nat) (hBound : i < v N) (acc : BinaryWord) :
      ∃ ticks ≤ pairsForLeftTimeBound (v B) (v N),
        (pairsForLeft lanes).RunsOutput x ticks (setValue I i v) (setValue I i v) acc
          (pairsForLeftOutput (v B) (v N) acc i) := by
    have hb : setValue I i v B = v B := by simp [setValue]
    have hn : setValue I i v N = v N := by simp [setValue]
    have hI : setValue I i v I = i := setValue_same ..
    have hJ : setValue I i v J = 0 := by simp [setValue, hj]
    have hWork' : ExactlyOneScratchZero lanes (setValue I i v) := by
      simpa [ExactlyOneScratchZero, setValue] using hWork
    have hi' : setValue I i v I ≤ setValue I i v N := by
      rw [hI, hn]
      exact Nat.le_of_lt hBound
    simpa only [hb, hn, hI] using pairsForLeftRun lanes x acc (setValue I i v) hWork' hi' hJ
  exact runsOutput_initializedCountdown N I A (pairsForLeft lanes) x v
    (pairsForLeftTimeBound (v B) (v N)) (pairsForLeftOutput (v B) (v N))
    (separate lanes (by decide)) (separate lanes (by decide)) (separate lanes (by decide))
    hi hWork.2.1 hBody suffix

private theorem exactlyOnePositiveRun (x suffix : BinaryWord) (v : R → Nat)
    (hWork : ExactlyOneScratchZero lanes v) (hi : v I = 0) :
    ∃ cost ≤ 1 + (5 * v N + 2) + (v N * (offsetLiteralTime (v B) (v N) + 1) + 1) + 1,
      (exactlyOnePositive lanes).RunsOutput x cost v v suffix
        (true :: (List.range (v N)).reverse.foldl (positiveLiteralOutput (v B))
          (false :: suffix)) := by
  let literal := emitOffsetLiteral B I Z A true
  have hBody (i : Nat) (hBound : i < v N) (acc : BinaryWord) :
      ∃ cost ≤ offsetLiteralTime (v B) (v N),
        literal.RunsOutput x cost (setValue I i v) (setValue I i v) acc
          (positiveLiteralOutput (v B) acc i) := by
    let cfg : Config R Unit := ⟨none, setValue I i v, none, acc⟩
    have hIndex : cfg.values Z = 0 := by simpa [cfg, setValue] using hWork.1
    have hScratch : cfg.values A = 0 := by simpa [cfg, setValue] using hWork.2.1
    have hb : cfg.values B = v B := by simp [cfg, setValue]
    have hI : cfg.values I = i := setValue_same ..
    have hRun := run_emitOffsetLiteral B I Z A true x cfg (by simp) hIndex hScratch rfl
    rw [hb, hI] at hRun
    refine ⟨offsetLiteralTime (v B) i, ?_, hRun⟩
    unfold offsetLiteralTime
    omega
  obtain ⟨ticks, hTicks, hRun⟩ := runsOutput_initializedCountdown N I A literal x v
    (offsetLiteralTime (v B) (v N)) (positiveLiteralOutput (v B))
    (separate lanes (by decide)) (separate lanes (by decide)) (separate lanes (by decide))
    hi hWork.2.1 hBody (false :: suffix)
  refine ⟨1 + ticks + 1, by omega, ?_⟩
  simpa only [exactlyOnePositive, literal] using
    ((bitRun (R := R) x false v suffix).seq hRun).seq (bitRun x true v _)

/-- Emit the whole field within the stated instruction budget and restore the valuation. -/
theorem run_exactlyOneField (x suffix : BinaryWord) (v : R → Nat)
    (hWork : ExactlyOneScratchZero lanes v) (hi : v I = 0) (hj : v J = 0) :
    ∃ cost ≤ exactlyOneFieldTimeBound (v B) (v N),
      (exactlyOneField lanes).RunsOutput x cost v v suffix
        (exactlyOneFieldOutput (v B) (v N) suffix) := by
  obtain ⟨pairCost, hPairs, hNegative⟩ := exactlyOnePairsRun lanes x suffix v hWork hi hj
  obtain ⟨positiveCost, hPositive, hRun⟩ := exactlyOnePositiveRun lanes x _ v hWork hi
  exact ⟨pairCost + positiveCost, Nat.add_le_add hPairs hPositive, hNegative.seq hRun⟩

omit [DecidableEq R] in
theorem exactlyOneFieldTimeBound_polynomiallyBounded {base count : Nat → Nat}
    (hb : PolynomiallyBounded base) (hn : PolynomiallyBounded count) :
    PolynomiallyBounded (fun n ↦ exactlyOneFieldTimeBound (base n) (count n)) := by
  let constant := PolynomiallyBounded.const
  have literal := offsetLiteralTime_polynomiallyBounded hb hn
  have compare := ((constant 6).mul (hn.add hn)).add (constant 6)
  have pair := compare.add ((((constant 1).add literal).add literal).add (constant 1))
  have copyCost := ((constant 5).mul hn).add (constant 2)
  have loop {body : Nat → Nat} (h : PolynomiallyBounded body) :
      PolynomiallyBounded (fun n ↦ count n * (body n + 1) + 1) :=
    (hn.mul (h.add (constant 1))).add (constant 1)
  exact (copyCost.add (loop (copyCost.add (loop pair)))).add
    ((((constant 1).add copyCost).add (loop literal)).add (constant 1))

theorem exactlyOneFieldTimeBound_mono {base larger count more : Nat}
    (hb : base ≤ larger) (hn : count ≤ more) :
    exactlyOneFieldTimeBound base count ≤ exactlyOneFieldTimeBound larger more := by
  have literal : offsetLiteralTime base count ≤ offsetLiteralTime larger more := by
    unfold offsetLiteralTime
    omega
  have pair : pairTimeBound base count ≤ pairTimeBound larger more := by
    unfold pairTimeBound ifEqualTime
    omega
  have copyCost : 5 * count + 2 ≤ 5 * more + 2 := by omega
  have loop {a b : Nat} (h : a ≤ b) : count * (a + 1) + 1 ≤ more * (b + 1) + 1 :=
    Nat.add_le_add_right (Nat.mul_le_mul hn (Nat.add_le_add_right h 1)) 1
  have inner : pairsForLeftTimeBound base count ≤ pairsForLeftTimeBound larger more :=
    Nat.add_le_add copyCost (loop pair)
  exact Nat.add_le_add (Nat.add_le_add copyCost (loop inner))
    (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_left copyCost 1) (loop literal)) 1)

private theorem finRange_values (n : Nat) :
    (List.finRange n).map (fun i : Fin n ↦ i.val) = List.range n := by
  apply List.ext_getElem
  · simp
  · simp

/-- Descending finite-index loops agree with numeric loops over the index values. -/
theorem foldFinDesc_values {σ : Type} (n : Nat) (step : σ → Nat → σ) (acc : σ) :
    Traversal.foldFinDesc n (fun s (i : Fin n) ↦ step s i.val) acc =
      (List.range n).reverse.foldl step acc := by
  rw [Traversal.foldFinDesc_eq, ← List.foldl_map, List.map_reverse, finRange_values]

private theorem positiveFold (base count : Nat) (suffix : BinaryWord) :
    (List.range count).reverse.foldl (positiveLiteralOutput base) (false :: suffix) =
      CNFCode.encodeClause ((List.finRange count).map fun i ↦ .pos (base + i.val)) ++ suffix := by
  let push (bits : BinaryWord) (bit : Bool) := bit :: bits
  let clause : CNF.Clause Nat := (List.finRange count).map fun i ↦ .pos (base + i.val)
  have hLiteral (bits : BinaryWord) (l : CNF.Literal Nat) :
      Serialization.emitLiteral push bits l = CNFCode.encodeLiteral l ++ bits := by
    rw [Serialization.emitLiteral_eq_foldl]
    change (CNFCode.encodeLiteral l).reverse.foldl (fun acc bit ↦ bit :: acc) bits = _
    rw [List.foldl_flip_cons_eq_append', List.reverse_reverse]
  have h := Serialization.emitClause_eq_foldl push suffix clause
  change _ = (CNFCode.encodeClause clause).reverse.foldl (fun bits bit ↦ bit :: bits) suffix at h
  rw [List.foldl_flip_cons_eq_append', List.reverse_reverse] at h
  have hClause : clause = (List.range count).map (fun i ↦ .pos (base + i)) := by
    simp only [clause, ← finRange_values, List.map_map, Function.comp_def]
  change _ = CNFCode.encodeClause clause ++ suffix
  rw [← h, Serialization.emitClause, hClause, ← List.map_reverse, List.foldl_map]
  unfold positiveLiteralOutput
  simp only [hLiteral, push]

/-- The loop output is exactly the reverse emission of the field's CNF clauses. -/
theorem exactlyOneFieldOutput_eq (base count : Nat) (suffix : BinaryWord) :
    exactlyOneFieldOutput base count suffix =
      (CNF.exactlyOne ((List.finRange count).map fun i ↦ base + i.val)).reverse.foldl
        (fun acc clause ↦ true :: (CNFCode.encodeClause clause ++ acc)) suffix := by
  let emit (acc : BinaryWord) (clause : CNF.Clause Nat) :=
    true :: (CNFCode.encodeClause clause ++ acc)
  have hNames : Function.Injective (fun i : Fin count ↦ base + i.val) :=
    fun _ _ h ↦ Fin.ext (Nat.add_left_cancel h)
  rw [← Traversal.foldExactlyOne_eq _ hNames emit suffix]
  have hInner (acc : BinaryWord) (i : Fin count) :
      Traversal.foldFinDesc count (fun acc (j : Fin count) ↦ if j = i then acc
        else emit acc [.neg (base + i.val), .neg (base + j.val)]) acc =
      pairsForLeftOutput base count acc i.val := by
    rw [pairsForLeftOutput, ← foldFinDesc_values]
    simp only [negativePairOutput, emit, Fin.ext_iff]
  simp only [exactlyOneFieldOutput, Traversal.foldExactlyOne, hInner, foldFinDesc_values,
    positiveFold, emit]

/-- Relate an exactly-one constraint to its numeric interval after naming the atoms. -/
theorem foldExactlyOne_named {α : Type} {count : Nat} (atom : Fin count → α) (name : α → Nat)
    (base : Nat) (h : ∀ i, name (atom i) = base + i.val) (suffix : BinaryWord) :
    Traversal.foldExactlyOne count atom
      (fun acc clause ↦ true :: (CNFCode.encodeClause (clause.map (CNF.Literal.map name)) ++ acc))
      suffix = exactlyOneFieldOutput base count suffix := by
  let number (i : Fin count) := base + i.val
  have hNumber : Function.Injective number := fun _ _ e ↦ Fin.ext (Nat.add_left_cancel e)
  rw [exactlyOneFieldOutput_eq, ← Traversal.foldExactlyOne_eq number hNumber]
  simp only [Traversal.foldExactlyOne, List.map_cons, List.map_nil, CNF.Literal.map,
    List.map_map, Function.comp_def, h, number]

end PvsNP.CookLevin
