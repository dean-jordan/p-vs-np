module

public import PvsNP.CookLevin.Generator.GapClause
public import PvsNP.TuringMachine.Registers.Affine

/-! # Enumerating the certificate gap constraints -/

@[expose] public section

namespace PvsNP.CookLevin

open RegisterMachine Fragment

/-- The two nested countdowns share the window width and a multiplier. -/
inductive InitialGapLane where
  | width | multiplier | gap (lane : GapClauseLane)
  deriving DecidableEq

/-- The existing gap emitter and the walker use the same coordinate lanes. -/
def initialGapLanes {R : Type} (lanes : InitialGapLane ↪ R) : GapClauseLane ↪ R :=
  ⟨fun lane ↦ lanes (.gap lane), fun _ _ h ↦ InitialGapLane.gap.inj (lanes.injective h)⟩

@[simp] theorem initialGapLanes_apply {R : Type} (lanes : InitialGapLane ↪ R)
    (lane : GapClauseLane) : initialGapLanes lanes lane = lanes (.gap lane) := rfl

variable {R : Type} (lanes : InitialGapLane ↪ R)

local notation "G" => initialGapLanes lanes
local notation "W" => lanes InitialGapLane.width
local notation "M" => lanes InitialGapLane.multiplier
local notation "I" => lanes (InitialGapLane.gap GapClauseLane.left)
local notation "J" => lanes (InitialGapLane.gap GapClauseLane.right)
local notation "LI" => lanes (InitialGapLane.gap GapClauseLane.leftOffset)
local notation "LJ" => lanes (InitialGapLane.gap GapClauseLane.rightOffset)
local notation "LO" => lanes (InitialGapLane.gap GapClauseLane.lower)
local notation "HI" => lanes (InitialGapLane.gap GapClauseLane.upper)
local notation "B" => lanes (InitialGapLane.gap GapClauseLane.atomBase)
local notation "S" => lanes (InitialGapLane.gap GapClauseLane.scratch)

/-- The name arithmetic and gap test share a scratch register. -/
structure InitialGapsReady (v : R → Nat) : Prop where
  multiplier : v M = 0
  leftOffset : v LI = 0
  rightOffset : v LJ = 0
  successor : v (G .successor) = 0
  scratch : GapClauseScratchZero G v

/-- Prepare the two blank-cell offsets before testing and clearing them. -/
abbrev initialGapPairFragment (symbols blank : Nat) : Fragment R :=
  let left := accumulateAffine I LI M S symbols blank
  let right := accumulateAffine J LJ M S symbols blank
  ((left.seq right).seq (gapFragment G)).seq ((clear LJ).seq (clear LI))

/-- Descend through the possible right coordinates for one left coordinate. -/
abbrev initialGapsForLeft (symbols blank : Nat) : Fragment R :=
  (add W J S).seq (countdown J (initialGapPairFragment lanes symbols blank))

/-- Visit the ordered pairs of window positions in descending order. -/
abbrev initialGapsFragment (symbols blank : Nat) : Fragment R :=
  (add W I S).seq (countdown I (initialGapsForLeft lanes symbols blank))

/-- Output of the guarded pair test on numeric indices. -/
def initialGapPairOutput (symbols blank base lower upper i : Nat)
    (suffix : BinaryWord) (j : Nat) : BinaryWord :=
  if lower ≤ i ∧ j = i + 1 ∧ j < upper then
    true :: (CNFCode.encodeClause [.neg (base + (i * symbols + blank)),
      .pos (base + (j * symbols + blank))] ++ suffix)
  else suffix

/-- Output of the inner pair loop. -/
def initialGapsForLeftOutput (width symbols blank base lower upper : Nat)
    (suffix : BinaryWord) (i : Nat) : BinaryWord :=
  (List.range width).reverse.foldl (initialGapPairOutput symbols blank base lower upper i) suffix

/-- Output of the complete gap traversal. -/
def initialGapsOutput (width symbols blank base lower upper : Nat) (suffix : BinaryWord) :
    BinaryWord :=
  (List.range width).reverse.foldl
    (initialGapsForLeftOutput width symbols blank base lower upper) suffix

/-- A uniform budget for one pair, with both coordinates bounded by the width. -/
def initialGapPairTimeBound (width symbols blank base lower upper : Nat) : Nat :=
  let offset := symbols * width + blank
  let prep := affineTime symbols blank width
  let emit := 1 + offsetLiteralTime base offset + offsetLiteralTime base offset + 1
  let test := ifEqualTime (width + 1) width +
    (ifEqualTime width lower + (ifEqualTime width upper + emit))
  prep + prep + ((5 * width + 2 + 1) + test + (width + 1 + 1)) + (offset + 1 + (offset + 1))

/-- Budget for a copied counter and a bounded body at each position. -/
def initialGapLoopTimeBound (width body : Nat) : Nat :=
  (5 * width + 2) + (width * (body + 1) + 1)

/-- Bound initialization, both countdowns, and every gap test. -/
def initialGapsTimeBound (width symbols blank base lower upper : Nat) : Nat :=
  initialGapLoopTimeBound width
    (initialGapLoopTimeBound width (initialGapPairTimeBound width symbols blank base lower upper))

variable [DecidableEq R]

private theorem run_pair (symbols blank : Nat) (x suffix : BinaryWord) (v : R → Nat)
    (hReady : InitialGapsReady lanes v) (hi : v I ≤ v W) (hj : v J ≤ v W) :
    ∃ cost ≤ initialGapPairTimeBound (v W) symbols blank (v B) (v LO) (v HI),
      (initialGapPairFragment lanes symbols blank).RunsOutput x cost v v suffix
        (initialGapPairOutput symbols blank (v B) (v LO) (v HI) (v I) suffix (v J)) := by
  let li := symbols * v I + blank
  let lj := symbols * v J + blank
  let left := setValue LI li v
  let both := setValue LJ lj left
  have hs : v S = 0 := hReady.scratch.2.2.2
  have hLeft := runsValues_accumulateAffine I LI M S symbols blank x v (by simp)
    hReady.multiplier hs
  rw [hReady.leftOffset, Nat.zero_add] at hLeft
  have hRight := runsValues_accumulateAffine J LJ M S symbols blank x left (by simp)
    (by simpa [left, setValue] using hReady.multiplier)
    (by simpa [left, setValue] using hs)
  have hRightPos : left J = v J := by simp [left, setValue]
  have hRightOffset : left LJ = 0 := by simpa [left, setValue] using hReady.rightOffset
  rw [hRightPos, hRightOffset, Nat.zero_add] at hRight
  have hSucceeded : both (G .successor) = 0 := by
    simpa [both, left, setValue] using hReady.successor
  have hScratch : GapClauseScratchZero G both := by
    simpa [GapClauseScratchZero, both, left, setValue] using hReady.scratch
  obtain ⟨ticks, hTicks, hGap⟩ := runsOutput_gapFragment G x suffix both hSucceeded hScratch
  have hName : gapClauseOutput G both suffix =
      initialGapPairOutput symbols blank (v B) (v LO) (v HI) (v I) suffix (v J) := by
    simp [gapClauseOutput, gapQualifies, gapClause, initialGapPairOutput,
      both, left, li, lj, setValue, Nat.mul_comm symbols]
  rw [hName] at hGap
  have hClearJ := runsValues_clear LJ x both
  have hClearI := runsValues_clear LI x left
  have hBackJ : setValue LJ 0 both = left := by
    rw [show both = setValue LJ lj left from rfl, setValue_replace, ← hRightOffset,
      setValue_current]
  have hBackI : setValue LI 0 left = v := by
    rw [show left = setValue LI li v from rfl, setValue_replace, ← hReady.leftOffset,
      setValue_current]
  rw [show both LJ = lj from setValue_same .., hBackJ] at hClearJ
  rw [show left LI = li from setValue_same .., hBackI] at hClearI
  have hRun := ((((hLeft.seq hRight).withOutput suffix).seq hGap).seq
    ((hClearJ.seq hClearI).withOutput _))
  refine ⟨_, ?_, hRun⟩
  have hLeftTime := affineTime_mono symbols blank hi
  have hRightTime := affineTime_mono symbols blank hj
  have hLeftLit := Nat.mul_le_mul_left symbols hi
  have hRightLit := Nat.mul_le_mul_left symbols hj
  simp [gapClauseTimeBound, gapTestsTimeBound, gapRawTime, ifEqualTime, offsetLiteralTime,
    both, left, li, lj, setValue] at hTicks
  simp only [initialGapPairTimeBound, ifEqualTime, offsetLiteralTime, li, lj]
  omega

private theorem ready_after_coordinate (v : R → Nat) (n : Nat) (position : InitialGapLane)
    (hPosition : position = .gap .left ∨ position = .gap .right)
    (h : InitialGapsReady lanes v) : InitialGapsReady lanes (setValue (lanes position) n v) := by
  rcases hPosition with rfl | rfl <;>
    exact ⟨by simpa [setValue] using h.multiplier,
      by simpa [setValue] using h.leftOffset, by simpa [setValue] using h.rightOffset,
      by simpa [setValue] using h.successor,
      by simpa [GapClauseScratchZero, setValue] using h.scratch⟩

private theorem run_for_left (symbols blank : Nat) (x suffix : BinaryWord) (v : R → Nat)
    (hReady : InitialGapsReady lanes v) (hi : v I ≤ v W) (hj : v J = 0) :
    ∃ cost ≤ initialGapLoopTimeBound (v W)
          (initialGapPairTimeBound (v W) symbols blank (v B) (v LO) (v HI)),
      (initialGapsForLeft lanes symbols blank).RunsOutput x cost v v suffix
        (initialGapsForLeftOutput (v W) symbols blank (v B) (v LO) (v HI) suffix (v I)) := by
  have hBody (j : Nat) (hjBound : j < v W) (acc : BinaryWord) :
      ∃ cost ≤ initialGapPairTimeBound (v W) symbols blank (v B) (v LO) (v HI),
        (initialGapPairFragment lanes symbols blank).RunsOutput x cost
          (setValue J j v) (setValue J j v) acc
          (initialGapPairOutput symbols blank (v B) (v LO) (v HI) (v I) acc j) := by
    have hAt := ready_after_coordinate lanes v j (.gap .right) (Or.inr rfl) hReady
    have hLeft : setValue J j v I ≤ setValue J j v W := by simpa [setValue] using hi
    have hRight : setValue J j v J ≤ setValue J j v W := by
      simpa [setValue] using Nat.le_of_lt hjBound
    simpa [setValue] using run_pair lanes symbols blank x acc (setValue J j v) hAt hLeft hRight
  exact runsOutput_initializedCountdown W J S (initialGapPairFragment lanes symbols blank) x v
    (initialGapPairTimeBound (v W) symbols blank (v B) (v LO) (v HI))
    (initialGapPairOutput symbols blank (v B) (v LO) (v HI) (v I))
    (by simp) (by simp) (by simp) hj hReady.scratch.2.2.2 hBody suffix

/-- The entire gap block restores its valuation and emits the exact numeric traversal. -/
theorem run_initialGapsFragment (symbols blank : Nat) (x suffix : BinaryWord) (v : R → Nat)
    (hReady : InitialGapsReady lanes v) (hi : v I = 0) (hj : v J = 0) :
    ∃ cost ≤ initialGapsTimeBound (v W) symbols blank (v B) (v LO) (v HI),
      (initialGapsFragment lanes symbols blank).RunsOutput x cost v v suffix
        (initialGapsOutput (v W) symbols blank (v B) (v LO) (v HI) suffix) := by
  let bound := initialGapLoopTimeBound (v W)
    (initialGapPairTimeBound (v W) symbols blank (v B) (v LO) (v HI))
  have hBody (i : Nat) (hiBound : i < v W) (acc : BinaryWord) :
      ∃ cost ≤ bound, (initialGapsForLeft lanes symbols blank).RunsOutput x cost
        (setValue I i v) (setValue I i v) acc
        (initialGapsForLeftOutput (v W) symbols blank (v B) (v LO) (v HI) acc i) := by
    have atReady := ready_after_coordinate lanes v i (.gap .left) (Or.inl rfl) hReady
    have hLeft : setValue I i v I ≤ setValue I i v W := by
      simpa [setValue] using Nat.le_of_lt hiBound
    have hRight : setValue I i v J = 0 := by simpa [setValue] using hj
    simpa [bound, setValue] using run_for_left lanes symbols blank x acc (setValue I i v)
      atReady hLeft hRight
  exact runsOutput_initializedCountdown W I S (initialGapsForLeft lanes symbols blank) x v bound
    (initialGapsForLeftOutput (v W) symbols blank (v B) (v LO) (v HI))
    (by simp) (by simp) (by simp) hi hReady.scratch.2.2.2 hBody suffix

/-- Polynomial closure of the double loop and its affine name calculations. -/
theorem initialGapsTimeBound_polynomiallyBounded (symbols blank : Nat)
    {width base lower upper : Nat → Nat} (hw : PolynomiallyBounded width)
    (hb : PolynomiallyBounded base) (hl : PolynomiallyBounded lower)
    (hu : PolynomiallyBounded upper) :
    PolynomiallyBounded (fun n ↦ initialGapsTimeBound (width n) symbols blank
      (base n) (lower n) (upper n)) := by
  let lit := PolynomiallyBounded.const
  have hOffset := (((lit symbols).mul hw).add (lit blank))
  have hPrep := affineTime_polynomiallyBounded symbols blank hw
  have hLiteral := offsetLiteralTime_polynomiallyBounded hb hOffset
  have hEmit := (((lit 1).add hLiteral).add hLiteral).add (lit 1)
  have compare {a b : Nat → Nat} (ha : PolynomiallyBounded a) (hb : PolynomiallyBounded b) :
      PolynomiallyBounded (fun n ↦ ifEqualTime (a n) (b n)) :=
    ((lit 6).mul (ha.add hb)).add (lit 6)
  have hSuccessor := hw.add (lit 1)
  have hTests := (compare hSuccessor hw).add ((compare hw hl).add ((compare hw hu).add hEmit))
  have hCopy := ((lit 5).mul hw).add (lit 2)
  have hGap := ((hCopy.add (lit 1)).add hTests).add (hSuccessor.add (lit 1))
  have hClear := (hOffset.add (lit 1)).add (hOffset.add (lit 1))
  have hPair := (((hPrep.add hPrep).add hGap).add hClear)
  have loop {body : Nat → Nat} (h : PolynomiallyBounded body) :
      PolynomiallyBounded (fun n ↦ initialGapLoopTimeBound (width n) (body n)) :=
    hCopy.add ((hw.mul (h.add (lit 1))).add (lit 1))
  exact loop (loop hPair)

private theorem initialGapPairOutput_eq {states symbols certificates width : Nat}
    (table : FiniteTable states symbols certificates) (x suffix : BinaryWord)
    (capacity offset : Nat) (i j : Fin width) :
    initialGapPairOutput symbols table.blank.val (states + width) (offset + x.length + 1)
      (offset + x.length + 1 + capacity) i.val suffix j.val =
      (table.initialGap x capacity offset i j).reverse.foldl (fun out clause ↦
        true :: (CNFCode.encodeClause (clause.map (CNF.Literal.map indexedAtomName)) ++ out))
        suffix := by
  simp only [initialGapPairOutput, FiniteTable.initialGap]
  split <;> simp [*, indexedAtomName, Tableau.Atom.name, Tableau.Atom.time, Tableau.Atom.offset,
    CNF.Literal.map]

/-- The numeric schedule agrees with the gap part of `foldInitialClauses`. -/
theorem initialGapsOutput_eq {states symbols certificates : Nat}
    (table : FiniteTable states symbols certificates) (x suffix : BinaryWord)
    (capacity offset width : Nat) :
    initialGapsOutput width symbols table.blank.val (states + width) (offset + x.length + 1)
      (offset + x.length + 1 + capacity) suffix =
      Traversal.foldFinDesc width (fun acc i ↦ Traversal.foldFinDesc width
        (fun out j ↦ (table.initialGap x capacity offset i j).reverse.foldl
          (fun a clause ↦ true ::
            (CNFCode.encodeClause (clause.map (CNF.Literal.map indexedAtomName)) ++ a)) out) acc)
        suffix := by
  simp only [← initialGapPairOutput_eq, foldFinDesc_values, initialGapsOutput]
  let inner (acc : BinaryWord) (i : Nat) :=
    initialGapsForLeftOutput width symbols table.blank.val (states + width)
      (offset + x.length + 1) (offset + x.length + 1 + capacity) acc i
  change (List.range width).reverse.foldl inner suffix =
    Traversal.foldFinDesc width (fun acc i ↦ inner acc i.val) suffix
  rw [foldFinDesc_values]

end PvsNP.CookLevin
