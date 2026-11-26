module

public import PvsNP.SAT.OracleWorkspace
public import PvsNP.SAT.QueryIteration

/-! # One adaptive SAT query iteration with a uniform workspace -/

namespace PvsNP.SATSearch

/-- The answer to the appended false trial selects a feasible next prefix. -/
public theorem prefixQuery_append_of_trial_answer
    (D : Machine Bool) (k : Nat)
    (hTime : ∀ q, D.HaltsWithin q (q.length ^ k + k)) (hDecides : D.Decides CNFSAT)
    {word pref : BinaryWord} (hWellFormed : ∃ F, CNFCode.decode word = some F)
    (hShort : pref.length < word.length) (hFeasible : prefixQuery word pref ∈ CNFSAT)
    {answer : Bool}
    (hAnswer : answer = true ↔
      D.Accepts (appendUnitQuery (appendPrefixQuery word pref) pref.length false)) :
    prefixQuery word (pref ++ [!answer]) ∈ CNFSAT := by
  let oracle := extensionOracle (clockedOracle D k) word
  have hDecider := clockedOracle_eq_true_iff D k hTime hDecides
  have hValid (p : BinaryWord) (hLength : p.length ≤ word.length) :
      oracle p = true ↔ prefixQuery word p ∈ CNFSAT := by
    simp only [oracle, extensionOracle, ite_eq_left hLength, hDecider]
  have hExtend (b : Bool) : (pref ++ [b]).length ≤ word.length := by
    simpa only [List.length_append, List.length_singleton] using Nat.succ_le_of_lt hShort
  have hTrial : oracle (pref ++ [false]) = answer := by
    apply Bool.eq_iff_iff.mpr
    calc
      oracle (pref ++ [false]) = true ↔ prefixQuery word (pref ++ [false]) ∈ CNFSAT :=
        hValid _ (hExtend false)
      _ ↔ appendPrefixQuery word (pref ++ [false]) ∈ CNFSAT :=
        (appendPrefixQuery_mem_CNFSAT_iff word _ hWellFormed).symm
      _ ↔ D.Accepts (appendUnitQuery (appendPrefixQuery word pref) pref.length false) := by
        rw [appendPrefixQuery_append_bit, hDecides]
      _ ↔ answer = true := hAnswer.symm
  have hSpec := extensionOracle_eq_true_iff (clockedOracle D k) hDecider word
  have hNext := prefixOracle_append_feasible hSpec hShort ((hValid _ hShort.le).mpr hFeasible)
  rw [show extensionOracle (clockedOracle D k) word (pref ++ [false]) = answer from hTrial]
    at hNext
  exact (hValid _ (hExtend (!answer))).mp hNext

/-- A uniform physical transition bound for one adaptive query iteration. -/
@[expose] public def satQueryStepBound (k n : Nat) : Nat :=
  let B := n + n * (n + 5)
  (2 * (B + n + 6) + 2) + oracleWorkspaceCallBound k n + (2 * (B + 2) + 2)

public theorem queryStepBound_le_satQueryStepBound (k n j i clock : Nat)
    (hTerminator : j ≤ n + n * (n + 5)) (hIndex : i ≤ n)
    (hClock : clock ≤ (n + n * (n + 5)) ^ k + k) :
    queryStepBound j i (oracleWorkspaceRadius k n) (oracleWorkspaceRadius k n) clock ≤
      satQueryStepBound k n := by
  simp only [queryStepBound, satQueryStepBound, oracleWorkspaceCallBound]
  omega

/-- A fixed clock exponent gives a polynomial budget for up to `n + 1` iterations. -/
public theorem satQueryIterations_polynomiallyBounded (k : Nat) :
    PolynomiallyBounded (fun n ↦ (n + 1) * satQueryStepBound k n) := by
  let hN := PolynomiallyBounded.id
  let c := PolynomiallyBounded.const
  have hCount := hN.add (c 1)
  have hB := hN.add (hN.mul (hN.add (c 5)))
  have hAppend := ((c 2).mul ((hB.add hN).add (c 6))).add (c 2)
  have hCommit := ((c 2).mul (hB.add (c 2))).add (c 2)
  apply (((hCount.mul hAppend).add (loadedSearchCalls_polynomiallyBounded k)).add
    (hCount.mul hCommit)).mono
  intro n
  simp only [satQueryStepBound, Nat.mul_add]
  exact Nat.le_refl _

private theorem length_appendPrefixQuery_le {word pref : BinaryWord}
    (hWellFormed : ∃ F, CNFCode.decode word = some F) (hLength : pref.length ≤ word.length) :
    (appendPrefixQuery word pref).length ≤ word.length + word.length * (word.length + 5) := by
  rw [length_appendPrefixQuery_eq_prefixQuery word pref hWellFormed, length_prefixQuery]
  exact prefixQueryLength_le word.length pref.length hLength

open TrackCall TrackCall.QueryEdit

/-- One physical stage extends the query buffer by a feasible assignment bit.
The auxiliary track supplies that stage's stop mark and workspace boundaries. -/
public theorem run_sat_query_iteration
    (D : Machine Bool) (k : Nat)
    (hTime : ∀ q, D.HaltsWithin q (q.length ^ k + k)) (hDecides : D.Decides CNFSAT)
    {ρ : Type} [Finite ρ] [Inhabited ρ]
    {C : Controller D (Cell ρ)} {labels : StepLabels C.State} {stop left right : ρ → Bool}
    (rules : StepRules C labels stop (queryLayout D left right)) (word pref : BinaryWord)
    (hWellFormed : ∃ F, CNFCode.decode word = some F)
    (hShort : pref.length < word.length) (hFeasible : prefixQuery word pref ∈ CNFSAT)
    {tape : C.compile.Tape} {work : Int → D.Symbol} {data : Int → Cell ρ}
    (hTracks : TracksAt D ρ tape 0 work data)
    (hBuffer : QueryBuffer data (appendPrefixQuery word pref) none)
    (hBlank : Loader.BlankOutside D (Cell ρ) tape
      (oracleWorkspaceRadius k word.length) (oracleWorkspaceRadius k word.length))
    (hEdgesLeft : ∀ a : Int, left (data a).1 = true ↔
      a = -(oracleWorkspaceRadius k word.length : Int))
    (hEdgesRight : ∀ a : Int, right (data a).1 =
      decide (a = (oracleWorkspaceRadius k word.length : Int)))
    (hStop : ∀ a : Nat, a ≤ pref.length →
      stop (data (((appendPrefixQuery word pref).dropLast.length : Int) + 3 + (a : Int))).1 =
        decide (a = pref.length)) :
    let current := appendPrefixQuery word pref
    let j := current.dropLast.length
    let R := oracleWorkspaceRadius k word.length
    ∃ (answer : Bool) (ticks : Nat) (nextWork : Int → D.Symbol),
      ticks ≤ satQueryStepBound k word.length ∧
      let final := C.compile.run ticks ⟨.inl (.inl labels.append.seekTail), tape⟩
      let nextData :=
        updateCell ((j + 2 : Nat) : Int) (ordinary (!answer))
          (writeEdits (j : Int) (appendEdits pref.length) data)
      final.state = .inl (.inl labels.next) ∧
      TracksAt D ρ final.tape 0 nextWork nextData ∧
      QueryBuffer nextData (appendPrefixQuery word (pref ++ [!answer])) none ∧
      Loader.BlankOutside D (Cell ρ) final.tape R R ∧
      (answer = true ↔ D.Accepts (appendUnitQuery current pref.length false)) ∧
      prefixQuery word (pref ++ [!answer]) ∈ CNFSAT := by
  dsimp only
  let current := appendPrefixQuery word pref
  let j := current.dropLast.length
  let B := word.length + word.length * (word.length + 5)
  let R := oracleWorkspaceRadius k word.length
  let trial := appendUnitQuery current pref.length false
  let clock := trial.length ^ k + k
  have hLength : current.length ≤ B := length_appendPrefixQuery_le hWellFormed hShort.le
  have hTerminator : j ≤ B := by
    rw [show j = current.length - 1 from List.length_dropLast]
    omega
  have hNextLength : (pref ++ [false]).length ≤ word.length := by
    simpa only [List.length_append, List.length_singleton] using Nat.succ_le_of_lt hShort
  have hTrialLength : trial.length ≤ B := by
    rw [show trial = appendPrefixQuery word (pref ++ [false]) from
      (appendPrefixQuery_append_bit word pref false).symm]
    exact length_appendPrefixQuery_le hWellFormed hNextLength
  have hClockBound : clock ≤ B ^ k + k :=
    Nat.add_le_add_right (Nat.pow_le_pow_left hTrialLength k) k
  have hRadius : R = B + (B ^ k + k) + 1 := rfl
  have hFit : trial.length ≤ R + 1 := by omega
  have hClockFits : clock ≤ R := by omega
  obtain ⟨answer, ticks, nextWork, hTicks, hState, hNextTracks, hNextBuffer, hNextBlank, hAnswer⟩ :=
    run_query_iteration rules current pref.length R R clock hTracks hBuffer hBlank
      hEdgesLeft hEdgesRight hStop (by omega) hFit hClockFits hClockFits (hTime trial)
  have hBudget := queryStepBound_le_satQueryStepBound k word.length j pref.length clock
    hTerminator hShort.le hClockBound
  have hSelected := prefixQuery_append_of_trial_answer D k hTime hDecides
    hWellFormed hShort hFeasible hAnswer
  refine ⟨answer, ticks, nextWork, hTicks.trans hBudget, hState, hNextTracks, ?_,
    hNextBlank, hAnswer, hSelected⟩
  rw [appendPrefixQuery_append_bit]
  exact hNextBuffer

end PvsNP.SATSearch
