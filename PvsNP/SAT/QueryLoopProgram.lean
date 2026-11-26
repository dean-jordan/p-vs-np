module

public import PvsNP.SAT.QueryLoop
public import PvsNP.SAT.QueryIterationProgram

/-! # A bounded SAT search run of the concrete cyclic controller -/

public section

namespace PvsNP.SATSearch

open TrackCall TrackCall.QueryEdit

/-- Starting with a satisfiable word on a prepared tape, the cyclic controller
reaches the first scan of the next cycle with a checked assignment. -/
theorem run_loopIterationProgram
    (D : Machine Bool) (k : Nat)
    (hTime : ∀ q, D.HaltsWithin q (q.length ^ k + k)) (hDecides : D.Decides CNFSAT)
    {ρ : Type} [Finite ρ] [Inhabited ρ] (stop left right : ρ → Bool)
    (word : BinaryWord) (hSat : word ∈ CNFSAT)
    {tape : (machine D (Cell ρ)).Tape} {work : Int → D.Symbol} {data : Int → Cell ρ}
    (hTracks : TracksAt D ρ tape 0 work data)
    (hBuffer : QueryBuffer data word none)
    (hBlank : Loader.BlankOutside D (Cell ρ) tape
      (oracleWorkspaceRadius k word.length) (oracleWorkspaceRadius k word.length))
    (hEdgesLeft : ∀ a : Int, left (data a).1 = true ↔
      a = -(oracleWorkspaceRadius k word.length : Int))
    (hEdgesRight : ∀ a : Int, right (data a).1 =
      decide (a = (oracleWorkspaceRadius k word.length : Int)))
    (hStopSchedule : ∀ a : Nat,
      stop (data (a : Int)).1 = (unaryStopPositions word.length word.length).contains a) :
    ∃ (ticks : Nat) (assignment : BinaryWord) (finalWork : Int → D.Symbol)
      (finalData : Int → Cell ρ),
      ticks ≤ word.length * satQueryStepBound k word.length ∧
      assignment.length = word.length ∧ SATAssignment.checkWord word assignment = true ∧
      let final := (loopIterationProgram D stop (queryLayout D left right)).compile.run ticks
        ⟨.inl (.inl .seekTail), tape⟩
      final.state = .inl (.inl .seekTail) ∧
      TracksAt D ρ final.tape 0 finalWork finalData ∧
      QueryBuffer finalData (appendPrefixQuery word assignment) none ∧
      Loader.BlankOutside D (Cell ρ) final.tape
        (oracleWorkspaceRadius k word.length) (oracleWorkspaceRadius k word.length) := by
  have hWellFormed : ∃ F, CNFCode.decode word = some F := by
    obtain ⟨F, hF, _⟩ := hSat
    exact ⟨F, hF⟩
  have hFeasible : prefixQuery word [] ∈ CNFSAT := by
    simpa only [prefixQuery_nil] using hSat
  exact run_sat_query_loop D k hTime hDecides
    (loopIterationProgram_rules D stop (queryLayout D left right))
    loopIterationLabels_next_eq_seekTail word [] word.length hWellFormed (Nat.zero_add _)
    hFeasible hTracks hBuffer hBlank hEdgesLeft hEdgesRight hStopSchedule

end PvsNP.SATSearch
