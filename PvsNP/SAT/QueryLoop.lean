module

public import PvsNP.SAT.QueryIndices
public import PvsNP.SAT.QueryIterationSAT

/-! # A continuing run of the adaptive SAT query stages -/

namespace PvsNP.SATSearch

open TrackCall TrackCall.QueryEdit

/-- With the immutable stop schedule and workspace edges already on the
auxiliary track, the stages extend the feasible prefix to a checked assignment.
The final configuration is at the next stage boundary. -/
public theorem run_sat_query_loop
    (D : Machine Bool) (k : Nat)
    (hTime : ∀ q, D.HaltsWithin q (q.length ^ k + k)) (hDecides : D.Decides CNFSAT)
    {ρ : Type} [Finite ρ] [Inhabited ρ]
    {C : Controller D (Cell ρ)} {labels : StepLabels C.State} {stop left right : ρ → Bool}
    (rules : StepRules C labels stop (queryLayout D left right))
    (hLoop : labels.next = labels.append.seekTail) (word pref : BinaryWord) (remaining : Nat)
    (hWellFormed : ∃ F, CNFCode.decode word = some F)
    (hLength : pref.length + remaining = word.length)
    (hFeasible : prefixQuery word pref ∈ CNFSAT)
    {tape : C.compile.Tape} {work : Int → D.Symbol} {data : Int → Cell ρ}
    (hTracks : TracksAt D ρ tape 0 work data)
    (hBuffer : QueryBuffer data (appendPrefixQuery word pref) none)
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
      ticks ≤ remaining * satQueryStepBound k word.length ∧
      assignment.length = word.length ∧ SATAssignment.checkWord word assignment = true ∧
      let final := C.compile.run ticks ⟨.inl (.inl labels.append.seekTail), tape⟩
      final.state = .inl (.inl labels.append.seekTail) ∧
      TracksAt D ρ final.tape 0 finalWork finalData ∧
      QueryBuffer finalData (appendPrefixQuery word assignment) none ∧
      Loader.BlankOutside D (Cell ρ) final.tape
        (oracleWorkspaceRadius k word.length) (oracleWorkspaceRadius k word.length) := by
  have hWord : word ≠ [] := by
    obtain ⟨F, hDecode⟩ := hWellFormed
    rw [CNFCode.decode_eq_some_iff.mp hDecode]
    cases F <;> simp [CNFCode.encode_cons]
  induction remaining generalizing pref tape work data with
  | zero =>
    have hFull : pref.length = word.length := by omega
    obtain ⟨assignment, hSize, hPrefix, hCheck⟩ :=
      (mem_prefixQuery_iff_exists_assignment hFull.le).mp hFeasible
    have hSame := hPrefix.eq_of_length (hFull.trans hSize.symm)
    subst assignment
    exact ⟨0, pref, work, data, Nat.zero_le _, hFull, hCheck, rfl, hTracks, hBuffer, hBlank⟩
  | succ remaining ih =>
    have hShort : pref.length < word.length := by omega
    let j := (appendPrefixQuery word pref).dropLast.length
    have hStop (a : Nat) (ha : a ≤ pref.length) :
        stop (data ((j : Int) + 3 + (a : Int))).1 = decide (a = pref.length) := by
      rw [show j = queryTail word.length pref.length from
        dropLast_length_appendPrefixQuery word pref hWord]
      rw [show (queryTail word.length pref.length : Int) + 3 + (a : Int) =
        ((queryTail word.length pref.length + 3 + a : Nat) : Int) by omega, hStopSchedule]
      exact contains_unaryStopPositions word.length word.length pref.length a hShort ha
    obtain ⟨answer, stageTicks, nextWork, hStageTicks, hStageState, hNextTracks, hNextBuffer,
      hNextBlank, _, hNextFeasible⟩ :=
      run_sat_query_iteration D k hTime hDecides rules word pref hWellFormed hShort hFeasible
        hTracks hBuffer hBlank hEdgesLeft hEdgesRight hStop
    let nextPref := pref ++ [!answer]
    let trialData := writeEdits (j : Int) (appendEdits pref.length) data
    let nextData := updateCell ((j + 2 : Nat) : Int) (ordinary (!answer)) trialData
    let middle := C.compile.run stageTicks ⟨.inl (.inl labels.append.seekTail), tape⟩
    have hPayload (a : Int) : (nextData a).1 = (data a).1 :=
      (writeEdits_payload _ [ordinary (!answer)] trialData a).trans
        (writeEdits_payload (j : Int) (appendEdits pref.length) data a)
    have hNextLength : nextPref.length + remaining = word.length := by
      simp only [nextPref, List.length_append, List.length_singleton]
      omega
    obtain ⟨restTicks, assignment, finalWork, finalData, hRestTicks, hAssignLength, hCheck,
      hState, hFinalTracks, hFinalBuffer, hFinalBlank⟩ :=
      ih (pref := nextPref) (tape := middle.tape) (work := nextWork) (data := nextData)
        hNextLength hNextFeasible hNextTracks hNextBuffer hNextBlank
        (fun a ↦ by simpa only [hPayload a] using hEdgesLeft a)
        (fun a ↦ by simpa only [hPayload a] using hEdgesRight a)
        (fun a ↦ by simpa only [hPayload (a : Int)] using hStopSchedule a)
    have hResume : middle.state = .inl (.inl labels.append.seekTail) := by
      rw [← hLoop]
      exact hStageState
    have hMiddle : C.compile.run stageTicks ⟨.inl (.inl labels.append.seekTail), tape⟩ =
        ⟨.inl (.inl labels.append.seekTail), middle.tape⟩ := by
      change middle = ⟨.inl (.inl labels.append.seekTail), middle.tape⟩
      rw [← hResume]
    have hTicks : stageTicks + restTicks ≤ (remaining + 1) * satQueryStepBound k word.length := by
      rw [Nat.succ_mul]
      omega
    refine ⟨stageTicks + restTicks, assignment, finalWork, finalData, hTicks, hAssignLength,
      hCheck, ?_⟩
    dsimp only
    rw [Machine.run_add, hMiddle]
    exact ⟨hState, hFinalTracks, hFinalBuffer, hFinalBlank⟩

end PvsNP.SATSearch
