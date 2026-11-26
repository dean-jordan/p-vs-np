module

public import PvsNP.SAT.OracleSearch
public import PvsNP.TuringMachine.TrackCall.Loader.Load

/-! # A fixed workspace for the queries of a clocked SAT search -/

namespace PvsNP.SATSearch

/-- A symmetric workspace accommodates both the longest query and the
largest child clock in the recorded trace. -/
@[expose] public def oracleWorkspaceRadius (k n : Nat) : Nat :=
  let B := n + n * (n + 5)
  B + (B ^ k + k) + 1

/-- A uniform physical transition bound for loading and running one query. -/
@[expose] public def oracleWorkspaceCallBound (k n : Nat) : Nat :=
  let B := n + n * (n + 5)
  4 * oracleWorkspaceRadius k n + 2 * (B ^ k + k) + 6

/-- Given the protected query and boundary marks in place, the loader can run
any recorded query and return with the same frame and blank exterior. -/
public theorem search_query_has_loaded_call
    (D : Machine Bool) (k : Nat)
    (hTime : ∀ q, D.HaltsWithin q (q.length ^ k + k))
    {ρ : Type} [Finite ρ] [Inhabited ρ] (C : TrackCall.Controller D ρ)
    (labels : TrackCall.Loader.Labels C.State) (layout : TrackCall.Loader.Layout D ρ)
    (rules : TrackCall.Loader.Rules C labels layout)
    (word query : BinaryWord) (hQuery : query ∈ (searchWithOracle (clockedOracle D k) word).2)
    {tape : C.compile.Tape} {saved : Turing.Tape ρ}
    (window : TrackCall.Loader.WindowSpec layout saved (D.start query).tape
      (oracleWorkspaceRadius k word.length) (oracleWorkspaceRadius k word.length))
    (hFrame : TrackCall.FrameAt D ρ tape saved 0)
    (hBlank : TrackCall.Loader.BlankOutside D ρ tape
      (oracleWorkspaceRadius k word.length) (oracleWorkspaceRadius k word.length)) :
    ∃ ticks ≤ oracleWorkspaceCallBound k word.length,
      let final := C.compile.run ticks ⟨.inl (.inl labels.seekLeft), tape⟩
      final.state =
        .inl (.inl (C.resume labels.reject labels.accept (clockedOracle D k query))) ∧
      TrackCall.FrameAt D ρ final.tape saved 0 ∧
      TrackCall.Loader.BlankOutside D ρ final.tape
        (oracleWorkspaceRadius k word.length) (oracleWorkspaceRadius k word.length) := by
  let B := word.length + word.length * (word.length + 5)
  let R := oracleWorkspaceRadius k word.length
  have hLength : query.length ≤ B :=
    searchWithOracle_query_length_le (clockedOracle D k) word query hQuery
  have hClock : query.length ^ k + k ≤ B ^ k + k :=
    Nat.add_le_add_right (Nat.pow_le_pow_left hLength k) k
  have hRadius : R = B + (B ^ k + k) + 1 := rfl
  have hLengthFits : query.length ≤ R + 1 := by omega
  have hClockFits : query.length ^ k + k ≤ R := by omega
  obtain ⟨answer, ticks, hTicks, hState, hFinalFrame, hFinalBlank, hAnswer⟩ :=
    TrackCall.Loader.run_load_call C labels layout rules R R query window hFrame hBlank
      hLengthFits hClockFits hClockFits (hTime query)
  have hClocked : answer = clockedOracle D k query :=
    Bool.eq_iff_iff.mpr
      (hAnswer.trans (clockedOracle_eq_true_iff_accepts D k query (hTime query)).symm)
  have hBound : oracleWorkspaceCallBound k word.length = 4 * R + 2 * (B ^ k + k) + 6 := rfl
  refine ⟨ticks, ?_, hClocked ▸ hState, hFinalFrame, hFinalBlank⟩
  rw [hBound]
  omega

/-- Multiplying the loaded-call bound by the maximum query count gives a
polynomial for each fixed decider exponent. -/
public theorem loadedSearchCalls_polynomiallyBounded (k : Nat) :
    PolynomiallyBounded (fun n ↦ (n + 1) * oracleWorkspaceCallBound k n) := by
  let hN := PolynomiallyBounded.id
  let c := PolynomiallyBounded.const
  have hB := hN.add (hN.mul (hN.add (c 5)))
  have hClock := (hB.pow k).add (c k)
  have hRadius : PolynomiallyBounded (oracleWorkspaceRadius k) :=
    (hB.add hClock).add (c 1)
  exact (hN.add (c 1)).mul ((((c 4).mul hRadius).add ((c 2).mul hClock)).add (c 6))

end PvsNP.SATSearch
