module

public import Batteries.Data.List.Basic
public import PvsNP.SAT.OracleSearch
public import PvsNP.TuringMachine.TrackCall.Return

import Init.Data.List.Nat.Sum

/-! # Returning Cook calls for prepared SAT search queries -/

namespace PvsNP.SATSearch

private theorem exists_ticks_of_pointwise {α : Type} {R : α → Nat → Prop}
    {queries : List α} {count cap : Nat} (hCount : queries.length ≤ count)
    (hCall : ∀ q ∈ queries, ∃ t ≤ cap, R q t) :
    ∃ ticks : List Nat, List.Forall₂ R queries ticks ∧ ticks.sum ≤ count * cap := by
  suffices ∃ ticks : List Nat, List.Forall₂ R queries ticks ∧
      ticks.sum ≤ queries.length * cap by
    obtain ⟨ticks, hLinked, hSum⟩ := this
    exact ⟨ticks, hLinked, hSum.trans (Nat.mul_le_mul_right cap hCount)⟩
  clear hCount count
  induction queries with
  | nil => exact ⟨[], .nil, by simp⟩
  | cons q rest ih =>
    obtain ⟨t, ht, hResult⟩ := hCall q (List.mem_cons_self ..)
    obtain ⟨ticks, hLinked, hSum⟩ := ih (fun q hq ↦ hCall q (List.mem_cons_of_mem _ hq))
    refine ⟨t :: ticks, .cons hResult hLinked, ?_⟩
    rw [List.sum_cons, List.length_cons, Nat.succ_mul, Nat.add_comm (rest.length * cap)]
    exact Nat.add_le_add ht hSum

/-- Every query in a clocked search trace can run from its own prepared tape.
The total counts physical call transitions through return to the controller. -/
public theorem search_queries_have_returning_calls
    (D : Machine Bool) (k : Nat)
    (hTime : ∀ q, D.HaltsWithin q (q.length ^ k + k))
    {ρ : Type} [Finite ρ] [Inhabited ρ] (C : TrackCall.Controller D ρ)
    (reject accept : C.State) (saved : Turing.Tape ρ) (word : BinaryWord) :
    let n := word.length
    let B := n + n * (n + 5)
    ∃ ticks : List Nat,
      List.Forall₂ (fun q t ↦
        let final := C.compile.run t
          (C.embedCall reject accept (TrackCall.entry D ρ (TrackCall.prepareTape D ρ q saved)))
        final.state = .inl (.inl (C.resume reject accept (clockedOracle D k q))) ∧
          TrackCall.FrameAt D ρ final.tape saved 0)
        (searchWithOracle (clockedOracle D k) word).2 ticks ∧
      ticks.sum ≤ (n + 1) * (2 * (B ^ k + k) + 2) := by
  dsimp only
  let B := word.length + word.length * (word.length + 5)
  refine exists_ticks_of_pointwise (cap := 2 * (B ^ k + k) + 2)
    (searchWithOracle_query_count_le (clockedOracle D k) word) ?_
  intro q hq
  have hLength : q.length ≤ B := searchWithOracle_query_length_le (clockedOracle D k) word q hq
  have hPower := Nat.pow_le_pow_left hLength k
  obtain ⟨answer, t, ht, hState, hFrame, hAnswer⟩ :=
    C.run_call_prepared reject accept q saved (hTime q)
  have hClocked : answer = clockedOracle D k q :=
    Bool.eq_iff_iff.mpr (hAnswer.trans (clockedOracle_eq_true_iff_accepts D k q (hTime q)).symm)
  exact ⟨t, by omega, hClocked ▸ hState, hFrame⟩

/-- For a fixed decider exponent, the total prepared-call bound is polynomial. -/
public theorem returningSearchCalls_polynomiallyBounded (k : Nat) :
    PolynomiallyBounded (fun n ↦ (n + 1) * (2 * ((n + n * (n + 5)) ^ k + k) + 2)) := by
  let hN := PolynomiallyBounded.id
  let c := PolynomiallyBounded.const
  have hQuery := hN.add (hN.mul (hN.add (c 5)))
  have hClock := (hQuery.pow k).add (c k)
  exact (hN.add (c 1)).mul (((c 2).mul hClock).add (c 2))

end PvsNP.SATSearch
