module

public import PvsNP.MCSP.ClockedPrefixOracle
public import PvsNP.MCSP.MagnificationClock
public import PvsNP.TuringMachine.TrackCall.Loader.Load

/-! # Loaded Cook calls for the adaptive MCSP prefix search -/

public section

namespace PvsNP.MCSP

open Circuits
open TrackCall (Controller FrameAt)
open TrackCall.Loader (BlankOutside Labels Layout Rules WindowSpec)

/-- Use one symmetric work interval for every request at the same arity and cap. -/
@[expose] def mergePrefixCallRadius (k parameters : Nat) : Nat :=
  26 * (parameters + 1) ^ 2 + mergeRequestTickBound k parameters

/-- Count the loader sweeps and both directions of the decider call. -/
@[expose] def mergePrefixCallBound (k parameters : Nat) : Nat :=
  4 * mergePrefixCallRadius k parameters + 2 * mergeRequestTickBound k parameters + 6

private theorem queryLength_polynomiallyBounded :
    PolynomiallyBounded (fun n ↦ 26 * (n + 1) ^ 2) :=
  (PolynomiallyBounded.const 26).mul
    ((PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)).pow 2)

theorem mergePrefixCallBound_polynomiallyBounded (k : Nat) :
    PolynomiallyBounded (mergePrefixCallBound k) := by
  have hTicks := mergeRequestTickBound_polynomiallyBounded k
  have hRadius : PolynomiallyBounded (mergePrefixCallRadius k) :=
    queryLength_polynomiallyBounded.add hTicks
  exact (((PolynomiallyBounded.const 4).mul hRadius).add
    ((PolynomiallyBounded.const 2).mul hTicks)).add (PolynomiallyBounded.const 6)

/-- Starting at the loader entry with the query encoded on the protected track,
the real Cook call returns to the chosen branch and leaves the workspace reusable. -/
theorem run_clockedPrefixCall (D : Machine Bool) (k : Nat)
    (hTime : ∀ word : BinaryWord, D.HaltsWithin word (word.length ^ k + k))
    {ρ : Type} [Finite ρ] [Inhabited ρ] (C : Controller D ρ)
    (labels : Labels C.State) (layout : Layout D ρ) (rules : Rules C labels layout)
    (r : MergeRequest) {tape : C.compile.Tape} {saved : Turing.Tape ρ}
    (window : WindowSpec layout saved (D.start (encodeMergeRequest r)).tape
      (mergePrefixCallRadius k (r.arity + r.cap)) (mergePrefixCallRadius k (r.arity + r.cap)))
    (hFrame : FrameAt D ρ tape saved 0)
    (hBlank : BlankOutside D ρ tape
      (mergePrefixCallRadius k (r.arity + r.cap)) (mergePrefixCallRadius k (r.arity + r.cap))) :
    ∃ ticks ≤ mergePrefixCallBound k (r.arity + r.cap),
      let final := C.compile.run ticks ⟨.inl (.inl labels.seekLeft), tape⟩
      final.state =
        .inl (.inl (C.resume labels.reject labels.accept (clockedPrefixAnswer D k r))) ∧
      FrameAt D ρ final.tape saved 0 ∧ BlankOutside D ρ final.tape
        (mergePrefixCallRadius k (r.arity + r.cap))
        (mergePrefixCallRadius k (r.arity + r.cap)) := by
  let word := encodeMergeRequest r
  let radius := mergePrefixCallRadius k (r.arity + r.cap)
  have hLength := (length_encodeMergeRequest_le r).trans
    (mergeRequestLengthBound_le_quadratic r.arity r.cap)
  have hDecider := mergeRequestClock_le k r
  have hLengthFits : word.length ≤ radius + 1 := by
    change word.length ≤
      26 * (r.arity + r.cap + 1) ^ 2 + mergeRequestTickBound k (r.arity + r.cap) + 1
    exact hLength.trans (by omega)
  have hTimeFits : mergeRequestClock k r ≤ radius := by
    exact hDecider.trans (Nat.le_add_left _ _)
  obtain ⟨answer, ticks, hTicks, hState, hFinalFrame, hFinalBlank, hAnswer⟩ :=
    TrackCall.Loader.run_load_call C labels layout rules radius radius word window hFrame hBlank
      hLengthFits hTimeFits hTimeFits (hTime word)
  have hClocked : answer = clockedPrefixAnswer D k r := by
    apply Bool.eq_iff_iff.mpr
    rw [hAnswer, D.accepts_iff_at_bound word (hTime word)]
    change (D.run (mergeRequestClock k r) (D.start word)).state = .inr true ↔
      clockedPrefixAnswer D k r = true
    cases hState : (D.run (mergeRequestClock k r) (D.start word)).state <;>
      simp [clockedPrefixAnswer, word, hState]
  refine ⟨ticks, ?_, hClocked ▸ hState, hFinalFrame, hFinalBlank⟩
  change ticks ≤ 4 * radius + 2 * mergeRequestTickBound k (r.arity + r.cap) + 6
  omega

/-- Canonical requests in their actual order, including the opening feasibility query. -/
@[expose] def mergeRowRequests {n : Nat} (cap : Nat) (oracle : MergePrefixOracle n)
    (old : BooleanCircuit n) (seen : Nat) (bit : Bool)
    (hSeen : seen ≤ 2 ^ n) (hOld : old.size ≤ max 1 cap) : List MergeRequest :=
  ((searchMergeWithPrefix cap oracle old seen bit).2).attach.map fun pref ↦
    ⟨n, cap, old, seen, bit, pref.val, hSeen, hOld,
      searchMergeWithPrefix_query_length_le cap oracle old seen bit pref.property⟩

theorem mergeRowRequests_length {n : Nat} (cap : Nat) (oracle : MergePrefixOracle n)
    (old : BooleanCircuit n) (seen : Nat) (bit : Bool)
    (hSeen : seen ≤ 2 ^ n) (hOld : old.size ≤ max 1 cap) :
    (mergeRowRequests cap oracle old seen bit hSeen hOld).length =
      (searchMergeWithPrefix cap oracle old seen bit).2.length := by
  simp only [mergeRowRequests, List.length_map, List.length_attach]

theorem mergeRowRequests_parameters {n cap : Nat} {oracle : MergePrefixOracle n}
    {old : BooleanCircuit n} {seen : Nat} {bit : Bool}
    {hSeen : seen ≤ 2 ^ n} {hOld : old.size ≤ max 1 cap} {r : MergeRequest}
    (h : r ∈ mergeRowRequests cap oracle old seen bit hSeen hOld) :
    r.arity = n ∧ r.cap = cap := by
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp h
  exact ⟨rfl, rfl⟩

theorem mergeRowRequests_answers (D : Machine Bool) (k : Nat) {n : Nat} (cap : Nat)
    (old : BooleanCircuit n) (seen : Nat) (bit : Bool)
    (hSeen : seen ≤ 2 ^ n) (hOld : old.size ≤ max 1 cap) :
    let oracle := clockedMergePrefixOracle (n := n) D k cap
    (mergeRowRequests cap oracle old seen bit hSeen hOld).map
        (fun r ↦ (r.pref, clockedPrefixAnswer D k r)) =
      (searchMergeWithPrefix cap oracle old seen bit).2.map
        (fun pref ↦ (pref, oracle old seen bit pref)) := by
  dsimp only
  rw [mergeRowRequests, List.map_map]
  conv_rhs => rw [← List.attach_map_val]
  apply List.map_congr_left
  intro q _
  let r : MergeRequest := ⟨n, cap, old, seen, bit, q.val, hSeen, hOld,
    searchMergeWithPrefix_query_length_le cap _ old seen bit q.property⟩
  exact congrArg (fun answer : Bool ↦ (q.val, answer))
    (clockedMergePrefixOracle_eq_answer D k r).symm

/-- A uniform bound for all prepared loader calls in one adaptive row update. -/
@[expose] def mergeRowCallBound (k parameters : Nat) : Nat :=
  (26 * (parameters + 1) ^ 2 + 1) * mergePrefixCallBound k parameters

theorem mergeRowCallBound_polynomiallyBounded (k : Nat) :
    PolynomiallyBounded (mergeRowCallBound k) :=
  (queryLength_polynomiallyBounded.add (PolynomiallyBounded.const 1)).mul
    (mergePrefixCallBound_polynomiallyBounded k)

theorem mergeRowPreparedBound_polynomiallyBounded (k : Nat) {prepareCost : Nat → Nat}
    (hPrepare : PolynomiallyBounded prepareCost) :
    PolynomiallyBounded (fun parameters ↦
      (26 * (parameters + 1) ^ 2 + 1) *
        (prepareCost parameters + mergePrefixCallBound k parameters)) :=
  (queryLength_polynomiallyBounded.add (PolynomiallyBounded.const 1)).mul
    (hPrepare.add (mergePrefixCallBound_polynomiallyBounded k))

theorem mergeRowRequests_length_le {n cap : Nat} {oracle : MergePrefixOracle n}
    {old : BooleanCircuit n} {seen : Nat} {bit : Bool}
    (hSeen : seen ≤ 2 ^ n) (hOld : old.size ≤ max 1 cap) :
    (mergeRowRequests cap oracle old seen bit hSeen hOld).length ≤ 26 * (n + cap + 1) ^ 2 + 1 := by
  rw [mergeRowRequests_length]
  apply (searchMergeWithPrefix_query_count_le cap oracle old seen bit).trans
  apply Nat.add_le_add_right
  apply Nat.le_trans ?_ (mergeRequestLengthBound_le_quadratic n cap)
  unfold mergeRequestLengthBound
  omega

/-- Compose a list of loaded calls on one physical tape when the local producer
can write the next query and recover its invariant after the selected reply. -/
theorem run_clockedPrefixCalls (D : Machine Bool) (k : Nat)
    (hTime : ∀ word : BinaryWord, D.HaltsWithin word (word.length ^ k + k))
    {ρ : Type} [Finite ρ] [Inhabited ρ] (C : Controller D ρ)
    (labels : Labels C.State) (layout : Layout D ρ) (rules : Rules C labels layout)
    (parameters prepareCost : Nat) (requests : List MergeRequest)
    (hParameters : ∀ r ∈ requests, r.arity + r.cap = parameters)
    (inv : List MergeRequest → C.compile.Config → Prop)
    (hPrepare : ∀ r pending, (r :: pending) <:+ requests → ∀ cfg, inv (r :: pending) cfg →
      ∃ prep ≤ prepareCost, ∃ saved : Turing.Tape ρ,
        let ready := C.compile.run prep cfg
        let radius := mergePrefixCallRadius k (r.arity + r.cap)
        ready.state = .inl (.inl labels.seekLeft) ∧
          WindowSpec layout saved (D.start (encodeMergeRequest r)).tape radius radius ∧
          FrameAt D ρ ready.tape saved 0 ∧ BlankOutside D ρ ready.tape radius radius ∧
          ∀ next : C.compile.Config, next.state =
            .inl (.inl (C.resume labels.reject labels.accept (clockedPrefixAnswer D k r))) →
            FrameAt D ρ next.tape saved 0 → BlankOutside D ρ next.tape radius radius →
              inv pending next)
    (cfg : C.compile.Config) (hStart : inv requests cfg) :
    ∃ ticks ≤ requests.length * (prepareCost + mergePrefixCallBound k parameters),
      inv [] (C.compile.run ticks cfg) := by
  induction requests generalizing cfg with
  | nil => exact ⟨0, Nat.zero_le _, hStart⟩
  | cons request rest ih =>
    obtain ⟨prep, hPrep, saved, hEntry, hWindow, hFrame, hBlank, hReady⟩ :=
      hPrepare request rest (List.suffix_refl _) cfg hStart
    let ready := C.compile.run prep cfg
    change ready.state = _ at hEntry
    have hEntryCfg : ready = ⟨.inl (.inl labels.seekLeft), ready.tape⟩ := by
      rw [← hEntry]
    obtain ⟨call, hCall, hState, hFrame, hBlank⟩ :=
      run_clockedPrefixCall D k hTime C labels layout rules request hWindow hFrame hBlank
    have hNext : inv rest (C.compile.run (prep + call) cfg) := by
      rw [Machine.run_add]
      change inv rest (C.compile.run call ready)
      rw [hEntryCfg]
      exact hReady _ hState hFrame hBlank
    rw [hParameters request (List.mem_cons_self ..)] at hCall
    obtain ⟨later, hLater, hFinal⟩ := ih
      (fun r hr ↦ hParameters r (List.mem_cons_of_mem _ hr))
      (fun r pending suffix ↦ hPrepare r pending (suffix.trans (List.suffix_cons request rest)))
      _ hNext
    refine ⟨prep + call + later, ?_, ?_⟩
    · rw [List.length_cons, Nat.succ_mul]
      omega
    · rwa [Machine.run_add]

/-- The part of the row budget spent inside prepared calls fits the exact
one-way clock once the gate threshold denominator is large enough. -/
theorem eventually_mergeRowCallBound_magnification (k : Nat) :
    ∃ denominator₀ > 0, ∀ denominator ≥ denominator₀, ∃ arity₀, ∀ n ≥ arity₀,
      2 ^ n * mergeRowCallBound k (n + magnificationGateCap denominator n) ≤
        magnificationTime (2 ^ n) :=
  eventually_magnification_clock (mergeRowCallBound_polynomiallyBounded k)

end PvsNP.MCSP
