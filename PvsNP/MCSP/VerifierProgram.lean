module

public import PvsNP.MCSP.TraceChecker
public import PvsNP.MCSP.TraceExtentDispatch
public import PvsNP.TuringMachine.Registers.Decision

/-! # The counted verifier program needed for prefix feasibility -/

public section

namespace PvsNP.MCSP

open RegisterMachine

/-- The exact packed violation checker can be implemented by a counted register program.
Polynomial simulation and the two bounded projections then put prefix feasibility in `P`
under `P = NP`. The register specification is over all words, including malformed pairs. -/
theorem mergePrefixLanguage_mem_P_of_p_eq_np_of_register_run
    {R L : Type} [Finite R] [Finite L] [DecidableEq R] (entry : L)
    (program : L → Instruction R L) {bound : Nat → Nat} (hBound : PolynomiallyBounded bound)
    (hRun : ∀ word, ∃ steps ≤ bound word.length, ∃ cfg,
      run program word steps (Config.initial entry) = some cfg ∧ cfg.pc = none ∧
        cfg.output = [checkPackedMergePrefixViolation word]) (hCollapse : P = NP) :
    MergePrefixLanguage ∈ P := by
  have hChecking : {word : BinaryWord | checkPackedMergePrefixViolation word = true} =
      packedCheckingLanguage MergePrefixViolation := by
    ext word
    exact checkPackedMergePrefixViolation_eq_true_iff word
  exact mergePrefixLanguage_mem_P_of_p_eq_np hCollapse
    (hChecking ▸ mem_P_of_boolean_run entry program hBound hRun)

/-- A polynomial register checker for certified wire values suffices for the same collapse. -/
theorem mergePrefixLanguage_mem_P_of_trace_register_run
    {R L : Type} [Finite R] [Finite L] [DecidableEq R] (entry : L)
    (program : L → Instruction R L) (accepts : BinaryWord → Bool)
    {bound : Nat → Nat} (hBound : PolynomiallyBounded bound)
    (hCheck : ∀ word, accepts word = true ↔ word ∈ packedCheckingLanguage MergePrefixTraceViolation)
    (hRun : ∀ word, ∃ steps ≤ bound word.length, ∃ cfg,
      run program word steps (Config.initial entry) = some cfg ∧ cfg.pc = none ∧
        cfg.output = [accepts word]) (hCollapse : P = NP) : MergePrefixLanguage ∈ P := by
  have hChecking : {word : BinaryWord | accepts word = true} =
      packedCheckingLanguage MergePrefixTraceViolation := by
    ext word
    exact hCheck word
  exact mergePrefixLanguage_mem_P_of_trace_checker hCollapse
    (hChecking ▸ mem_P_of_boolean_run entry program hBound hRun)

/-- The counted program can target the exact executable checker on every binary word. -/
theorem mergePrefixLanguage_mem_P_of_trace_checker_run
    {R L : Type} [Finite R] [Finite L] [DecidableEq R] (entry : L)
    (program : L → Instruction R L) {bound : Nat → Nat} (hBound : PolynomiallyBounded bound)
    (hRun : ∀ word, ∃ steps ≤ bound word.length, ∃ cfg,
      run program word steps (Config.initial entry) = some cfg ∧ cfg.pc = none ∧
        cfg.output = [checkPackedMergePrefixTraceViolation word]) (hCollapse : P = NP) :
    MergePrefixLanguage ∈ P :=
  mergePrefixLanguage_mem_P_of_trace_register_run entry program checkPackedMergePrefixTraceViolation
    hBound checkPackedMergePrefixTraceViolation_eq_true_iff hRun hCollapse

/-- The remaining bounded run need only handle the successful shape branch.
The front end supplies an exact answer before it enters that branch on all other inputs. -/
theorem mergePrefixLanguage_mem_P_of_traceFront_continuation
    {R : Type} [Finite R] [DecidableEq R]
    (headers : TraceHeaderLane → R) (extents : TraceExtentLane → R)
    (hHeaders : Function.Injective headers) (hExtents : Function.Injective extents)
    (hLink : TraceExtentLink headers extents)
    (hSeparate : ∀ lane ∈ extentDispatchHeaderLanes, ∀ k, headers lane ≠ extents k)
    (hNewLanes : ∀ lane, lane ∉ traceExtentInputLanes → ∀ k, extents lane ≠ headers k)
    (continuation : Fragment R) {bound : Nat → Nat} (hBound : PolynomiallyBounded bound)
    (hNext : ∀ word, TraceFrontContinuation headers extents continuation word
      (fun _ ↦ 0) [] (bound word.length)) (hCollapse : P = NP) : MergePrefixLanguage ∈ P := by
  let front := traceFrontRegister headers extents continuation
  have hClock : PolynomiallyBounded (fun n ↦ traceFrontRegisterCost n (bound n) + 1) :=
    (traceFrontRegisterCost_polynomiallyBounded hBound).add (PolynomiallyBounded.const 1)
  refine mergePrefixLanguage_mem_P_of_trace_checker_run front.entry front.close hClock ?_ hCollapse
  intro word
  obtain ⟨ticks, hTicks, _, hRun⟩ := runsOutput_traceFrontRegister headers extents
    hHeaders hExtents hLink hSeparate hNewLanes continuation word (fun _ ↦ 0)
    (fun _ ↦ rfl) [] (bound word.length) (hNext word)
  exact ⟨ticks + 1, Nat.add_le_add_right hTicks 1, _, Fragment.run_close hRun rfl rfl, rfl, rfl⟩

end PvsNP.MCSP
