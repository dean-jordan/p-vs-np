module

public import PvsNP.TuringMachine.TrackCall.Controller
public import PvsNP.TuringMachine.TrackCall.Rewind
public import PvsNP.TuringMachine.TrackCall.Simulation

import Mathlib.Data.Nat.Find

/-! # A returning call with a bound in physical Cook transitions -/

@[expose] public section

namespace PvsNP.TrackCall

open Turing

variable {α : Type} (D : Machine α) (ρ : Type) [Finite ρ] [Inhabited ρ]

/-- Enter the returning call with its head at the prepared origin. -/
def entry (tape : (machine D ρ).Tape) : (machine D ρ).Config :=
  ⟨.inl (executing D.initial true), tape⟩

/-- A returning call preserves scratch cells whose distance from the origin
is at least the child's clock bound. -/
theorem runReturning_preserving_outside (input : List α) (protectedTape : Tape ρ)
    (tape : (machine D ρ).Tape)
    (hScratch : scratch D ρ tape = (D.start input).tape)
    (hFrame : FrameAt D ρ tape protectedTape 0)
    {bound : Nat} (hTime : D.HaltsWithin input bound) :
    ∃ (answer : Bool) (ticks : Nat), ticks ≤ 2 * bound + 2 ∧
      let final := (machine D ρ).run ticks (entry D ρ tape)
      final.state = .inr answer ∧ FrameAt D ρ final.tape protectedTape 0 ∧
      (answer = true ↔ D.Accepts input) ∧
      ∀ i : Int, bound ≤ i.natAbs →
        (@Tape.nth _ (machine D ρ).tapeInhabited final.tape i).1 =
          (@Tape.nth _ (machine D ρ).tapeInhabited tape i).1 := by
  obtain ⟨t, ht, answer, hHalt, hRunning⟩ := (D.haltsWithin_iff_firstHalt input bound).mp hTime
  let middle := (machine D ρ).run t (entry D ρ tape)
  obtain ⟨pos, side, hState, _, hMiddleFrame, hSide, hPosition, hMiddleOutside⟩ :=
    simulate_run_preserving_outside D ρ t (D.start input) tape protectedTape 0 true
      hScratch hFrame (sideAt_zero _) hRunning
  change middle.state = .inl (phaseState (D.run t (D.start input)).state side) at hState
  rw [hHalt] at hState
  have hMiddle : middle = (⟨.inl (rewinding answer side), middle.tape⟩ :
      (machine D ρ).Config) := by
    change middle = ⟨.inl (phaseState (.inr answer) side), middle.tape⟩
    rw [← hState]
  have hFrame' : FrameAt D ρ middle.tape protectedTape pos := hMiddleFrame
  have hReturned : ((machine D ρ).run (pos.natAbs + 2) middle).state = .inr answer ∧
      FrameAt D ρ ((machine D ρ).run (pos.natAbs + 2) middle).tape protectedTape 0 := by
    exact hMiddle.symm ▸ rewind_run D ρ answer side hFrame' hSide
  have hAccept : answer = true ↔ D.Accepts input := by
    have hLocal : D.HaltsWithin input t := ⟨t, Nat.le_refl _, answer, hHalt⟩
    rw [D.accepts_iff_at_bound input hLocal, hHalt, Sum.inr.injEq]
  refine ⟨answer, t + (pos.natAbs + 2), by omega, ?_, ?_, hAccept, ?_⟩
  · rw [Machine.run_add]
    exact hReturned.1
  · rw [Machine.run_add]
    exact hReturned.2
  · intro i hi
    rw [Machine.run_add]
    have hRewind :
        @Tape.nth _ (machine D ρ).tapeInhabited
            ((machine D ρ).run (pos.natAbs + 2) middle).tape i =
          @Tape.nth _ (machine D ρ).tapeInhabited middle.tape (i - pos) :=
      hMiddle.symm ▸ rewind_run_nth D ρ answer side hFrame' hSide i
    have hOutside := hMiddleOutside i (by omega)
    rw [Int.sub_zero] at hOutside
    exact (congrArg Prod.fst hRewind).trans hOutside

/-- A prepared query incurs one physical tick per child tick, at most as many
ticks to rewind, and two final ticks to halt at the origin. -/
theorem runReturning (input : List α) (protectedTape : Tape ρ) (tape : (machine D ρ).Tape)
    (hScratch : scratch D ρ tape = (D.start input).tape)
    (hFrame : FrameAt D ρ tape protectedTape 0)
    {bound : Nat} (hTime : D.HaltsWithin input bound) :
    ∃ (answer : Bool) (ticks : Nat), ticks ≤ 2 * bound + 2 ∧
      ((machine D ρ).run ticks (entry D ρ tape)).state = .inr answer ∧
      FrameAt D ρ ((machine D ρ).run ticks (entry D ρ tape)).tape protectedTape 0 ∧
      (answer = true ↔ D.Accepts input) := by
  obtain ⟨answer, ticks, hTicks, hHalt, hFinal, hAnswer, _⟩ :=
    runReturning_preserving_outside D ρ input protectedTape tape hScratch hFrame hTime
  exact ⟨answer, ticks, hTicks, hHalt, hFinal, hAnswer⟩

/-- Prepare a query on a scratch track with an arbitrary protected tape. -/
theorem runReturning_prepared (input : List α) (protectedTape : Tape ρ)
    {bound : Nat} (hTime : D.HaltsWithin input bound) :
    ∃ (answer : Bool) (ticks : Nat), ticks ≤ 2 * bound + 2 ∧
      ((machine D ρ).run ticks (entry D ρ (prepareTape D ρ input protectedTape))).state =
        .inr answer ∧
      FrameAt D ρ
        ((machine D ρ).run ticks (entry D ρ (prepareTape D ρ input protectedTape))).tape
        protectedTape 0 ∧
      (answer = true ↔ D.Accepts input) :=
  runReturning D ρ input protectedTape _ (scratch_prepareTape D ρ input protectedTape)
    (frameAt_prepareTape D ρ input protectedTape) hTime

private theorem firstReturningHalt (cfg : (machine D ρ).Config) (t : Nat) (answer : Bool)
    (hHalt : ((machine D ρ).run t cfg).state = .inr answer) :
    ∃ u ≤ t, ((machine D ρ).run u cfg) = (machine D ρ).run t cfg ∧
      ∀ j < u, ∃ q, ((machine D ρ).run j cfg).state = .inl q := by
  classical
  have hExists : ∃ u, ((machine D ρ).run u cfg).state = .inr answer := ⟨t, hHalt⟩
  have hFirst := Nat.find_spec hExists
  have hLe := Nat.find_min' hExists hHalt
  refine ⟨Nat.find hExists, hLe, ((machine D ρ).run_eq_of_halted_le cfg hLe hFirst).symm, ?_⟩
  intro j hj
  cases hEarly : ((machine D ρ).run j cfg).state with
  | inl q => exact ⟨q, rfl⟩
  | inr early =>
    have hSame := (machine D ρ).halt_result_unique cfg hEarly hFirst
    subst early
    exact (Nat.not_le_of_gt hj (Nat.find_min' hExists hEarly)).elim

namespace Controller

variable {D ρ} (C : Controller D ρ)

/-- The linked call preserves every protected cell and the scratch cells
whose distance from the origin is at least the child's clock bound. -/
theorem run_call_preserving_outside (reject accept : C.State)
    (input : List α) (protectedTape : Tape ρ)
    (tape : (machine D ρ).Tape) (hScratch : scratch D ρ tape = (D.start input).tape)
    (hFrame : FrameAt D ρ tape protectedTape 0)
    {bound : Nat} (hTime : D.HaltsWithin input bound) :
    ∃ (answer : Bool) (ticks : Nat), ticks ≤ 2 * bound + 2 ∧
      let final := C.compile.run ticks (C.embedCall reject accept (entry D ρ tape))
      final.state = .inl (.inl (C.resume reject accept answer)) ∧
      FrameAt D ρ final.tape protectedTape 0 ∧ (answer = true ↔ D.Accepts input) ∧
      ∀ i : Int, bound ≤ i.natAbs →
        (@Tape.nth _ C.compile.tapeInhabited final.tape i).1 =
          (@Tape.nth _ (machine D ρ).tapeInhabited tape i).1 := by
  obtain ⟨answer, t, ht, hHalt, hReturned, hAnswer, hOutside⟩ :=
    runReturning_preserving_outside D ρ input protectedTape tape hScratch hFrame hTime
  obtain ⟨u, hu, hRun, hBefore⟩ := firstReturningHalt D ρ _ t answer hHalt
  refine ⟨answer, u, hu.trans ht, ?_⟩
  rw [C.run_embedCall reject accept _ u hBefore, hRun]
  exact ⟨by simp only [embedCall, hHalt, fromCall], hReturned, hAnswer, hOutside⟩

/-- In a compiled controller, a call returns to the selected label at the
marked origin, retaining every protected cell. -/
theorem run_call (reject accept : C.State) (input : List α) (protectedTape : Tape ρ)
    (tape : (machine D ρ).Tape) (hScratch : scratch D ρ tape = (D.start input).tape)
    (hFrame : FrameAt D ρ tape protectedTape 0)
    {bound : Nat} (hTime : D.HaltsWithin input bound) :
    ∃ (answer : Bool) (ticks : Nat), ticks ≤ 2 * bound + 2 ∧
      let final := C.compile.run ticks (C.embedCall reject accept (entry D ρ tape))
      final.state = .inl (.inl (C.resume reject accept answer)) ∧
      FrameAt D ρ final.tape protectedTape 0 ∧ (answer = true ↔ D.Accepts input) := by
  obtain ⟨answer, ticks, hTicks, hState, hFinal, hAnswer, _⟩ :=
    C.run_call_preserving_outside reject accept input protectedTape tape hScratch hFrame hTime
  exact ⟨answer, ticks, hTicks, hState, hFinal, hAnswer⟩

theorem run_call_prepared (reject accept : C.State) (input : List α) (protectedTape : Tape ρ)
    {bound : Nat} (hTime : D.HaltsWithin input bound) :
    ∃ (answer : Bool) (ticks : Nat), ticks ≤ 2 * bound + 2 ∧
      let final := C.compile.run ticks
        (C.embedCall reject accept (entry D ρ (prepareTape D ρ input protectedTape)))
      final.state = .inl (.inl (C.resume reject accept answer)) ∧
      FrameAt D ρ final.tape protectedTape 0 ∧ (answer = true ↔ D.Accepts input) :=
  C.run_call reject accept input protectedTape _ (scratch_prepareTape D ρ input protectedTape)
    (frameAt_prepareTape D ρ input protectedTape) hTime

/-- Count the controller's call instruction as well as the complete child
computation and return. The call instruction must leave a prepared query. -/
theorem run_call_of_transition (q reject accept : C.State) (input : List α)
    (protectedTape : Tape ρ) (tape : C.compile.Tape) (cell : Symbol D ρ) (dir : Dir)
    {bound : Nat} (hTime : D.HaltsWithin input bound) :
    let _ := C.compile.tapeInhabited
    C.transition q tape.head = (.call reject accept, cell, dir) →
    let prepared := (tape.write cell).move dir
    scratch D ρ prepared = (D.start input).tape →
    FrameAt D ρ prepared protectedTape 0 →
    ∃ (answer : Bool) (ticks : Nat), ticks ≤ 2 * bound + 3 ∧
      let final := C.compile.run ticks ⟨.inl (.inl q), tape⟩
      final.state = .inl (.inl (C.resume reject accept answer)) ∧
      FrameAt D ρ final.tape protectedTape 0 ∧ (answer = true ↔ D.Accepts input) := by
  dsimp only
  intro hTick hScratch hFrame
  obtain ⟨answer, ticks, hTicks, hReturn⟩ :=
    C.run_call reject accept input protectedTape _ hScratch hFrame hTime
  refine ⟨answer, ticks + 1, by omega, ?_⟩
  rw [Machine.run_succ, C.tick_controller q tape hTick]
  exact hReturn

end Controller

end PvsNP.TrackCall
