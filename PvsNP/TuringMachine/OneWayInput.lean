module

public import PvsNP.TuringMachine.Sweeps

import Mathlib.Basic.Finite.Sum

/-! # Deterministic machines with a one-way input and a separate work tape

The input head can stay or move right. Its view is an optional bit, with
`none` at and beyond the right end of the input. The work head can move
in either direction or stay. It starts on a blank two-way work tape,
independent of the input head. Each transition, including the one that
halts, takes one tick.
-/

@[expose] public section

namespace PvsNP

/-- The two possible actions on the read-only input head. -/
inductive OneWayInputMove where
  | stay | advance

/-- The remainder itself is read-only. A move can only discard its first bit. -/
def OneWayInputMove.apply (remaining : List Bool) : OneWayInputMove → List Bool
  | .stay => remaining
  | .advance => remaining.tail

/-- A finite-state machine with an independent one-way binary input head and
one two-way writable work head. The work move `none` holds the work head still. -/
structure OneWayMachine where
  State : Type
  Symbol : Type
  stateFinite : Finite State
  symbolFinite : Finite Symbol
  initial : State
  blank : Symbol
  transition : State → Option Bool → Symbol →
    (State ⊕ Bool) × Symbol × Option Turing.Dir × OneWayInputMove

namespace OneWayMachine

variable (M : OneWayMachine)

abbrev tapeInhabited : Inhabited M.Symbol := ⟨M.blank⟩

abbrev Tape := @Turing.Tape M.Symbol M.tapeInhabited

/-- A halted state records its answer. Only the unread input suffix is observable. -/
structure Config where
  state : M.State ⊕ Bool
  remaining : List Bool
  tape : M.Tape

/-- At the start there are no work-tape symbols and the whole input is unread. -/
def start (word : List Bool) : M.Config :=
  ⟨.inl M.initial, word, @Turing.Tape.mk₁ _ M.tapeInhabited []⟩

/-- Perform a transition. A halted configuration is fixed under later clock ticks. -/
def tick (cfg : M.Config) : M.Config :=
  letI := M.tapeInhabited
  match cfg.state with
  | .inr _ => cfg
  | .inl q =>
    let (next, written, workMove, inputMove) := M.transition q cfg.remaining.head? cfg.tape.head
    let tape := cfg.tape.write written
    ⟨next, inputMove.apply cfg.remaining, workMove.elim tape (fun dir ↦ Turing.Tape.move dir tape)⟩

/-- Expand a running transition whose work head moves in the specified direction. -/
theorem tick_running_move (q : M.State) (input : List Bool) (tape : M.Tape)
    {next : M.State ⊕ Bool} {written : M.Symbol} {dir : Turing.Dir}
    {read : OneWayInputMove}
    (h : M.transition q input.head? (@Turing.Tape.head _ M.tapeInhabited tape) =
      (next, written, some dir, read)) :
    M.tick ⟨.inl q, input, tape⟩ =
      ⟨next, read.apply input, @Turing.Tape.move _ M.tapeInhabited dir
        (@Turing.Tape.write _ M.tapeInhabited written tape)⟩ := by
  simp only [tick, h, Option.elim_some]

/-- Iterate the counted transition. -/
def run : Nat → M.Config → M.Config
  | 0, cfg => cfg
  | ticks + 1, cfg => run ticks (M.tick cfg)

@[simp] theorem run_zero (cfg : M.Config) : M.run 0 cfg = cfg := rfl

theorem run_succ (ticks : Nat) (cfg : M.Config) :
    M.run (ticks + 1) cfg = M.run ticks (M.tick cfg) := rfl

theorem run_add (first later : Nat) (cfg : M.Config) :
    M.run (first + later) cfg = M.run later (M.run first cfg) := by
  induction first generalizing cfg with
  | zero => rw [Nat.zero_add, run_zero]
  | succ k ih => rw [Nat.succ_add, run_succ, ih, run_succ]

@[simp] theorem tick_halted (answer : Bool) (input : List Bool) (tape : M.Tape) :
    M.tick ⟨.inr answer, input, tape⟩ = ⟨.inr answer, input, tape⟩ := rfl

theorem run_eq_of_halted (ticks : Nat) (cfg : M.Config) {answer : Bool}
    (h : cfg.state = .inr answer) : M.run ticks cfg = cfg := by
  obtain ⟨state, input, tape⟩ := cfg
  change state = .inr answer at h
  subst state
  induction ticks with
  | zero => rfl
  | succ k ih => rw [run_succ, tick_halted, ih]

theorem run_eq_of_halted_le (cfg : M.Config) {first later : Nat} {answer : Bool}
    (hTicks : first ≤ later) (h : (M.run first cfg).state = .inr answer) :
    M.run later cfg = M.run first cfg := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hTicks
  rw [run_add, M.run_eq_of_halted extra _ h]

/-- In a run of `ticks`, the unread input is obtained by advancing at most `ticks` times. -/
theorem run_input_suffix (ticks : Nat) (cfg : M.Config) :
    ∃ advance ≤ ticks, (M.run ticks cfg).remaining = cfg.remaining.drop advance := by
  have hStep (c : M.Config) : ∃ advance ≤ 1,
      (M.tick c).remaining = c.remaining.drop advance := by
    obtain ⟨state, input, tape⟩ := c
    cases state with
    | inr answer => exact ⟨0, by decide, rfl⟩
    | inl q =>
      rcases h : M.transition q input.head? (@Turing.Tape.head _ M.tapeInhabited tape)
        with ⟨next, written, work, move⟩
      cases move with
      | stay => exact ⟨0, by decide, by simp [tick, h, OneWayInputMove.apply]⟩
      | advance => exact ⟨1, by decide, by simp [tick, h, OneWayInputMove.apply]⟩
  induction ticks generalizing cfg with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ k ih =>
    obtain ⟨first, hFirst, hRead⟩ := hStep cfg
    obtain ⟨later, hLater, hRest⟩ := ih (M.tick cfg)
    refine ⟨first + later, by omega, ?_⟩
    rw [run_succ, hRest, hRead, List.drop_drop]

/-- Acceptance means some finite run reaches the accepting state. -/
def Accepts (word : List Bool) : Prop := ∃ ticks, (M.run ticks (M.start word)).state = .inr true

/-- A bound counts the transitions to either halting state. -/
def HaltsWithin (word : List Bool) (bound : Nat) : Prop :=
  ∃ ticks ≤ bound, ∃ answer, (M.run ticks (M.start word)).state = .inr answer

theorem haltsWithin_iff (word : List Bool) (bound : Nat) :
    M.HaltsWithin word bound ↔ ∃ answer, (M.run bound (M.start word)).state = .inr answer := by
  constructor
  · rintro ⟨ticks, hTicks, answer, hHalt⟩
    exact ⟨answer, (congrArg Config.state (M.run_eq_of_halted_le _ hTicks hHalt)).trans hHalt⟩
  · rintro ⟨answer, hHalt⟩
    exact ⟨bound, le_rfl, answer, hHalt⟩

/-- Totality can be supplied by a separate time bound. -/
def Decides (language : Set (List Bool)) : Prop := ∀ word, word ∈ language ↔ M.Accepts word

/-- The given function bounds all computations on inputs of the specified length. -/
def TimeBounded (clock : Nat → Nat) : Prop := ∀ word, M.HaltsWithin word (clock word.length)

/-- Deterministic time on one work tape and a separate one-way input tape.
The multiplicative constant may also cover a constant additive overhead. -/
def DTIME (clock : Nat → Nat) : Set (Set (List Bool)) :=
  {language | ∃ M : OneWayMachine, M.Decides language ∧
    ∃ scale : Nat, M.TimeBounded (fun length ↦ scale * (clock length + 1))}

end OneWayMachine

namespace Machine

open Turing

/-- The input loader copies, rewinds, then runs the original Cook machine. -/
inductive OneWayPhase (Q : Type) where
  | copy | rewind | simulate (state : Q)

private def oneWayPhaseCode {Q : Type} : OneWayPhase Q → Bool ⊕ Q
  | .copy => .inl false
  | .rewind => .inl true
  | .simulate q => .inr q

instance {Q : Type} [Finite Q] : Finite (OneWayPhase Q) :=
  Finite.of_injective oneWayPhaseCode (by
    intro a b h
    cases a <;> cases b <;> simp_all [oneWayPhaseCode])

variable (M : Machine Bool) [DecidableEq M.Symbol]

/-- Copy the input once to the work tape and then simulate the Cook machine.
The copied symbols are nonblank, so the blank immediately to their left
identifies the starting position during the rewind. -/
@[reducible] def withOneWayInput : OneWayMachine := by
  let _ : Finite M.State := M.stateFinite
  exact {
    State := OneWayPhase M.State
    Symbol := M.Symbol
    stateFinite := inferInstance
    symbolFinite := M.symbolFinite
    initial := .copy
    blank := M.blank
    transition := fun phase bit scanned ↦ match phase with
      | .copy => match bit with
        | some b => (.inl .copy, M.input b, some .right, .advance)
        | none => (.inl .rewind, scanned, some .left, .stay)
      | .rewind =>
        if scanned = M.blank then (.inl (.simulate M.initial), scanned, some .right, .stay)
        else (.inl .rewind, scanned, some .left, .stay)
      | .simulate q =>
        let (next, written, dir) := M.transition q scanned
        (next.map .simulate id, written, some dir, .stay) }

/-- The running Cook work tape can be installed in the simulation phase. -/
def oneWayConfig (cfg : M.Config) (remaining : List Bool) : M.withOneWayInput.Config :=
  ⟨cfg.state.map .simulate id, remaining, cfg.tape⟩

@[simp] theorem oneWayConfig_halted_iff (cfg : M.Config) (remaining : List Bool) (answer : Bool) :
    (M.oneWayConfig cfg remaining).state = .inr answer ↔ cfg.state = .inr answer := by
  cases hState : cfg.state <;> simp [oneWayConfig, hState]

/-- Once the loader finishes, a work-tape transition is exactly a Cook transition. -/
theorem withOneWayInput_tick_simulate (cfg : M.Config) (remaining : List Bool) :
    M.withOneWayInput.tick (M.oneWayConfig cfg remaining) =
      M.oneWayConfig (M.tick cfg) remaining := by
  obtain ⟨state, tape⟩ := cfg
  cases state with
  | inr answer => rfl
  | inl q =>
    rcases h : M.transition q (@Tape.head _ M.tapeInhabited tape) with ⟨next, written, dir⟩
    simp only [oneWayConfig, OneWayMachine.tick, tick, withOneWayInput, Sum.map_inl, h,
      Option.elim_some, OneWayInputMove.apply]

/-- The Cook simulation preserves the exact work configuration and unread input. -/
theorem withOneWayInput_run_simulate (ticks : Nat) (cfg : M.Config) (remaining : List Bool) :
    M.withOneWayInput.run ticks (M.oneWayConfig cfg remaining) =
      M.oneWayConfig (M.run ticks cfg) remaining := by
  induction ticks generalizing cfg with
  | zero => rfl
  | succ k ih =>
    rw [OneWayMachine.run_succ, withOneWayInput_tick_simulate, Machine.run_succ, ih]

private theorem withOneWayInput_run_copy (input : List Bool) (left : List M.Symbol) :
    M.withOneWayInput.run input.length ⟨.inl .copy, input, M.tapeFromLists left []⟩ =
      ⟨.inl .copy, [], M.tapeFromLists ((input.map M.input).reverse ++ left) []⟩ := by
  induction input generalizing left with
  | nil => rfl
  | cons bit input ih =>
    simp only [List.length_cons, OneWayMachine.run_succ, OneWayMachine.tick, withOneWayInput,
      List.head?_cons, OneWayInputMove.apply, List.tail_cons, Option.elim_some,
      write_tapeFromLists_nil, move_tapeFromLists_right_cons]
    simpa only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
      using ih (M.input bit :: left)

private theorem withOneWayInput_run_rewind (crossed left right : List M.Symbol)
    (nonblank : ∀ s ∈ crossed, s ≠ M.blank) :
    M.withOneWayInput.run crossed.length
      ⟨.inl .rewind, [], @Tape.move _ M.tapeInhabited .left
        (M.tapeFromLists (crossed ++ left) right)⟩ =
      ⟨.inl .rewind, [], @Tape.move _ M.tapeInhabited .left
        (M.tapeFromLists left (crossed.reverse ++ right))⟩ := by
  induction crossed generalizing right with
  | nil => rfl
  | cons sym tail ih =>
    have hSymbol := nonblank sym (List.mem_cons_self ..)
    have hMove : M.withOneWayInput.transition .rewind none sym =
        (.inl .rewind, sym, some .left, .stay) := by
      change (if sym = M.blank then
        ((.inl (.simulate M.initial), sym, some .right, .stay) :
          (OneWayPhase M.State ⊕ Bool) × M.Symbol × Option Dir × OneWayInputMove)
        else (.inl .rewind, sym, some .left, .stay)) = _
      exact ite_eq_right hSymbol
    have hStep : M.withOneWayInput.tick
        ⟨.inl .rewind, [], M.tapeFromLists (tail ++ left) (sym :: right)⟩ =
        ⟨.inl .rewind, [], @Tape.move _ M.tapeInhabited .left
          (M.tapeFromLists (tail ++ left) (sym :: right))⟩ := by
      have hRun := M.withOneWayInput.tick_running_move .rewind []
        (M.tapeFromLists (tail ++ left) (sym :: right)) hMove
      simpa only [OneWayInputMove.apply, write_tapeFromLists_cons] using hRun
    simp only [List.length_cons, List.cons_append, OneWayMachine.run_succ,
      move_tapeFromLists_left_cons, hStep]
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
      ih (sym :: right) (fun s hs ↦ nonblank s (List.mem_cons_of_mem sym hs))

/-- Starting with a blank work tape, load the Cook initial configuration in
exactly two ticks per input symbol plus two turning ticks. -/
theorem withOneWayInput_load (input : List Bool) :
    M.withOneWayInput.run (2 * input.length + 2) (M.withOneWayInput.start input) =
      M.oneWayConfig (M.start input) [] := by
  let symbols := input.map M.input
  have hLength : symbols.reverse.length = input.length := by
    simp only [symbols, List.length_reverse, List.length_map]
  have hAll : ∀ s ∈ symbols.reverse, s ≠ M.blank := by
    intro s hs
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hs)
    exact M.input_ne_blank b
  have hCopy := M.withOneWayInput_run_copy input []
  have hRewind := M.withOneWayInput_run_rewind symbols.reverse [] [] hAll
  rw [hLength, List.append_nil, List.reverse_reverse, List.append_nil] at hRewind
  have hTurn : M.withOneWayInput.tick ⟨.inl .copy, [], M.tapeFromLists symbols.reverse []⟩ =
      ⟨.inl .rewind, [], @Tape.move _ M.tapeInhabited .left
        (M.tapeFromLists symbols.reverse [])⟩ := by
    simp only [OneWayMachine.tick, withOneWayInput, List.head?_nil, OneWayInputMove.apply,
      Tape.write_self, Option.elim_some]
  have hStart : M.withOneWayInput.tick ⟨.inl .rewind, [], @Tape.move _ M.tapeInhabited .left
      (M.tapeFromLists [] symbols)⟩ = M.oneWayConfig (M.start input) [] := by
    have hBlank : @Tape.head _ M.tapeInhabited
        (@Tape.move _ M.tapeInhabited .left (M.tapeFromLists [] symbols)) = M.blank := by
      rw [move_tapeFromLists_left_nil, head_tapeFromLists_cons]
    let t := @Tape.move _ M.tapeInhabited .left (M.tapeFromLists [] symbols)
    have hWrite : @Tape.write _ M.tapeInhabited M.blank t = t :=
      (congrArg (fun b ↦ @Tape.write _ M.tapeInhabited b t) hBlank).symm.trans
        (@Tape.write_self _ M.tapeInhabited t)
    simp only [OneWayMachine.tick, withOneWayInput, hBlank, ite_true, OneWayInputMove.apply,
      Option.elim_some]
    rw [show @Tape.write _ M.tapeInhabited M.blank
      (@Tape.move _ M.tapeInhabited .left (M.tapeFromLists [] symbols)) = t from hWrite]
    unfold t
    rw [@Tape.move_left_right _ M.tapeInhabited (M.tapeFromLists [] symbols)]
    rfl
  have hTicks : 2 * input.length + 2 = (input.length + 1) + (input.length + 1) := by omega
  have hLoadStart : M.withOneWayInput.start input =
      ⟨.inl .copy, input, M.tapeFromLists [] []⟩ := rfl
  have hCopyTurn : M.withOneWayInput.run (input.length + 1) (M.withOneWayInput.start input) =
      ⟨.inl .rewind, [], @Tape.move _ M.tapeInhabited .left
        (M.tapeFromLists symbols.reverse [])⟩ := by
    rw [OneWayMachine.run_add, hLoadStart, hCopy, List.append_nil]
    exact hTurn
  rw [hTicks, OneWayMachine.run_add, hCopyTurn, OneWayMachine.run_add, hRewind]
  exact hStart

/-- The exact simulation clock is the original clock plus the linear loading overhead. -/
theorem withOneWayInput_run (input : List Bool) (ticks : Nat) :
    M.withOneWayInput.run (2 * input.length + 2 + ticks) (M.withOneWayInput.start input) =
      M.oneWayConfig (M.run ticks (M.start input)) [] := by
  rw [OneWayMachine.run_add, withOneWayInput_load, withOneWayInput_run_simulate]

/-- Once the cost of loading is included, the two clocks bound exactly the same halts. -/
theorem withOneWayInput_haltsWithin_iff (input : List Bool) (bound : Nat) :
    M.withOneWayInput.HaltsWithin input (2 * input.length + 2 + bound) ↔
      M.HaltsWithin input bound := by
  rw [OneWayMachine.haltsWithin_iff, M.haltsWithin_iff, withOneWayInput_run]
  constructor
  · rintro ⟨answer, h⟩
    exact ⟨answer, (M.oneWayConfig_halted_iff _ _ _).mp h⟩
  · rintro ⟨answer, h⟩
    exact ⟨answer, (M.oneWayConfig_halted_iff _ _ _).mpr h⟩

/-- A bounded halt in the Cook model has the linear loading overhead in the one-way model. -/
theorem withOneWayInput_haltsWithin (input : List Bool) {bound : Nat}
    (h : M.HaltsWithin input bound) :
    M.withOneWayInput.HaltsWithin input (2 * input.length + 2 + bound) :=
  (M.withOneWayInput_haltsWithin_iff input bound).mpr h

/-- The loader never creates an accepting state, and the simulated answer is preserved. -/
theorem withOneWayInput_accepts_iff (input : List Bool) :
    M.withOneWayInput.Accepts input ↔ M.Accepts input := by
  let wrapped := M.withOneWayInput
  let start := wrapped.start input
  let loading := 2 * input.length + 2
  constructor
  · rintro ⟨ticks, h⟩
    have hLe : loading ≤ ticks := by
      by_cases hTime : loading ≤ ticks
      · exact hTime
      · have hFreeze := wrapped.run_eq_of_halted_le start (show ticks ≤ loading by omega) h
        rw [show wrapped.run loading start = M.oneWayConfig (M.start input) [] from
          M.withOneWayInput_load input] at hFreeze
        have contra := congrArg OneWayMachine.Config.state hFreeze
        rw [h] at contra
        have hEarly := (M.oneWayConfig_halted_iff _ _ _).mp contra
        contradiction
    obtain ⟨rest, hTicks⟩ := Nat.exists_eq_add_of_le hLe
    rw [hTicks, show wrapped.run (loading + rest) start = _
      from M.withOneWayInput_run input rest] at h
    exact ⟨rest, (M.oneWayConfig_halted_iff _ _ _).mp h⟩
  · rintro ⟨ticks, h⟩
    refine ⟨loading + ticks, ?_⟩
    rw [withOneWayInput_run]
    exact (M.oneWayConfig_halted_iff _ _ _).mpr h

/-- The exact accepted language of a Cook machine is preserved. -/
theorem withOneWayInput_decides {language : Set (List Bool)} (h : M.Decides language) :
    M.withOneWayInput.Decides language :=
  fun input ↦ (h input).trans (M.withOneWayInput_accepts_iff input).symm

omit [DecidableEq M.Symbol] in
/-- Every Cook machine admits the one-way embedding, including when no
particular executable equality test for the finite alphabet is supplied. -/
theorem exists_withOneWayInput :
    ∃ W : OneWayMachine, (∀ input, W.Accepts input ↔ M.Accepts input) ∧
      ∀ input bound, W.HaltsWithin input (2 * input.length + 2 + bound) ↔
        M.HaltsWithin input bound := by
  classical
  exact ⟨M.withOneWayInput, M.withOneWayInput_accepts_iff, M.withOneWayInput_haltsWithin_iff⟩

end Machine

end PvsNP
