module

public import PvsNP.TuringMachine.Registers.Program
public import PvsNP.TuringMachine.Registers.Setup
public import PvsNP.TuringMachine.Registers.Increment
public import PvsNP.TuringMachine.Registers.Decrement
public import PvsNP.TuringMachine.Registers.Cursor
public import PvsNP.TuringMachine.Registers.ResetInput
public import PvsNP.TuringMachine.Registers.Output
public import PvsNP.TuringMachine.Registers.Finish

import Mathlib.Basic.Finite.Prod
import Mathlib.Basic.Finite.Sum
import Mathlib.Data.Fintype.Option

/-! # Finite control for register programs

At the home marker, the active label selects one register instruction.
The finite phases for that instruction drive the corresponding tape steps.
An input-read phase can also carry its result to the home marker.
-/

@[expose] public section

namespace PvsNP.RegisterMachine

open Turing

/-- The four states used to frame the input before the program starts. -/
inductive SetupPhase
  | entry | mark | scan | land

/-- The tape phases used by the instructions at any one program label. -/
inductive ControlPhase
  | active | inspect | scan | clear | rewind | land | alternateRead
  | rewindInput (result : Option Bool)
  | landInput (result : Option Bool)

private def setupCode : SetupPhase → Fin 4
  | .entry => 0
  | .mark => 1
  | .scan => 2
  | .land => 3

private def phaseCode : ControlPhase → Fin 9 × Option Bool
  | .active => (0, none)
  | .inspect => (1, none)
  | .scan => (2, none)
  | .clear => (3, none)
  | .rewind => (4, none)
  | .land => (5, none)
  | .alternateRead => (6, none)
  | .rewindInput result => (7, result)
  | .landInput result => (8, result)

instance : Finite SetupPhase := by
  apply Finite.of_injective setupCode
  intro a b h
  cases a <;> cases b <;> simp_all [setupCode]

instance : Finite ControlPhase := by
  apply Finite.of_injective phaseCode
  intro a b h
  cases a <;> cases b <;> simp_all [phaseCode]

/-- Setup states and the finite intermediate states of each program label. -/
abbrev ControlState (L : Type) := SetupPhase ⊕ (L × ControlPhase)

instance {L : Type} [Finite L] : Finite (ControlState L) := by
  unfold ControlState
  let _ : Finite (L × ControlPhase) := inferInstance
  infer_instance

namespace ControlState

variable {L : Type}

/-- A program label at its instruction boundary. -/
abbrev label (l : L) : ControlState L := .inr (l, .active)

/-- A phase within a program instruction. -/
abbrev phase (l : L) (p : ControlPhase) : ControlState L := .inr (l, p)

/-- The initial state of every compiled register program. -/
abbrev initial : ControlState L := .inl .entry

variable {R : Type}

abbrev Transition (R L : Type) := (ControlState L ⊕ Bool) × Symbol R × Dir

abbrev go (state : ControlState L) (symbol : Symbol R) (dir : Dir) : Transition R L :=
  (.inl state, symbol, dir)

abbrev reject (symbol : Symbol R) : Transition R L := (.inr false, symbol, .right)

def setupTransition (entry : L) : SetupPhase → Symbol R → Transition R L
  | .entry, a => go (.inl .mark) a .left
  | .mark, .blank => go (.inl .scan) .start .right
  | .scan, .bit b => go (.inl .scan) (.bit b) .right
  | .scan, .blank => go (.inl .land) .home .left
  | .land, .bit b => go (.label entry) (.bit b) .right
  | .land, .start => go (.label entry) .start .right
  | _, a => reject a

def incrementTransition [DecidableEq R] (label next : L) (lane : R) :
    ControlPhase → Symbol R → Transition R L
  | .active, .home => go (phase label .scan) .home .right
  | .scan, .track cell =>
    if cell lane then go (phase label .scan) (.track cell) .right
    else go (phase label .rewind) (.track (setTrack cell lane true)) .left
  | .scan, .blank =>
    go (phase label .rewind) (.track (setTrack (fun _ ↦ false) lane true)) .left
  | .rewind, .track cell => go (phase label .rewind) (.track cell) .left
  | .rewind, .home => go (phase label .land) .home .right
  | .land, .track cell => go (.label next) (.track cell) .left
  | _, a => reject a

def decrementTransition [DecidableEq R] (label zero next : L) (lane : R) :
    ControlPhase → Symbol R → Transition R L
  | .active, .home => go (phase label .inspect) .home .right
  | .inspect, .track cell =>
    if cell lane then go (phase label .scan) (.track cell) .right
    else go (.label zero) (.track cell) .left
  | .inspect, .blank => go (.label zero) .blank .left
  | .scan, .track cell =>
    if cell lane then go (phase label .scan) (.track cell) .right
    else go (phase label .clear) (.track cell) .left
  | .scan, .blank => go (phase label .clear) .blank .left
  | .clear, .track cell =>
    go (phase label .rewind) (.track (setTrack cell lane false)) .left
  | .rewind, .track cell => go (phase label .rewind) (.track cell) .left
  | .rewind, .home => go (phase label .land) .home .right
  | .land, .track cell => go (.label next) (.track cell) .left
  | _, a => reject a

def readTransition (label : L) (next : Option Bool → L) (first : Bool) :
    ControlPhase → Symbol R → Transition R L
  | .active, .home => go (phase label (if first then .inspect else .scan)) .home .left
  | .alternateRead, .home => go (phase label (if first then .scan else .inspect)) .home .left
  | .scan, .bit b => go (phase label .scan) (.bit b) .left
  | .scan, .inputMark b => go (phase label .inspect) (.bit b) .left
  | .inspect, .bit b => go (phase label (.rewindInput (some b))) (.inputMark b) .right
  | .inspect, .start => go (phase label (.rewindInput none)) .start .right
  | .rewindInput result, .bit b => go (phase label (.rewindInput result)) (.bit b) .right
  | .rewindInput result, .home => go (phase label (.landInput result)) .home .left
  | .landInput result, a => go (.label (next result)) a .right
  | _, a => reject a

def resetTransition (label next : L) : ControlPhase → Symbol R → Transition R L
  | .active, .home => go (phase label .scan) .home .left
  | .scan, .bit b => go (phase label .scan) (.bit b) .left
  | .scan, .inputMark b => go (phase label .rewind) (.bit b) .right
  | .rewind, .bit b => go (phase label .rewind) (.bit b) .right
  | .rewind, .home => go (phase label .land) .home .left
  | .land, .bit b => go (.label next) (.bit b) .right
  | _, a => reject a

def emitTransition (label next : L) (b : Bool) : ControlPhase → Symbol R → Transition R L
  | .active, .home => go (phase label .scan) .home .left
  | .scan, .bit a => go (phase label .scan) (.bit a) .left
  | .scan, .start => go (phase label .scan) .start .left
  | .scan, .blank => go (phase label .rewind) (.bit b) .right
  | .rewind, .bit a => go (phase label .rewind) (.bit a) .right
  | .rewind, .start => go (phase label .rewind) .start .right
  | .rewind, .home => go (phase label .land) .home .left
  | .land, .bit a => go (.label next) (.bit a) .right
  | .land, .start => go (.label next) .start .right
  | _, a => reject a

def finishTransition (label : L) : ControlPhase → Symbol R → Transition R L
  | .active, .home => go (phase label .scan) .home .right
  | .scan, .track cell => go (phase label .scan) (.track cell) .right
  | .scan, .blank => go (phase label .rewind) .blank .left
  | .rewind, .track _ => go (phase label .rewind) .blank .left
  | .rewind, .home => go (phase label .clear) .blank .left
  | .clear, .bit _ => go (phase label .clear) .blank .left
  | .clear, .start => go (phase label .land) .blank .left
  | .land, .bit b => go (phase label .land) (.bit b) .left
  | .land, .blank => (.inr true, .blank, .right)
  | _, a => reject a

end ControlState

open ControlState

variable {R L : Type}

/-- The transition table for the Cook machine simulating a register program. -/
def controlTransition [DecidableEq R] (entry : L) (program : L → Instruction R L) :
    ControlState L → Symbol R → (ControlState L ⊕ Bool) × Symbol R × Dir
  | .inl s, a => setupTransition entry s a
  | .inr (label, p), a =>
    match program label with
    | .inc lane next => incrementTransition label next lane p a
    | .dec lane zero next => decrementTransition label zero next lane p a
    | .readFirst next => readTransition label next true p a
    | .readNext next => readTransition label next false p a
    | .resetInput next => resetTransition label next p a
    | .emit b next => emitTransition label next b p a
    | .halt => finishTransition label p a

/-- Compile the finite program labels to one single-tape Cook machine. -/
abbrev control [Finite R] [Finite L] [DecidableEq R] (entry : L)
    (program : L → Instruction R L) : Machine Bool :=
  host ControlState.initial (controlTransition entry program)

/-- The setup machine starts at the designated program label after framing the input. -/
def controlSetupRules [DecidableEq R] (entry : L) (program : L → Instruction R L) :
    SetupRules (controlTransition entry program) where
  entry := .initial
  mark := .inl .mark
  scan := .inl .scan
  land := .inl .land
  next := .label entry
  enter _ := rfl
  mark_blank := rfl
  scan_bit _ := rfl
  scan_blank := rfl
  land_bit _ := rfl
  land_start := rfl

/-- The compiled states satisfy the counted increment macro's transition rules. -/
def controlIncrementRules [DecidableEq R] (entry : L) (program : L → Instruction R L)
    (label next : L) (lane : R) (instruction : program label = .inc lane next) :
    IncrementRules (controlTransition entry program) lane where
  entry := .label label
  scan := phase label .scan
  rewind := phase label .rewind
  land := phase label .land
  next := .label next
  enter_home := by simp [controlTransition, instruction, incrementTransition]
  scan_true cell h := by simp [controlTransition, instruction, incrementTransition, h]
  scan_false cell h := by simp [controlTransition, instruction, incrementTransition, h]
  scan_blank := by simp [controlTransition, instruction, incrementTransition]
  rewind_track cell := by simp [controlTransition, instruction, incrementTransition]
  rewind_home := by simp [controlTransition, instruction, incrementTransition]
  land_track cell := by simp [controlTransition, instruction, incrementTransition]

/-- The compiled states satisfy the counted decrement macro's transition rules. -/
def controlDecrementRules [DecidableEq R] (entry : L) (program : L → Instruction R L)
    (label zero next : L) (lane : R) (instruction : program label = .dec lane zero next) :
    DecrementRules (controlTransition entry program) lane where
  entry := .label label
  inspect := phase label .inspect
  scan := phase label .scan
  clear := phase label .clear
  rewind := phase label .rewind
  land := phase label .land
  zero := .label zero
  next := .label next
  enter_home := by simp [controlTransition, instruction, decrementTransition]
  inspect_true cell h := by simp [controlTransition, instruction, decrementTransition, h]
  inspect_false cell h := by simp [controlTransition, instruction, decrementTransition, h]
  inspect_blank := by simp [controlTransition, instruction, decrementTransition]
  scan_true cell h := by simp [controlTransition, instruction, decrementTransition, h]
  scan_false cell h := by simp [controlTransition, instruction, decrementTransition, h]
  scan_blank := by simp [controlTransition, instruction, decrementTransition]
  clear_track cell := by simp [controlTransition, instruction, decrementTransition]
  rewind_track cell := by simp [controlTransition, instruction, decrementTransition]
  rewind_home := by simp [controlTransition, instruction, decrementTransition]
  land_track cell := by simp [controlTransition, instruction, decrementTransition]

def controlReadRules [DecidableEq R] (entry : L) (program : L → Instruction R L)
    (label : L) (next : Option Bool → L) (first : Bool)
    (instruction : program label = if first then .readFirst next else .readNext next) :
    CursorRules (controlTransition entry program) := by
  have step (p : ControlPhase) (a : Symbol R) :
      controlTransition entry program (phase label p) a = readTransition label next first p a := by
    cases first <;> simp_all [controlTransition]
  exact {
    first := phase label (if first then .active else .alternateRead)
    advance := phase label (if first then .alternateRead else .active)
    seek := phase label .scan
    pick := phase label .inspect
    rewind result := phase label (.rewindInput result)
    land result := phase label (.landInput result)
    next result := .label (next result)
    first_home := by cases first <;> rw [step] <;> rfl
    advance_home := by cases first <;> rw [step] <;> rfl
    seek_bit b := step .scan (.bit b)
    seek_mark b := step .scan (.inputMark b)
    pick_bit b := step .inspect (.bit b)
    pick_start := step .inspect .start
    rewind_bit result b := step (.rewindInput result) (.bit b)
    rewind_home result := step (.rewindInput result) .home
    land_bit result b := step (.landInput result) (.bit b)
    land_mark b := step (.landInput (some b)) (.inputMark b)
    land_start := step (.landInput none) .start }

/-- At a first-read label, the active state enters the first-read macro. -/
abbrev controlReadFirstRules [DecidableEq R] (entry : L) (program : L → Instruction R L)
    (label : L) (next : Option Bool → L) (instruction : program label = .readFirst next) :
    CursorRules (controlTransition entry program) :=
  controlReadRules entry program label next true instruction

/-- At an advance label, the active state enters the next-read macro. -/
abbrev controlReadNextRules [DecidableEq R] (entry : L) (program : L → Instruction R L)
    (label : L) (next : Option Bool → L) (instruction : program label = .readNext next) :
    CursorRules (controlTransition entry program) :=
  controlReadRules entry program label next false instruction

section CountedInstructions

variable [Finite R] [Finite L] [DecidableEq R]
variable (entry : L) (program : L → Instruction R L)

local notation "M" => control entry program

/-- A reset label restores the marked input symbol and reaches its successor. -/
theorem run_control_resetInput (label next : L) (near : BinaryWord) (prior : Bool)
    (far right : List (Symbol R)) (instruction : program label = .resetInput next) :
    (M).run (2 * near.length + 4)
        ⟨.inl (.label label), (M).tapeFromLists (bits near ++ .inputMark prior :: far)
          (.home :: right)⟩ =
      ⟨.inl (.label next), (M).tapeFromLists (bits near ++ .bit prior :: far)
        (.home :: right)⟩ := by
  have step (p : ControlPhase) (a : Symbol R) :
      controlTransition entry program (phase label p) a = resetTransition label next p a := by
    simp [controlTransition, instruction]
  exact run_resetInput ControlState.initial (controlTransition entry program)
    (.label label) (phase label .scan) (phase label .rewind) (phase label .land) (.label next)
    near prior far right (step .active .home) (fun b ↦ step .scan (.bit b))
    (step .scan (.inputMark prior)) (fun b ↦ step .rewind (.bit b)) (step .rewind .home)
    (fun b ↦ step .land (.bit b))

/-- An emit label appends its bit on the output side and reaches its successor. -/
theorem run_control_emitBit (label next : L) (x emitted : BinaryWord) (b : Bool)
    (right : List (Symbol R)) (instruction : program label = .emit b next) :
    (M).run (2 * (x.length + emitted.length) + 6)
        ⟨.inl (.label label), (M).tapeFromLists (bits x.reverse ++ .start :: bits emitted)
          (.home :: right)⟩ =
      ⟨.inl (.label next), (M).tapeFromLists (bits x.reverse ++ .start :: bits (emitted ++ [b]))
        (.home :: right)⟩ := by
  have step (p : ControlPhase) (a : Symbol R) :
      controlTransition entry program (phase label p) a = emitTransition label next b p a := by
    simp [controlTransition, instruction]
  exact run_emitBit ControlState.initial (controlTransition entry program)
    (.label label) (phase label .scan) (phase label .rewind) (phase label .land) (.label next)
    x emitted b right (step .active .home) (fun a ↦ step .scan (.bit a)) (step .scan .start)
    (step .scan .blank) (fun a ↦ step .rewind (.bit a)) (step .rewind .start) (step .rewind .home)
    (fun a ↦ step .land (.bit a)) (step .land .start)

/-- A halt label cleans up the work and input cells, leaving the canonical output tape. -/
theorem run_control_finish (label : L) (x emitted : BinaryWord) (cells : List (R → Bool))
    (instruction : program label = .halt) :
    (M).run (2 * cells.length + x.length + emitted.length + 5)
        ⟨.inl (.label label), (M).tapeFromLists (bits x.reverse ++ .start :: bits emitted)
          (.home :: trackTape cells)⟩ =
      ⟨.inr true, (M).wordTape emitted.reverse⟩ := by
  have step (p : ControlPhase) (a : Symbol R) :
      controlTransition entry program (phase label p) a = finishTransition label p a := by
    simp [controlTransition, instruction]
  exact run_finish ControlState.initial (controlTransition entry program)
    (.label label) (phase label .scan) (phase label .rewind) (phase label .clear)
    (phase label .land) x emitted cells (step .active .home)
    (fun a ↦ step .scan (.track a)) (step .scan .blank)
    (fun a ↦ step .rewind (.track a)) (step .rewind .home) (fun a ↦ step .clear (.bit a))
    (step .clear .start) (fun a ↦ step .land (.bit a)) (step .land .blank)

end CountedInstructions

end PvsNP.RegisterMachine
