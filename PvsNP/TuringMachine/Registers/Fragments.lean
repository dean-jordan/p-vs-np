module

public import PvsNP.TuringMachine.Registers.Program
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Data.Fintype.Option

/-! # Linking finite register program fragments -/

@[expose] public section

namespace PvsNP.RegisterMachine

variable {R L K J : Type}

/-- Relabel all successor labels, leaving the operation unchanged. -/
def Instruction.map (f : L → K) : Instruction R L → Instruction R K
  | .inc r next => .inc r (f next)
  | .dec r zero next => .dec r (f zero) (f next)
  | .readFirst next => .readFirst (f ∘ next)
  | .readNext next => .readNext (f ∘ next)
  | .resetInput next => .resetInput (f next)
  | .emit bit next => .emit bit (f next)
  | .halt => .halt

theorem Instruction.map_map (f : L → K) (g : K → J) (i : Instruction R L) :
    (i.map f).map g = i.map (g ∘ f) := by
  cases i <;> rfl

/-- Relabel control without changing registers, input cursor, or output. -/
def Config.map (f : L → K) (cfg : Config R L) : Config R K :=
  ⟨cfg.pc.map f, cfg.values, cfg.cursor, cfg.output⟩

variable [DecidableEq R]

theorem Instruction.execute_map (f : L → K) (i : Instruction R L)
    (x : BinaryWord) (cfg : Config R L) :
    (i.map f).execute x (cfg.map f) = (i.execute x cfg).map (Config.map f) := by
  cases i <;> cases h : cfg.cursor <;>
    simp [Instruction.map, Instruction.execute, Config.map, Config.readAt, Function.comp_def, h]
  all_goals split <;> rfl

private theorem run_preserves_halt {program : L → Instruction R L} {x : BinaryWord}
    {n : Nat} {cfg next : Config R L} (hPC : cfg.pc = none)
    (hRun : run program x n cfg = some next) : next.pc = none := by
  cases n with
  | zero =>
    simp only [run_zero, Option.some.injEq] at hRun
    exact hRun ▸ hPC
  | succ n => simp [run_succ, step, hPC] at hRun

/-- A trace whose endpoint still has a label can be moved into a larger program.
The larger program may replace any source halt with different code. -/
theorem run_map_of_live (f : L → K) {source : L → Instruction R L}
    {target : K → Instruction R K} {x : BinaryWord} {n : Nat} {cfg next : Config R L}
    (hCode : ∀ label, source label ≠ .halt → target (f label) = (source label).map f)
    (hRun : run source x n cfg = some next) (hLive : next.pc ≠ none) :
    run target x n (cfg.map f) = some (next.map f) := by
  induction n generalizing cfg with
  | zero =>
    simp only [run_zero, Option.some.injEq] at hRun
    subst next
    rfl
  | succ n ih =>
    rw [run_succ] at hRun ⊢
    cases hPC : cfg.pc with
    | none => simp [step, hPC] at hRun
    | some label =>
      cases hStep : step source x cfg with
      | none => simp [hStep] at hRun
      | some mid =>
        simp only [hStep, Option.bind_some] at hRun
        have hNotHalt : source label ≠ .halt := by
          intro hHalt
          rw [step_at hPC, hHalt] at hStep
          cases hCursor : cfg.cursor with
          | none =>
            simp only [Instruction.execute, hCursor, Option.some.injEq] at hStep
            exact hLive (run_preserves_halt (hStep ▸ rfl) hRun)
          | some j => simp [Instruction.execute, hCursor] at hStep
        have hPC' : (cfg.map f).pc = some (f label) := by simp [Config.map, hPC]
        rw [step_at hPC', hCode label hNotHalt, Instruction.execute_map, ← step_at hPC,
          hStep, Option.map_some, Option.bind_some]
        exact ih hRun

/-- A program with finitely many internal labels and a single shared exit.
An absent entry represents no instructions. -/
structure Fragment (R : Type) where
  Label : Type
  [finiteLabel : Finite Label]
  entry : Option Label
  code : Label → Instruction R (Option Label)

attribute [instance] Fragment.finiteLabel

namespace Fragment

variable (fragment : Fragment R)

/-- A fragment configuration distinguishes its live exit `some none` from a machine halt. -/
abbrev Cfg := Config R (Option fragment.Label)

/-- Turn a fragment's exit into the halt instruction of a complete program. -/
def close : Option fragment.Label → Instruction R (Option fragment.Label)
  | some label => fragment.code label
  | none => .halt

/-- Start at the fragment's entry without changing the data. -/
def enter (cfg : Config R K) : fragment.Cfg :=
  ⟨some fragment.entry, cfg.values, cfg.cursor, cfg.output⟩

/-- Run a fragment for an exact number of instructions. A normal completion
leaves the control at its live exit. -/
abbrev run (x : BinaryWord) (n : Nat) (cfg : fragment.Cfg) : Option fragment.Cfg :=
  RegisterMachine.run fragment.close x n cfg

/-- A fragment that immediately reaches its exit. -/
def skip : Fragment R where
  Label := Empty
  entry := none
  code := Empty.elim

/-- Map a first-fragment exit to the second fragment's entry. -/
def seqLeft {first : Fragment R} (second : Fragment R) :
    Option first.Label → Option (first.Label ⊕ second.Label)
  | some label => some (.inl label)
  | none => second.entry.map Sum.inr

/-- Link two fragments without spending an instruction at their shared boundary. -/
abbrev seq (first second : Fragment R) : Fragment R where
  Label := first.Label ⊕ second.Label
  entry := seqLeft second first.entry
  code
    | .inl label => (first.code label).map (seqLeft second)
    | .inr label => (second.code label).map (Option.map Sum.inr)

/-- Transport a normal fragment execution into a program that links every internal label.
The destination of the exit is chosen by the caller. -/
theorem run_link {fragment : Fragment R} (f : Option fragment.Label → K)
    {target : K → Instruction R K} {x : BinaryWord} {n : Nat} {cfg next : fragment.Cfg}
    (hCode : ∀ label, target (f (some label)) = (fragment.code label).map f)
    (hRun : fragment.run x n cfg = some next) (hExit : next.pc = some none) :
    RegisterMachine.run target x n (cfg.map f) = some (next.map f) := by
  apply run_map_of_live f _ hRun (by simp [hExit])
  intro label hLive
  cases label with
  | none => exact (hLive rfl).elim
  | some label => exact hCode label

/-- Normal sequential completion takes exactly the sum of the two instruction counts.
Either fragment may start directly at its exit. -/
theorem run_seq {first second : Fragment R} {x : BinaryWord} {m n : Nat}
    {cfg : Config R K} {mid : first.Cfg} {next : second.Cfg}
    (hFirst : first.run x m (first.enter cfg) = some mid) (hMid : mid.pc = some none)
    (hSecond : second.run x n (second.enter mid) = some next) (hNext : next.pc = some none) :
    (first.seq second).run x (m + n) ((first.seq second).enter cfg) =
      some (next.map (Option.map Sum.inr)) := by
  have hLeft := run_link (seqLeft (first := first) second)
    (target := (first.seq second).close) (fun _ ↦ rfl) hFirst hMid
  have hRight := run_link (Option.map Sum.inr)
    (target := (first.seq second).close) (fun _ ↦ rfl) hSecond hNext
  have hStart : (first.enter cfg).map (seqLeft second) = (first.seq second).enter cfg := rfl
  have hBoundary : mid.map (seqLeft second) = (second.enter mid).map (Option.map Sum.inr) := by
    simp [Config.map, enter, hMid, seqLeft]
  change RegisterMachine.run (first.seq second).close x (m + n) _ = _
  rw [RegisterMachine.run_add, ← hStart, hLeft, Option.bind_some, hBoundary]
  exact hRight

/-- A normal completion becomes a machine halt by taking the one exit instruction. -/
theorem run_close {fragment : Fragment R} {x : BinaryWord} {n : Nat} {cfg next : fragment.Cfg}
    (hRun : fragment.run x n cfg = some next) (hExit : next.pc = some none)
    (hCursor : next.cursor = none) :
    RegisterMachine.run fragment.close x (n + 1) cfg = some { next with pc := none } := by
  change RegisterMachine.run fragment.close x n cfg = some next at hRun
  rw [RegisterMachine.run_add, hRun, Option.bind_some]
  simp [RegisterMachine.run_succ, step_at hExit, close, Instruction.execute, hCursor]

end Fragment

end PvsNP.RegisterMachine
