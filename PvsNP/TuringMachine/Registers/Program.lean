module

public import PvsNP.TuringMachine.Registers.Values

/-!
# Register program semantics

A program assigns one instruction to each control label. Input is read from
right to left, and emitting prepends a bit in the final output orientation.
-/

@[expose] public section

namespace PvsNP.RegisterMachine

variable {R L : Type}

/-- Instructions for the packed unary register machine. -/
inductive Instruction (R L : Type) where
  | inc (reg : R) (next : L)
  | dec (reg : R) (zero next : L)
  | readFirst (next : Option Bool → L)
  | readNext (next : Option Bool → L)
  | resetInput (next : L)
  | emit (bit : Bool) (next : L)
  | halt

/-- A running configuration has a label. A cursor stores the position of its input mark. -/
structure Config (R L : Type) where
  pc : Option L
  values : R → Nat
  cursor : Option Nat
  output : BinaryWord

/-- Begin at the first label, with zero registers and no cursor or output. -/
def Config.initial (label : L) : Config R L :=
  ⟨some label, fun _ ↦ 0, none, []⟩

/-- An input cursor, when present, points into the reversed input. -/
def Config.ValidCursor (cfg : Config R L) (x : BinaryWord) : Prop :=
  ∀ i, cfg.cursor = some i → i < x.length

/-- Set the cursor to the newly read position, or clear it at the end of input. -/
def Config.readAt (cfg : Config R L) (x : BinaryWord) (i : Nat)
    (next : Option Bool → L) : Config R L :=
  let read := x.reverse[i]?
  { cfg with pc := some (next read), cursor := read.map (fun _ ↦ i) }

theorem Config.validCursor_initial (label : L) (x : BinaryWord) :
    (Config.initial (R := R) label).ValidCursor x := by
  simp [Config.ValidCursor, Config.initial]

theorem Config.validCursor_readAt (cfg : Config R L) (x : BinaryWord) (i : Nat)
    (next : Option Bool → L) : (cfg.readAt x i next).ValidCursor x := by
  intro pos hPos
  change (x.reverse[i]?).map (fun _ ↦ i) = some pos at hPos
  cases hRead : x.reverse[i]? with
  | none => simp [hRead] at hPos
  | some b =>
    simp only [hRead, Option.map_some, Option.some.injEq] at hPos
    subst pos
    simpa using (List.getElem?_eq_some_iff.mp hRead).choose

private theorem Config.readAt_invariants (cfg : Config R L) (x : BinaryWord) (i : Nat)
    (next : Option Bool → L) :
    (∀ reg, (cfg.readAt x i next).values reg ≤ cfg.values reg + 1) ∧
      (cfg.readAt x i next).output.length ≤ cfg.output.length + 1 ∧
      (cfg.ValidCursor x → (cfg.readAt x i next).ValidCursor x) := by
  refine ⟨?_, ?_, fun _ ↦ cfg.validCursor_readAt x i next⟩
  · simp [Config.readAt, Nat.le_succ]
  · simp [Config.readAt, Nat.le_succ]

variable [DecidableEq R]

/-- Decrement one register, using truncated subtraction. -/
def decrementValues (reg : R) (values : R → Nat) : R → Nat :=
  fun r ↦ if r = reg then values r - 1 else values r

/-- Apply an instruction. Cursor operations require the marker in the expected
state, and output and halt require unmarked input. -/
def Instruction.execute (x : BinaryWord) (cfg : Config R L) :
    Instruction R L → Option (Config R L)
  | .inc reg next => some { cfg with pc := some next, values := incrementValues reg cfg.values }
  | .dec reg zero next =>
    if cfg.values reg = 0 then some { cfg with pc := some zero }
    else some { cfg with pc := some next, values := decrementValues reg cfg.values }
  | .readFirst next =>
    match cfg.cursor with
    | none => some (cfg.readAt x 0 next)
    | some _ => none
  | .readNext next =>
    match cfg.cursor with
    | none => none
    | some i => some (cfg.readAt x (i + 1) next)
  | .resetInput next =>
    match cfg.cursor with
    | none => none
    | some _ => some { cfg with pc := some next, cursor := none }
  | .emit bit next =>
    match cfg.cursor with
    | none => some { cfg with pc := some next, output := bit :: cfg.output }
    | some _ => none
  | .halt =>
    match cfg.cursor with
    | none => some { cfg with pc := none }
    | some _ => none

/-- Execute the instruction at the current label. Halting clears the label. -/
def step (program : L → Instruction R L) (x : BinaryWord) (cfg : Config R L) :
    Option (Config R L) :=
  cfg.pc.bind fun label ↦ (program label).execute x cfg

theorem step_at {program : L → Instruction R L} {x : BinaryWord} {cfg : Config R L} {label : L}
    (h : cfg.pc = some label) : step program x cfg = (program label).execute x cfg := by
  simp [step, h]

theorem step_inc {program : L → Instruction R L} {x : BinaryWord} {cfg : Config R L}
    {label reg next} (hPC : cfg.pc = some label) (hRule : program label = .inc reg next) :
    step program x cfg = some
      { cfg with pc := some next, values := incrementValues reg cfg.values } := by
  rw [step_at hPC, hRule]
  rfl

theorem step_dec_zero {program : L → Instruction R L} {x : BinaryWord} {cfg : Config R L}
    {label reg zero next} (hPC : cfg.pc = some label) (hRule : program label = .dec reg zero next)
    (hZero : cfg.values reg = 0) : step program x cfg = some { cfg with pc := some zero } := by
  simp only [step_at hPC, hRule, Instruction.execute, ite_eq_left hZero]

theorem step_dec_pos {program : L → Instruction R L} {x : BinaryWord} {cfg : Config R L}
    {label reg zero next} (hPC : cfg.pc = some label) (hRule : program label = .dec reg zero next)
    (hPos : 0 < cfg.values reg) :
    step program x cfg = some
      { cfg with pc := some next, values := decrementValues reg cfg.values } := by
  simp only [step_at hPC, hRule, Instruction.execute, ite_eq_right (Nat.ne_of_gt hPos)]

theorem step_readFirst {program : L → Instruction R L} {x : BinaryWord} {cfg : Config R L}
    {label next} (hPC : cfg.pc = some label) (hRule : program label = .readFirst next)
    (hCursor : cfg.cursor = none) : step program x cfg = some (cfg.readAt x 0 next) := by
  simp only [step_at hPC, hRule, Instruction.execute, hCursor]

theorem step_readNext {program : L → Instruction R L} {x : BinaryWord} {cfg : Config R L}
    {label next i} (hPC : cfg.pc = some label) (hRule : program label = .readNext next)
    (hCursor : cfg.cursor = some i) : step program x cfg = some (cfg.readAt x (i + 1) next) := by
  simp only [step_at hPC, hRule, Instruction.execute, hCursor]

theorem step_resetInput {program : L → Instruction R L} {x : BinaryWord} {cfg : Config R L}
    {label next i} (hPC : cfg.pc = some label) (hRule : program label = .resetInput next)
    (hCursor : cfg.cursor = some i) :
    step program x cfg = some { cfg with pc := some next, cursor := none } := by
  simp only [step_at hPC, hRule, Instruction.execute, hCursor]

theorem step_emit {program : L → Instruction R L} {x : BinaryWord} {cfg : Config R L}
    {label bit next} (hPC : cfg.pc = some label) (hRule : program label = .emit bit next)
    (hCursor : cfg.cursor = none) :
    step program x cfg = some { cfg with pc := some next, output := bit :: cfg.output } := by
  simp only [step_at hPC, hRule, Instruction.execute, hCursor]

theorem step_halt {program : L → Instruction R L} {x : BinaryWord} {cfg : Config R L}
    {label} (hPC : cfg.pc = some label) (hRule : program label = .halt)
    (hCursor : cfg.cursor = none) :
    step program x cfg = some { cfg with pc := none } := by
  simp only [step_at hPC, hRule, Instruction.execute, hCursor]

/-- Execute exactly the given number of instructions. A failed step fails the run. -/
def run (program : L → Instruction R L) (x : BinaryWord) :
    Nat → Config R L → Option (Config R L)
  | 0, cfg => some cfg
  | n + 1, cfg => (step program x cfg).bind (run program x n)

@[simp] theorem run_zero (program : L → Instruction R L) (x : BinaryWord) (cfg : Config R L) :
    run program x 0 cfg = some cfg :=
  rfl

theorem run_succ (program : L → Instruction R L) (x : BinaryWord) (n : Nat) (cfg : Config R L) :
    run program x (n + 1) cfg = (step program x cfg).bind (run program x n) :=
  rfl

theorem run_add (program : L → Instruction R L) (x : BinaryWord) (m n : Nat) (cfg : Config R L) :
    run program x (m + n) cfg = (run program x m cfg).bind (run program x n) := by
  induction m generalizing cfg with
  | zero => simp
  | succ m ih =>
    simp only [Nat.succ_add, run_succ, Option.bind_assoc]
    congr 1
    funext cfg'
    exact ih cfg'

private theorem Instruction.execute_invariants {instruction : Instruction R L}
    {x : BinaryWord} {cfg next : Config R L}
    (hStep : instruction.execute x cfg = some next) :
    (∀ reg, next.values reg ≤ cfg.values reg + 1) ∧
      next.output.length ≤ cfg.output.length + 1 ∧
      (cfg.ValidCursor x → next.ValidCursor x) := by
  have hInc (reg r : R) : incrementValues reg cfg.values r ≤ cfg.values r + 1 := by
    unfold incrementValues
    split <;> omega
  have hDec (reg r : R) : decrementValues reg cfg.values r ≤ cfg.values r + 1 := by
    unfold decrementValues
    split <;> omega
  cases instruction <;> simp only [Instruction.execute] at hStep
  all_goals (try split at hStep)
  all_goals try contradiction
  all_goals cases hStep
  all_goals try apply Config.readAt_invariants
  all_goals simp [Config.ValidCursor, Nat.le_succ, hInc, hDec]

/-- A successful instruction grows each register and the output by at most one,
and preserves valid input marks. -/
theorem step_invariants {program : L → Instruction R L} {x : BinaryWord} {cfg next : Config R L}
    (hStep : step program x cfg = some next) :
    (∀ reg, next.values reg ≤ cfg.values reg + 1) ∧
      next.output.length ≤ cfg.output.length + 1 ∧
      (cfg.ValidCursor x → next.ValidCursor x) := by
  cases hPC : cfg.pc with
  | none => simp [step, hPC] at hStep
  | some label =>
    rw [step_at hPC] at hStep
    exact Instruction.execute_invariants hStep

/-- A successful counted run grows each register and the output by at most its instruction count. -/
theorem run_invariants {program : L → Instruction R L} {x : BinaryWord} {cfg next : Config R L}
    {n : Nat} (hRun : run program x n cfg = some next) :
    (∀ reg, next.values reg ≤ cfg.values reg + n) ∧
      next.output.length ≤ cfg.output.length + n ∧
      (cfg.ValidCursor x → next.ValidCursor x) := by
  induction n generalizing cfg with
  | zero =>
    simp only [run_zero, Option.some.injEq] at hRun
    subst next
    simp
  | succ n ih =>
    rw [run_succ] at hRun
    cases hStep : step program x cfg with
    | none => simp [hStep] at hRun
    | some mid =>
      simp only [hStep, Option.bind_some] at hRun
      obtain ⟨hReg, hSize, hMark⟩ := step_invariants hStep
      obtain ⟨hRegs, hSizes, hMarks⟩ := ih hRun
      refine ⟨fun reg ↦ ?_, ?_, fun h ↦ hMarks (hMark h)⟩
      · have := hReg reg
        have := hRegs reg
        omega
      · omega

end PvsNP.RegisterMachine
