module

public import PvsNP.TuringMachine.Registers.Program

/-! # Counted input length on the register machine

The program reads the input backwards. Each bit contributes one increment
and one advance. Reading the end marker clears the cursor.
-/

@[expose] public section

namespace PvsNP.RegisterMachine

variable {R L : Type}

/-- Count another bit on success, or leave the loop at end of input. -/
def inputLengthBranch (count next : L) : Option Bool → L
  | some _ => count
  | none => next

/-- The first read starts the loop and subsequent reads advance the cursor. -/
structure InputLengthRules (program : L → Instruction R L) (lane : R) where
  entry : L
  count : L
  advance : L
  next : L
  read_first : program entry = .readFirst (inputLengthBranch count next)
  increment : program count = .inc lane advance
  read_next : program advance = .readNext (inputLengthBranch count next)

variable [DecidableEq R]

/-- Increase only the selected register. -/
def addRegisterValue (lane : R) (amount : Nat) (values : R → Nat) : R → Nat :=
  fun r ↦ if r = lane then values r + amount else values r

private theorem addRegisterValue_zero (lane : R) (values : R → Nat) :
    addRegisterValue lane 0 values = values := by
  funext r
  simp [addRegisterValue]

private theorem addRegisterValue_one (lane : R) (values : R → Nat) :
    addRegisterValue lane 1 values = incrementValues lane values := rfl

private theorem addRegisterValue_increment (lane : R) (amount : Nat) (values : R → Nat) :
    addRegisterValue lane amount (incrementValues lane values) =
      addRegisterValue lane (amount + 1) values := by
  funext r
  by_cases h : r = lane
  · simp only [h, addRegisterValue, incrementValues, ite_true]
    omega
  · simp [h, addRegisterValue, incrementValues]

variable {program : L → Instruction R L} {lane : R}
variable (rules : InputLengthRules program lane) (x : BinaryWord)

private theorem run_count_round {cfg : Config R L} {i : Nat}
    (hPC : cfg.pc = some rules.count) (hCursor : cfg.cursor = some i) :
    run program x 2 cfg = some
      (({ cfg with values := incrementValues lane cfg.values }).readAt x (i + 1)
        (inputLengthBranch rules.count rules.next)) := by
  let incremented := { cfg with
    pc := some rules.advance
    values := incrementValues lane cfg.values }
  have incStep : step program x cfg = some incremented := step_inc hPC rules.increment
  have readStep := step_readNext (cfg := incremented) (x := x) rfl rules.read_next hCursor
  simp only [run, incStep, Option.bind_some, readStep]
  rfl

private theorem run_count_from (remaining : Nat) {i : Nat} {cfg : Config R L}
    (hLength : i + (remaining + 1) = x.length)
    (hPC : cfg.pc = some rules.count) (hCursor : cfg.cursor = some i) :
    run program x (2 * (remaining + 1)) cfg = some
      { cfg with
        pc := some rules.next
        cursor := none
        values := addRegisterValue lane (remaining + 1) cfg.values } := by
  induction remaining generalizing i cfg with
  | zero =>
    have endRead : x.reverse[i + 1]? = none := List.getElem?_eq_none (by simp [← hLength])
    simpa only [Config.readAt, endRead, inputLengthBranch, Option.map_none, Nat.zero_add,
      addRegisterValue_one] using run_count_round rules x hPC hCursor
  | succ remaining ih =>
    let mid := ({ cfg with values := incrementValues lane cfg.values }).readAt x (i + 1)
      (inputLengthBranch rules.count rules.next)
    have hIndex : i + 1 < x.reverse.length := by
      rw [List.length_reverse]
      omega
    have hRead : x.reverse[i + 1]? = some x.reverse[i + 1] := List.getElem?_eq_getElem hIndex
    have hPC' : mid.pc = some rules.count := by simp [mid, Config.readAt, hRead, inputLengthBranch]
    have hCursor' : mid.cursor = some (i + 1) := by simp [mid, Config.readAt, hRead]
    have hRest := ih (cfg := mid) (i := i + 1) (by omega) hPC' hCursor'
    have hCost : 2 * (remaining + 1 + 1) = 2 + 2 * (remaining + 1) := by omega
    rw [hCost, run_add, run_count_round rules x hPC hCursor, Option.bind_some, hRest]
    simp only [mid, Config.readAt, addRegisterValue_increment]

/-- The loop exits at its successor after adding the input length to one register. -/
theorem run_inputLength {cfg : Config R L} (hPC : cfg.pc = some rules.entry)
    (hCursor : cfg.cursor = none) :
    run program x (2 * x.length + 1) cfg = some
      { cfg with
        pc := some rules.next
        cursor := none
        values := addRegisterValue lane x.length cfg.values } := by
  rw [run_succ, step_readFirst hPC rules.read_first hCursor, Option.bind_some]
  cases hRead : x.reverse[0]? with
  | none =>
    have hLength : x.length = 0 := by
      have hEnd := List.getElem?_eq_none_iff.mp hRead
      rw [List.length_reverse] at hEnd
      omega
    simp [hLength, Config.readAt, inputLengthBranch, addRegisterValue_zero]
  | some bit =>
    let mid := cfg.readAt x 0 (inputLengthBranch rules.count rules.next)
    have hLength : 0 < x.length := by
      obtain ⟨hIndex, _⟩ := List.getElem?_eq_some_iff.mp hRead
      simpa only [List.length_reverse] using hIndex
    have hPC' : mid.pc = some rules.count := by simp [mid, Config.readAt, hRead, inputLengthBranch]
    have hCursor' : mid.cursor = some 0 := by simp [mid, Config.readAt, hRead]
    have hRest := run_count_from rules x (x.length - 1) (cfg := mid) (i := 0)
      (by omega) hPC' hCursor'
    have hAmount : x.length - 1 + 1 = x.length := by omega
    simpa only [hAmount, mid, Config.readAt] using hRest

end PvsNP.RegisterMachine
