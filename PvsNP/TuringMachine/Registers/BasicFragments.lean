module

public import PvsNP.TuringMachine.Registers.Fragments
public import PvsNP.TuringMachine.Registers.InputLength
public import PvsNP.TuringMachine.Registers.Multiply

/-! # Linkable register arithmetic and input length

Each fragment has its own finite set of internal labels and a common exit.
The counted macro theorems give its exact normal execution.
-/

@[expose] public section

namespace PvsNP.RegisterMachine.Fragment

variable {R K : Type}

/-- Add the input length to `lane`. -/
abbrev inputLength (lane : R) : Fragment R where
  Label := Fin 3
  entry := some 0
  code label := match label.val with
    | 0 => .readFirst (inputLengthBranch (some 1) none)
    | 1 => .inc lane (some 2)
    | _ => .readNext (inputLengthBranch (some 1) none)

/-- Add the source to the target through an initially empty scratch register. -/
abbrev add (source target scratch : R) : Fragment R where
  Label := Fin 5
  entry := some 0
  code label := match label.val with
    | 0 => .dec source (some 3) (some 1)
    | 1 => .inc target (some 2)
    | 2 => .inc scratch (some 0)
    | 3 => .dec scratch none (some 4)
    | _ => .inc source (some 3)

/-- Add the product to the accumulator and consume the multiplier. -/
abbrev multiply (multiplier multiplicand accumulator scratch : R) : Fragment R where
  Label := Fin 6
  entry := some 0
  code label := match label.val with
    | 0 => .dec multiplier none (some 1)
    | 1 => .dec multiplicand (some 4) (some 2)
    | 2 => .inc accumulator (some 3)
    | 3 => .inc scratch (some 1)
    | 4 => .dec scratch (some 0) (some 5)
    | _ => .inc multiplicand (some 4)

/-- A finite chain of increments, with a direct exit when the amount is zero. -/
abbrev incrementBy (lane : R) (amount : Nat) : Fragment R where
  Label := Fin amount
  entry := if h : 0 < amount then some ⟨0, h⟩ else none
  code label := .inc lane
    (if h : label.val + 1 < amount then some ⟨label.val + 1, h⟩ else none)

variable [DecidableEq R]

private def lengthRules (lane : R) : InputLengthRules (inputLength lane).close lane where
  entry := some 0
  count := some 1
  advance := some 2
  next := none
  read_first := rfl
  increment := rfl
  read_next := rfl

/-- Count the input, preserve the output, and leave the cursor unmarked at the exit. -/
theorem run_inputLength (lane : R) (x : BinaryWord) (cfg : Config R K)
    (hCursor : cfg.cursor = none) :
    (inputLength lane).run x (2 * x.length + 1) ((inputLength lane).enter cfg) =
      some ⟨some none, addRegisterValue lane x.length cfg.values, none, cfg.output⟩ :=
  RegisterMachine.run_inputLength (lengthRules lane) x (cfg := (inputLength lane).enter cfg)
    rfl hCursor

private def addRules (source target scratch : R) :
    AddRules (add source target scratch).close source target scratch where
  entry := some 0
  addTarget := some 1
  addScratch := some 2
  restore := some 3
  addSource := some 4
  next := none
  takeSource := rfl
  writeTarget := rfl
  writeScratch := rfl
  takeScratch := rfl
  writeSource := rfl

/-- Add through a scratch register using five instructions per unit and two zero tests. -/
theorem run_add (source target scratch : R) (x : BinaryWord) (cfg : Config R K)
    (hST : source ≠ target) (hSW : source ≠ scratch) (hTW : target ≠ scratch)
    (hScratch : cfg.values scratch = 0) :
    (add source target scratch).run x (5 * cfg.values source + 2)
        ((add source target scratch).enter cfg) =
      some ⟨some none, addValues source target cfg.values, cfg.cursor, cfg.output⟩ :=
  run_add_register (addRules source target scratch) x hST hSW hTW
    (cfg := (add source target scratch).enter cfg) rfl hScratch

private def multiplyRules (multiplier multiplicand accumulator scratch : R) :
    MultiplyRules (multiply multiplier multiplicand accumulator scratch).close
      multiplier multiplicand accumulator scratch where
  entry := some 0
  next := none
  add := {
    entry := some 1
    addTarget := some 2
    addScratch := some 3
    restore := some 4
    addSource := some 5
    next := some 0
    takeSource := rfl
    writeTarget := rfl
    writeScratch := rfl
    takeScratch := rfl
    writeSource := rfl }
  takeMultiplier := rfl
  addReturns := rfl

/-- The multiplication fragment completes in the exact repeated-addition count. -/
theorem run_multiply (multiplier multiplicand accumulator scratch : R)
    (x : BinaryWord) (cfg : Config R K)
    (hMP : multiplier ≠ multiplicand) (hMA : multiplier ≠ accumulator)
    (hMS : multiplier ≠ scratch) (hPA : multiplicand ≠ accumulator)
    (hPS : multiplicand ≠ scratch) (hAS : accumulator ≠ scratch)
    (hScratch : cfg.values scratch = 0) :
    (multiply multiplier multiplicand accumulator scratch).run x
        (cfg.values multiplier * (5 * cfg.values multiplicand + 3) + 1)
        ((multiply multiplier multiplicand accumulator scratch).enter cfg) =
      some ⟨some none, multiplyValues multiplier multiplicand accumulator cfg.values,
        cfg.cursor, cfg.output⟩ :=
  RegisterMachine.run_multiply (multiplyRules multiplier multiplicand accumulator scratch)
    x hMP hMA hMS hPA hPS hAS
    (cfg := (multiply multiplier multiplicand accumulator scratch).enter cfg) rfl hScratch

private theorem incrementThenAdd (lane : R) (amount : Nat) (values : R → Nat) :
    addRegisterValue lane amount (incrementValues lane values) =
      addRegisterValue lane (amount + 1) values := by
  funext r
  by_cases h : r = lane
  · simp only [h, addRegisterValue, incrementValues, ite_true]
    omega
  · simp [h, addRegisterValue, incrementValues]

private theorem run_incrementFrom (lane : R) (amount : Nat) (x : BinaryWord)
    (remaining : Nat) (current : Fin amount) (cfg : (incrementBy lane amount).Cfg)
    (hRemaining : current.val + (remaining + 1) = amount)
    (hPC : cfg.pc = some (some current)) :
    (incrementBy lane amount).run x (remaining + 1) cfg =
      some ⟨some none, addRegisterValue lane (remaining + 1) cfg.values,
        cfg.cursor, cfg.output⟩ := by
  change RegisterMachine.run (incrementBy lane amount).close x (remaining + 1) cfg = _
  induction remaining generalizing current cfg with
  | zero =>
    have hLimit : ¬ current.val + 1 < amount := by omega
    have hCode : (incrementBy lane amount).close (some current) = .inc lane none := by
      simp [close, incrementBy, hLimit]
    have hStep := step_inc (x := x) hPC hCode
    rw [RegisterMachine.run_succ, hStep, Option.bind_some, run_zero]
    rfl
  | succ remaining ih =>
    have hLimit : current.val + 1 < amount := by omega
    let next : Fin amount := ⟨current.val + 1, hLimit⟩
    have hCode : (incrementBy lane amount).close (some current) = .inc lane (some next) := by
      simp [close, incrementBy, hLimit, next]
    let mid : (incrementBy lane amount).Cfg :=
      ⟨some (some next), incrementValues lane cfg.values, cfg.cursor, cfg.output⟩
    have hStep : step (incrementBy lane amount).close x cfg = some mid :=
      step_inc hPC hCode
    have hLeft : next.val + (remaining + 1) = amount := by
      change current.val + 1 + (remaining + 1) = amount
      omega
    have hRest := ih next mid hLeft rfl
    rw [RegisterMachine.run_succ, hStep, Option.bind_some, hRest]
    simp only [mid, incrementThenAdd]

/-- The constant increment fragment runs exactly one instruction per unit. -/
theorem run_incrementBy (lane : R) (amount : Nat) (x : BinaryWord) (cfg : Config R K) :
    (incrementBy lane amount).run x amount ((incrementBy lane amount).enter cfg) =
      some ⟨some none, addRegisterValue lane amount cfg.values, cfg.cursor, cfg.output⟩ := by
  cases amount with
  | zero =>
    have hValues : addRegisterValue lane 0 cfg.values = cfg.values := by
      funext r
      simp [addRegisterValue]
    rw [hValues]
    rfl
  | succ amount =>
    let cfg' := (incrementBy lane (amount + 1)).enter cfg
    let first : Fin (amount + 1) := ⟨0, Nat.succ_pos _⟩
    have hPC : cfg'.pc = some (some first) := by
      simp [cfg', first, enter, incrementBy]
    exact run_incrementFrom lane (amount + 1) x amount first cfg' (Nat.zero_add _) hPC

end PvsNP.RegisterMachine.Fragment
