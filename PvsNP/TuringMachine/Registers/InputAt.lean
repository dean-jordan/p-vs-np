module

public import PvsNP.TuringMachine.Registers.Program

/-! # Counted reverse input lookup

The machine reads from the right end of the input and decrements the index
for each advance. A matching bit is saved in the control label while the
cursor is reset. If the input ends first, a loop clears the remaining index.
-/

@[expose] public section

namespace PvsNP.RegisterMachine

variable {R L : Type}

/-- Examine the index at a bit, or clear it after the end of input. -/
def inputAtBranch (inspect : Bool → L) (pastEnd : L) : Option Bool → L
  | some b => inspect b
  | none => pastEnd

/-- Local labels for a reverse input lookup using one index register. -/
structure InputAtRules (program : L → Instruction R L) (index : R) where
  entry : L
  inspect : Bool → L
  advance : L
  reset : Bool → L
  pastEnd : L
  next : Option Bool → L
  read_first : program entry = .readFirst (inputAtBranch inspect pastEnd)
  inspect_index : ∀ b, program (inspect b) = .dec index (reset b) advance
  read_next : program advance = .readNext (inputAtBranch inspect pastEnd)
  reset_mark : ∀ b, program (reset b) = .resetInput (next (some b))
  clear_pastEnd : program pastEnd = .dec index (next none) pastEnd

/-- An in-range lookup costs two instructions per advance and three fixed
instructions. At end of input, the remaining index is drained. -/
def inputAtCost (index length : Nat) : Nat :=
  if index < length then 2 * index + 3 else index + length + 2

theorem inputAtCost_le (index length : Nat) : inputAtCost index length ≤ 2 * index + 3 := by
  unfold inputAtCost
  split <;> omega

variable [DecidableEq R]

/-- The register state after the lookup has consumed its index. -/
def clearInputAtIndex (index : R) (values : R → Nat) : R → Nat :=
  fun r ↦ if r = index then 0 else values r

private theorem clear_at_zero (index : R) (values : R → Nat) (h : values index = 0) :
    clearInputAtIndex index values = values := by
  funext r
  by_cases hr : r = index
  · subst r
    simp [clearInputAtIndex, h]
  · simp [clearInputAtIndex, hr]

private theorem clear_after_decrement (index : R) (values : R → Nat) :
    clearInputAtIndex index (decrementValues index values) = clearInputAtIndex index values := by
  funext r
  by_cases h : r = index <;> simp [clearInputAtIndex, decrementValues, h]

private def afterReadCost (index remaining : Nat) : Nat :=
  if index < remaining then 2 * index + 2 else index + remaining + 1

private theorem inputAtCost_eq (index length : Nat) :
    inputAtCost index length = afterReadCost index length + 1 := by
  by_cases h : index < length <;> simp [inputAtCost, afterReadCost, h]

private theorem afterReadCost_advance (i index length : Nat) (hi : i < length) :
    afterReadCost (index + 1) (length - i) = 2 + afterReadCost index (length - (i + 1)) := by
  by_cases h : index < length - (i + 1)
  · have h' : index + 1 < length - i := by omega
    simp only [afterReadCost, ite_eq_left h, ite_eq_left h']
    omega
  · have h' : ¬ index + 1 < length - i := by omega
    simp only [afterReadCost, ite_eq_right h, ite_eq_right h']
    omega

variable {program : L → Instruction R L} {index : R}
variable (rules : InputAtRules program index) (x : BinaryWord)

private theorem run_pastEnd (amount : Nat) {cfg : Config R L}
    (hCount : cfg.values index = amount) (hPC : cfg.pc = some rules.pastEnd) :
    run program x (amount + 1) cfg = some
      { cfg with
        pc := some (rules.next none)
        values := clearInputAtIndex index cfg.values } := by
  induction amount generalizing cfg with
  | zero =>
    rw [run_succ, step_dec_zero hPC rules.clear_pastEnd hCount, Option.bind_some, run_zero,
      clear_at_zero index cfg.values hCount]
  | succ amount ih =>
    let mid := { cfg with
      pc := some rules.pastEnd
      values := decrementValues index cfg.values }
    have hPos : 0 < cfg.values index := by omega
    have hStep : step program x cfg = some mid := step_dec_pos hPC rules.clear_pastEnd hPos
    have hLeft : mid.values index = amount := by simp [mid, decrementValues, hCount]
    have hRest := ih (cfg := mid) hLeft rfl
    rw [run_succ, hStep, Option.bind_some, hRest]
    simp only [mid, clear_after_decrement]

private theorem run_afterRead_none (amount i : Nat) {cfg : Config R L}
    (hCount : cfg.values index = amount) (hRead : x.reverse[i]? = none) :
    run program x (afterReadCost amount (x.length - i))
        (cfg.readAt x i (inputAtBranch rules.inspect rules.pastEnd)) = some
      { cfg with
        pc := some (rules.next (x.reverse[i + amount]?))
        cursor := none
        values := clearInputAtIndex index cfg.values } := by
  have hPast : x.length ≤ i := by
    simpa only [List.length_reverse] using List.getElem?_eq_none_iff.mp hRead
  have hResult : x.reverse[i + amount]? = none :=
    List.getElem?_eq_none (by rw [List.length_reverse]; omega)
  let read := cfg.readAt x i (inputAtBranch rules.inspect rules.pastEnd)
  have hPC : read.pc = some rules.pastEnd := by simp [read, Config.readAt, hRead, inputAtBranch]
  simpa only [afterReadCost, Nat.sub_eq_zero_of_le hPast, Nat.not_lt_zero, ite_false, Nat.add_zero,
    hResult, read, Config.readAt, hRead, Option.map_none] using
    run_pastEnd rules x amount (cfg := read) hCount hPC

private theorem run_afterRead (amount i : Nat) {cfg : Config R L}
    (hCount : cfg.values index = amount) :
    run program x (afterReadCost amount (x.length - i))
        (cfg.readAt x i (inputAtBranch rules.inspect rules.pastEnd)) = some
      { cfg with
        pc := some (rules.next (x.reverse[i + amount]?))
        cursor := none
        values := clearInputAtIndex index cfg.values } := by
  induction amount generalizing cfg i with
  | zero =>
    cases hRead : x.reverse[i]? with
    | none => simpa only [Nat.add_zero, hRead] using run_afterRead_none rules x 0 i hCount hRead
    | some b =>
      let read := cfg.readAt x i (inputAtBranch rules.inspect rules.pastEnd)
      let mid := { read with pc := some (rules.reset b) }
      have hPC : read.pc = some (rules.inspect b) := by
        simp [read, Config.readAt, hRead, inputAtBranch]
      have hCursor : mid.cursor = some i := by simp [mid, read, Config.readAt, hRead]
      have hDec : step program x read = some mid := step_dec_zero hPC (rules.inspect_index b) hCount
      have hReset := step_resetInput (cfg := mid) (x := x) rfl (rules.reset_mark b) hCursor
      have hIndex : i < x.length := by
        simpa only [List.length_reverse] using (List.getElem?_eq_some_iff.mp hRead).choose
      have hAvailable : 0 < x.length - i := by omega
      simp only [afterReadCost, ite_eq_left hAvailable, Nat.mul_zero, Nat.zero_add]
      change run program x 2 read = _
      simp only [run, hDec, hReset, Option.bind_some,
        clear_at_zero index cfg.values hCount]
      rfl
  | succ amount ih =>
    cases hRead : x.reverse[i]? with
    | none => exact run_afterRead_none rules x (amount + 1) i hCount hRead
    | some b =>
      let read := cfg.readAt x i (inputAtBranch rules.inspect rules.pastEnd)
      let reduced := { cfg with values := decrementValues index cfg.values }
      let mid := { read with
        pc := some rules.advance
        values := reduced.values }
      have hPC : read.pc = some (rules.inspect b) := by
        simp [read, Config.readAt, hRead, inputAtBranch]
      have hCursor : mid.cursor = some i := by simp [mid, read, Config.readAt, hRead]
      have hPos : 0 < read.values index := by change 0 < cfg.values index; omega
      have hDec : step program x read = some mid := step_dec_pos hPC (rules.inspect_index b) hPos
      have hAdvance := step_readNext (cfg := mid) (x := x) rfl rules.read_next hCursor
      have hRound : run program x 2 read = some
          (reduced.readAt x (i + 1) (inputAtBranch rules.inspect rules.pastEnd)) := by
        simp only [run, hDec, hAdvance, Option.bind_some]
        rfl
      have hIndex : i < x.length := by
        simpa only [List.length_reverse] using (List.getElem?_eq_some_iff.mp hRead).choose
      have hLeft : reduced.values index = amount := by simp [reduced, decrementValues, hCount]
      have hRest := ih (i + 1) (cfg := reduced) hLeft
      change run program x (afterReadCost (amount + 1) (x.length - i)) read = _
      rw [afterReadCost_advance i amount x.length hIndex, run_add, hRound, Option.bind_some, hRest]
      have hPosition : i + 1 + amount = i + (amount + 1) := by omega
      simp only [reduced, hPosition, clear_after_decrement]

/-- Read the bit at the supplied reverse index, clear the index and cursor,
and branch on the result. Other registers and output are preserved. -/
theorem run_inputAt {cfg : Config R L} (hPC : cfg.pc = some rules.entry)
    (hCursor : cfg.cursor = none) :
    run program x (inputAtCost (cfg.values index) x.length) cfg = some
      { cfg with
        pc := some (rules.next (x.reverse[cfg.values index]?))
        cursor := none
        values := clearInputAtIndex index cfg.values } := by
  rw [inputAtCost_eq, run_succ, step_readFirst hPC rules.read_first hCursor, Option.bind_some]
  simpa only [Nat.sub_zero, Nat.zero_add] using
    run_afterRead rules x (cfg.values index) 0 (cfg := cfg) rfl

end PvsNP.RegisterMachine
