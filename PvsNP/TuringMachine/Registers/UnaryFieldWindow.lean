module

public import PvsNP.TuringMachine.Registers.ForwardLookup
public import PvsNP.TuringMachine.Registers.StridedField

import PvsNP.TuringMachine.Registers.OutputRuns

/-! # Scan a unary prefix in a strided input window

Each true bit consumes one cell of the window and adds one to the count.
A false bit consumes its cell and marks success. The remaining width and
the next ordinary input position are available for the next field.
-/

public section

namespace PvsNP.RegisterMachine.Fragment

variable {R : Type}

/-- The number of leading true bits and whether a terminator follows them. -/
@[expose] def unaryWindowResult : BinaryWord → Nat × Bool
  | [] => (0, false)
  | false :: _ => (0, true)
  | true :: tail =>
    let result := unaryWindowResult tail
    (result.1 + 1, result.2)

theorem unaryWindowResult_terminated (k : Nat) (rest : BinaryWord) :
    unaryWindowResult (List.replicate k true ++ false :: rest) = (k, true) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ, List.cons_append, unaryWindowResult, ih]

theorem unaryWindowResult_no_terminator (k : Nat) :
    unaryWindowResult (List.replicate k true) = (k, false) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ, unaryWindowResult, ih]

theorem unaryWindowResult_spec (bits : BinaryWord) :
    let result := unaryWindowResult bits
    if result.2 then ∃ rest, bits = List.replicate result.1 true ++ false :: rest
    else bits = List.replicate result.1 true := by
  induction bits with
  | nil => rfl
  | cons b tail ih =>
    cases b with
    | false => exact ⟨tail, rfl⟩
    | true =>
      cases hResult : unaryWindowResult tail with
      | mk k ok =>
        cases ok with
        | false =>
          have hTail : tail = List.replicate k true := by simpa [hResult] using ih
          simpa only [unaryWindowResult, hResult, Bool.false_eq_true, ite_false,
            List.replicate_succ] using congrArg (List.cons true) hTail
        | true =>
          obtain ⟨rest, hTail⟩ : ∃ rest, tail = List.replicate k true ++ false :: rest := by
            simpa [hResult] using ih
          simp only [unaryWindowResult, hResult, ite_true, List.replicate_succ, List.cons_append]
          exact ⟨rest, congrArg (List.cons true) hTail⟩

theorem unaryWindowResult_consumed_le (bits : BinaryWord) :
    (unaryWindowResult bits).1 + (unaryWindowResult bits).2.toNat ≤ bits.length := by
  induction bits with
  | nil => decide
  | cons b bits ih =>
    cases b with
    | false => simp [unaryWindowResult]
    | true =>
      simp only [unaryWindowResult, List.length_cons]
      omega

private def unaryReadBranch (stride : Nat) (lanes : Fin 8 → R) : Option Bool → Fragment R
  | none => skip
  | some false => (incrementBy (lanes 1) stride).seq (incrementBy (lanes 4) 1)
  | some true => ((incrementBy (lanes 1) stride).seq (incrementBy (lanes 3) 1)).seq
      (incrementBy (lanes 5) 1)

private def unaryWindowRead (stride : Nat) (lanes : Fin 8 → R) : Fragment R :=
  (add (lanes 1) (lanes 5) (lanes 7)).seq
    (forwardLookup (lanes 0) (lanes 5) (lanes 6) (lanes 7) (unaryReadBranch stride lanes))

private def unaryWindowLink (body : Fragment R) :
    Option body.Label → Option (Fin 2 ⊕ body.Label)
  | none => some (.inl 1)
  | some label => some (.inr label)

/-- Lane 0 holds the input length, lane 1 the ordinary input position, lane 2
the remaining width, lane 3 the count, and lane 4 the success flag.
Lanes 5 through 7 are zeroed scratch registers. -/
def unaryFieldWindow (stride : Nat) (lanes : Fin 8 → R) : Fragment R :=
  let body := unaryWindowRead stride lanes
  { Label := Fin 2 ⊕ body.Label
    entry := some (.inl 0)
    code
      | .inl i => if i = 0 then .dec (lanes 2) none (unaryWindowLink body body.entry)
          else .dec (lanes 5) none (some (.inl 0))
      | .inr label => (body.code label).map (unaryWindowLink body) }

/-- A prepared window of the indicated width has this instruction budget. -/
@[expose] def unaryFieldWindowCost (stride inputLength width : Nat) : Nat :=
  width * (12 * inputLength + stride + 12) + 1

theorem unaryFieldWindowCost_polynomiallyBounded (stride : Nat)
    {inputLength width : Nat → Nat} (hInput : PolynomiallyBounded inputLength)
    (hWidth : PolynomiallyBounded width) :
    PolynomiallyBounded (fun n ↦ unaryFieldWindowCost stride (inputLength n) (width n)) :=
  (hWidth.mul ((((PolynomiallyBounded.const 12).mul hInput).add
    (PolynomiallyBounded.const stride)).add (PolynomiallyBounded.const 12))).add
    (PolynomiallyBounded.const 1)

variable [DecidableEq R]

private def unaryReadValues (stride : Nat) (lanes : Fin 8 → R) (bit : Bool)
    (before : R → Nat) : R → Nat :=
  let advanced := setValue (lanes 1) (before (lanes 1) + stride) before
  if bit then
    setValue (lanes 5) 1 (setValue (lanes 3) (before (lanes 3) + 1) advanced)
  else setValue (lanes 4) (before (lanes 4) + 1) advanced

private theorem runsValues_unaryReadBranch (stride : Nat) (lanes : Fin 8 → R)
    (hLanes : Function.Injective lanes) (x : BinaryWord) (before : R → Nat) (bit : Bool)
    (hIndex : before (lanes 5) = 0) :
    (unaryReadBranch stride lanes (some bit)).RunsValues x
      (stride + (if bit then 2 else 1)) before (unaryReadValues stride lanes bit before) := by
  have hLane (i j : Fin 8) : lanes i = lanes j ↔ i = j := ⟨fun e ↦ hLanes e, congrArg lanes⟩
  let advanced := setValue (lanes 1) (before (lanes 1) + stride) before
  have hAdvance := runsValues_incrementBy (lanes 1) stride x before
  cases bit with
  | false =>
    have hFlag : advanced (lanes 4) = before (lanes 4) := by simp [advanced, setValue, hLane]
    simpa only [unaryReadBranch, unaryReadValues, Bool.false_eq_true, ite_false, hFlag, advanced]
      using hAdvance.seq (runsValues_incrementBy (lanes 4) 1 x advanced)
  | true =>
    let counted := setValue (lanes 3) (before (lanes 3) + 1) advanced
    have hCount : advanced (lanes 3) = before (lanes 3) := by simp [advanced, setValue, hLane]
    have hFlag : counted (lanes 5) = 0 := by simp [counted, advanced, setValue, hLane, hIndex]
    have hCountRun : (incrementBy (lanes 3) 1).RunsValues x 1 advanced counted := by
      simpa only [counted, hCount] using runsValues_incrementBy (lanes 3) 1 x advanced
    have hRun := (hAdvance.seq hCountRun).seq
      (runsValues_incrementBy (lanes 5) 1 x counted)
    simpa only [unaryReadBranch, unaryReadValues, ite_true, hFlag, counted, advanced,
      Nat.zero_add, show stride + 1 + 1 = stride + 2 by omega] using hRun

private theorem runsValues_unaryWindowRead (stride : Nat) (lanes : Fin 8 → R)
    (hLanes : Function.Injective lanes) (x : BinaryWord) (before : R → Nat) (bit : Bool)
    (hLength : before (lanes 0) = x.length) (hIndex : before (lanes 5) = 0)
    (hWork : before (lanes 6) = 0) (hScratch : before (lanes 7) = 0)
    (hRead : x[before (lanes 1)]? = some bit) :
    ∃ ticks ≤ 12 * x.length + stride + 9,
      (unaryWindowRead stride lanes).RunsValues x ticks before
        (unaryReadValues stride lanes bit before) := by
  have hDistinct (i j : Fin 8) (h : i ≠ j) : lanes i ≠ lanes j := fun e ↦ h (hLanes e)
  let address := setValue (lanes 5) (before (lanes 1)) before
  have hOther (i : Fin 8) (hi : i ≠ 5) : address (lanes i) = before (lanes i) :=
    setValue_other (hDistinct i 5 hi) ..
  have hPosition : address (lanes 5) = before (lanes 1) := setValue_same ..
  have hReset : setValue (lanes 5) 0 address = before := by
    simp only [address, setValue_replace, ← hIndex, setValue_current]
  have hCopy : (add (lanes 1) (lanes 5) (lanes 7)).RunsValues
      x (5 * before (lanes 1) + 2) before address := by
    simpa only [address, hIndex, Nat.zero_add] using
      runsValues_add (lanes 1) (lanes 5) (lanes 7) x before
        (hDistinct 1 5 (by decide)) (hDistinct 1 7 (by decide)) (hDistinct 5 7 (by decide))
        hScratch
  have hBranch := runsValues_unaryReadBranch stride lanes hLanes x before bit hIndex
  have hLookup := runsValues_forwardLookup (lanes 0) (lanes 5) (lanes 6) (lanes 7)
    (unaryReadBranch stride lanes) x address
    (hDistinct 0 6 (by decide)) (hDistinct 0 7 (by decide)) (hDistinct 5 6 (by decide))
    (hDistinct 6 7 (by decide)) ((hOther 0 (by decide)).trans hLength)
    ((hOther 6 (by decide)).trans hWork) ((hOther 7 (by decide)).trans hScratch)
    (by simpa only [hPosition, hReset, hRead] using hBranch)
  have hIn := (List.getElem?_eq_some_iff.mp hRead).choose
  have hCost : forwardLookupCost x.length (address (lanes 5)) = 7 * x.length + 5 := by
    rw [hPosition, forwardLookupCost, ite_eq_left hIn]
  refine ⟨_, ?_, hCopy.seq hLookup⟩
  rw [hCost]
  cases bit <;> simp <;> omega

private theorem run_unaryWindow_read (stride : Nat) (lanes : Fin 8 → R)
    (x : BinaryWord) (before after : R → Nat) (ticks : Nat) (output : BinaryWord)
    (hMore : 0 < before (lanes 2))
    (hRun : (unaryWindowRead stride lanes).RunsValues x ticks
      (decrementValues (lanes 2) before) after) :
    let loop := unaryFieldWindow stride lanes
    loop.run x (1 + ticks) (loop.enter (⟨none, before, none, output⟩ : Config R Unit)) =
      some ⟨some (some (Sum.inl (1 : Fin 2))), after, none, output⟩ := by
  let loop := unaryFieldWindow stride lanes
  let body := unaryWindowRead stride lanes
  let link : Option body.Label → Option loop.Label := unaryWindowLink body
  let start := loop.enter (⟨none, before, none, output⟩ : Config R Unit)
  let bodyStart := body.enter
    (⟨none, decrementValues (lanes 2) before, none, output⟩ : Config R Unit)
  have hFirst : step loop.close x start = some (bodyStart.map link) :=
    step_dec_pos (program := loop.close) (reg := lanes 2) rfl rfl hMore
  have hBody := run_link link (target := loop.close) (fun _ ↦ rfl) (hRun output) rfl
  change RegisterMachine.run loop.close x (1 + ticks) start = _
  rw [RegisterMachine.run_add, RegisterMachine.run_succ, hFirst, Option.bind_some,
    RegisterMachine.run_zero, Option.bind_some]
  exact hBody

private theorem run_unaryWindow_stop (stride : Nat) (lanes : Fin 8 → R)
    (x : BinaryWord) {cfg : (unaryFieldWindow stride lanes).Cfg}
    (hPC : cfg.pc = some (some (Sum.inl (1 : Fin 2)))) (hFlag : cfg.values (lanes 5) = 0) :
    (unaryFieldWindow stride lanes).run x 1 cfg = some { cfg with pc := some none } := by
  let loop := unaryFieldWindow stride lanes
  have tick := step_dec_zero (program := loop.close) (x := x) hPC rfl hFlag
  change RegisterMachine.run loop.close x 1 cfg = _
  rw [RegisterMachine.run_succ, tick, Option.bind_some, RegisterMachine.run_zero]
  rfl

private theorem run_unaryWindow_resume (stride : Nat) (lanes : Fin 8 → R)
    (x : BinaryWord) {cfg : (unaryFieldWindow stride lanes).Cfg}
    (hPC : cfg.pc = some (some (Sum.inl (1 : Fin 2)))) (hFlag : 0 < cfg.values (lanes 5)) :
    (unaryFieldWindow stride lanes).run x 1 cfg = some
      { cfg with
        pc := some (some (Sum.inl (0 : Fin 2)))
        values := decrementValues (lanes 5) cfg.values } := by
  let loop := unaryFieldWindow stride lanes
  have tick := step_dec_pos (program := loop.close) (x := x) hPC rfl hFlag
  change RegisterMachine.run loop.close x 1 cfg = _
  rw [RegisterMachine.run_succ, tick, Option.bind_some, RegisterMachine.run_zero]
  rfl

/-- The counted scan stops at the first zero or consumes the entire prepared window. -/
theorem runsValues_unaryFieldWindow_of_reads (stride : Nat) (lanes : Fin 8 → R)
    (hLanes : Function.Injective lanes) (x bits : BinaryWord) (before : R → Nat)
    (hLength : before (lanes 0) = x.length) (hBudget : before (lanes 2) = bits.length)
    (hIndex : before (lanes 5) = 0) (hWork : before (lanes 6) = 0)
    (hScratch : before (lanes 7) = 0)
    (hReads : ∀ i, i < bits.length → x[before (lanes 1) + stride * i]? = bits[i]?) :
    let result := unaryWindowResult bits
    let consumed := result.1 + result.2.toNat
    ∃ ticks ≤ unaryFieldWindowCost stride x.length bits.length, ∃ after : R → Nat,
      (unaryFieldWindow stride lanes).RunsValues x ticks before after ∧
      after (lanes 1) = before (lanes 1) + stride * consumed ∧
      after (lanes 2) = before (lanes 2) - consumed ∧
      after (lanes 3) = before (lanes 3) + result.1 ∧
      after (lanes 4) = before (lanes 4) + result.2.toNat ∧
      ∀ r, r ≠ lanes 1 → r ≠ lanes 2 → r ≠ lanes 3 → r ≠ lanes 4 → after r = before r := by
  have hLane (i j : Fin 8) : lanes i = lanes j ↔ i = j := ⟨fun e ↦ hLanes e, congrArg lanes⟩
  let loop := unaryFieldWindow stride lanes
  induction bits generalizing before with
  | nil =>
    simp only [unaryWindowResult, Bool.toNat_false, Nat.add_zero, Nat.mul_zero, Nat.sub_zero]
    refine ⟨1, by simp [unaryFieldWindowCost], before, ?_, rfl, rfl, rfl, rfl,
      fun _ _ _ _ _ ↦ rfl⟩
    intro output
    let start := loop.enter (⟨none, before, none, output⟩ : Config R Unit)
    have tick := step_dec_zero (program := loop.close) (x := x) (cfg := start)
      (reg := lanes 2) rfl rfl hBudget
    change RegisterMachine.run loop.close x 1 start = _
    rw [RegisterMachine.run_succ, tick, Option.bind_some, RegisterMachine.run_zero]
    rfl
  | cons bit bits ih =>
    let tested := decrementValues (lanes 2) before
    have hTest (i : Fin 8) (hi : i ≠ 2) : tested (lanes i) = before (lanes i) := by
      simp [tested, decrementValues, hLane, hi]
    have hMore : 0 < before (lanes 2) := by rw [hBudget]; simp
    have hThis := hReads 0 (by simp)
    obtain ⟨readTicks, hReadTicks, hRead⟩ := runsValues_unaryWindowRead stride lanes hLanes
      x tested bit ((hTest 0 (by decide)).trans hLength) ((hTest 5 (by decide)).trans hIndex)
      ((hTest 6 (by decide)).trans hWork) ((hTest 7 (by decide)).trans hScratch)
      (by simpa only [hTest 1 (by decide), Nat.mul_zero, Nat.add_zero, List.getElem?_cons_zero]
        using hThis)
    let read := unaryReadValues stride lanes bit tested
    have hHead (output : BinaryWord) : RegisterMachine.run loop.close x (1 + readTicks)
        (loop.enter (⟨none, before, none, output⟩ : Config R Unit)) =
        some ⟨some (some (Sum.inl (1 : Fin 2))), read, none, output⟩ :=
      run_unaryWindow_read stride lanes x before read readTicks output hMore hRead
    cases bit with
    | false =>
      simp only [unaryWindowResult, Bool.toNat_true, Nat.zero_add, Nat.mul_one, Nat.add_zero]
      have hEmpty : read (lanes 5) = 0 := by
        simp [read, unaryReadValues, setValue, hLane, hTest 5 (by decide), hIndex]
      refine ⟨1 + readTicks + 1, ?_, read, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [unaryFieldWindowCost, List.length_cons, Nat.succ_mul]
        omega
      · intro output
        have hStop := run_unaryWindow_stop stride lanes x
          (cfg := ⟨some (some (Sum.inl (1 : Fin 2))), read, none, output⟩) rfl hEmpty
        change RegisterMachine.run loop.close x _ _ = _
        rw [RegisterMachine.run_add, hHead, Option.bind_some]
        exact hStop
      · simp [read, unaryReadValues, setValue, hLane, hTest 1 (by decide)]
      · simp [read, unaryReadValues, tested, decrementValues, setValue, hLane]
      · simp [read, unaryReadValues, setValue, hLane, hTest 3 (by decide)]
      · simp [read, unaryReadValues, hTest 4 (by decide)]
      · intro r hP hB _ hF
        simp [read, unaryReadValues, tested, setValue, decrementValues, hP, hB, hF]
    | true =>
      let advanced := decrementValues (lanes 5) read
      have hFlag : read (lanes 5) = 1 := by simp [read, unaryReadValues]
      have hNextPos : advanced (lanes 1) = before (lanes 1) + stride := by
        simp [advanced, read, unaryReadValues, decrementValues,
          setValue, hLane, hTest 1 (by decide)]
      have hNextBudget : advanced (lanes 2) = before (lanes 2) - 1 := by
        simp [advanced, read, unaryReadValues, tested, decrementValues, setValue, hLane]
      have hNextCount : advanced (lanes 3) = before (lanes 3) + 1 := by
        simp [advanced, read, unaryReadValues, decrementValues,
          setValue, hLane, hTest 3 (by decide)]
      have hNextFlag : advanced (lanes 4) = before (lanes 4) := by
        simp [advanced, read, unaryReadValues, decrementValues,
          setValue, hLane, hTest 4 (by decide)]
      have hFrame (r : R) (hp : r ≠ lanes 1) (hb : r ≠ lanes 2) (hc : r ≠ lanes 3) :
          advanced r = before r := by
        by_cases hi : r = lanes 5
        · subst r
          simp [advanced, decrementValues, hFlag, hIndex]
        · simp [advanced, read, unaryReadValues, tested, decrementValues, setValue, hp, hb, hc, hi]
      have hOther (i : Fin 8) (hp : i ≠ 1) (hb : i ≠ 2) (hc : i ≠ 3) :
          advanced (lanes i) = before (lanes i) :=
        hFrame _ (fun e ↦ hp (hLanes e)) (fun e ↦ hb (hLanes e)) (fun e ↦ hc (hLanes e))
      have hTailRead (i : Nat) (hi : i < bits.length) :
          x[advanced (lanes 1) + stride * i]? = bits[i]? := by
        rw [hNextPos, show before (lanes 1) + stride + stride * i =
          before (lanes 1) + stride * (i + 1) by rw [Nat.mul_succ]; omega]
        exact hReads (i + 1) (by simpa using hi)
      have hLeft : advanced (lanes 2) = bits.length := by rw [hNextBudget, hBudget]; simp
      obtain ⟨tailTicks, hTailTicks, after, hTail, hPos, hBudget', hCount, hSuccess, hUnchanged⟩ :=
        ih advanced ((hOther 0 (by decide) (by decide) (by decide)).trans hLength) hLeft
          ((hOther 5 (by decide) (by decide) (by decide)).trans hIndex)
          ((hOther 6 (by decide) (by decide) (by decide)).trans hWork)
          ((hOther 7 (by decide) (by decide) (by decide)).trans hScratch) hTailRead
      refine ⟨1 + readTicks + 1 + tailTicks, ?_, after, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [unaryFieldWindowCost, List.length_cons, Nat.succ_mul]
        unfold unaryFieldWindowCost at hTailTicks
        omega
      · intro output
        let start := loop.enter (⟨none, before, none, output⟩ : Config R Unit)
        let next := loop.enter (⟨none, advanced, none, output⟩ : Config R Unit)
        have hResume := run_unaryWindow_resume stride lanes x
          (cfg := ⟨some (some (Sum.inl (1 : Fin 2))), read, none, output⟩) rfl
          (by simp [hFlag])
        change RegisterMachine.run loop.close x 1
          ⟨some (some (Sum.inl (1 : Fin 2))), read, none, output⟩ = some next at hResume
        change RegisterMachine.run loop.close x _ start = _
        rw [RegisterMachine.run_add, RegisterMachine.run_add, hHead, Option.bind_some,
          hResume, Option.bind_some]
        exact hTail output
      · rw [hPos, hNextPos]
        simp only [unaryWindowResult, Nat.mul_add, Nat.mul_one]
        omega
      · rw [hBudget', hNextBudget, Nat.sub_sub]
        simp only [unaryWindowResult]
        omega
      · rw [hCount, hNextCount]
        simp only [unaryWindowResult]
        omega
      · simpa only [unaryWindowResult, hNextFlag] using hSuccess
      · intro r hp hb hc hf
        exact (hUnchanged r hp hb hc hf).trans (hFrame r hp hb hc)

/-- Run the scan on an in-range strided window at an ordinary input position. -/
theorem runsValues_unaryFieldWindow (stride : Nat) (lanes : Fin 8 → R)
    (hLanes : Function.Injective lanes) (x : BinaryWord) (start width : Nat)
    (before : R → Nat) (hRange : ∀ i, i < width → start + stride * i < x.length)
    (hLength : before (lanes 0) = x.length) (hStart : before (lanes 1) = start)
    (hBudget : before (lanes 2) = width) (hIndex : before (lanes 5) = 0)
    (hWork : before (lanes 6) = 0) (hScratch : before (lanes 7) = 0) :
    let result := unaryWindowResult (stridedBits x start stride width)
    let consumed := result.1 + result.2.toNat
    ∃ ticks ≤ unaryFieldWindowCost stride x.length width, ∃ after : R → Nat,
      (unaryFieldWindow stride lanes).RunsValues x ticks before after ∧
      after (lanes 1) = before (lanes 1) + stride * consumed ∧
      after (lanes 2) = before (lanes 2) - consumed ∧
      after (lanes 3) = before (lanes 3) + result.1 ∧
      after (lanes 4) = before (lanes 4) + result.2.toNat ∧
      ∀ r, r ≠ lanes 1 → r ≠ lanes 2 → r ≠ lanes 3 → r ≠ lanes 4 → after r = before r := by
  simpa only [length_stridedBits] using
    runsValues_unaryFieldWindow_of_reads stride lanes hLanes x
      (stridedBits x start stride width) before hLength
      (by rwa [length_stridedBits]) hIndex hWork hScratch
      (fun i hi ↦ by
        rw [hStart]
        have hi' : i < width := by simpa only [length_stridedBits] using hi
        exact (getElem?_stridedBits x start stride width i hi' (hRange i hi')).symm)

end PvsNP.RegisterMachine.Fragment
