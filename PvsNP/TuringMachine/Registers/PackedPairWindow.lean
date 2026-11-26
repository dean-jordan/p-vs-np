module

public import PvsNP.TuringMachine.Registers.BinaryCompare
public import PvsNP.TuringMachine.Registers.PackedPairScan

import PvsNP.Complexity.PackedOffsets
import PvsNP.TuringMachine.Registers.Dispatch
import PvsNP.TuringMachine.Registers.OutputRuns

/-! # Scan a packed pair inside a strided input window

The offset is a physical reverse input position, while the remaining length
counts logical bits. The parser stores its separator and half-symbol state
in a bounded register. Once it encounters a malformed symbol it enters a
sink, so subsequent bits cannot make the window valid.
-/

public section

namespace PvsNP.RegisterMachine.Fragment

variable {R : Type}

private def boundary (seen : Bool) : Fin 7 := if seen then 1 else 0

/-- The first component is the next mode. The optional Boolean identifies
which length to increment: true for the instance, false for the certificate. -/
private def windowTransition (mode : Fin 7) : Option Bool → Fin 7 × Option Bool
  | none => (6, none)
  | some bit => match mode.val with
    | 0 => (if bit then 3 else 2, none)
    | 1 => (if bit then 5 else 4, none)
    | 2 => if bit then (1, none) else (0, some false)
    | 3 => if bit then (6, none) else (0, some false)
    | 4 | 5 => if bit then (6, none) else (1, some true)
    | _ => (6, none)

private abbrev WindowProgress := Fin 7 × Nat × Nat

private def windowStep (state : WindowProgress) (bit : Bool) : WindowProgress :=
  let (mode, inst, cert) := state
  match windowTransition mode (some bit) with
  | (next, none) => (next, inst, cert)
  | (next, some false) => (next, inst, cert + 1)
  | (next, some true) => (next, inst + 1, cert)

private theorem foldl_windowStep_sink (bits : BinaryWord) (inst cert : Nat) :
    bits.foldl windowStep (6, inst, cert) = (6, inst, cert) := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
    change bits.foldl windowStep (6, inst, cert) = _
    exact ih

private def windowCounts (state : WindowProgress) (inst cert : Nat) :
    Option (BinaryWord × BinaryWord) → Prop
  | none => state.1 ≠ 1
  | some (x, y) => state = (1, inst + x.length, cert + y.length)

private theorem windowStep_data (seen lo : Bool) (inst cert : Nat) :
    windowStep (windowStep (boundary seen, inst, cert) lo) false =
      (boundary seen, inst + seen.toNat, cert + (!seen).toNat) := by
  cases seen <;> cases lo <;> rfl

private theorem windowCounts_data (state : WindowProgress) (seen lo : Bool) (inst cert : Nat)
    (after : Option (BinaryWord × BinaryWord))
    (h : windowCounts state (inst + seen.toNat) (cert + (!seen).toNat) after) :
    windowCounts state inst cert (after.map (pushReverseData seen lo)) := by
  cases after with
  | none => exact h
  | some pair =>
    obtain ⟨x, y⟩ := pair
    cases seen <;>
      simpa [windowCounts, pushReverseData, Nat.add_right_comm, Nat.add_assoc] using h

private theorem foldl_windowStep_counts (bits : BinaryWord) (seen : Bool) (inst cert : Nat) :
    windowCounts (bits.foldl windowStep (boundary seen, inst, cert))
      inst cert (scanReverse seen bits) := by
  cases bits with
  | nil => cases seen <;> simp [windowCounts, scanReverse, boundary]
  | cons lo bits =>
    cases bits with
    | nil =>
      cases seen <;> cases lo <;>
        simp [windowCounts, windowStep, windowTransition, scanReverse, boundary]
    | cons hi tail =>
      cases hi with
      | false =>
        simp only [List.foldl_cons, windowStep_data]
        exact windowCounts_data _ seen lo inst cert _
          (foldl_windowStep_counts tail seen (inst + seen.toNat) (cert + (!seen).toNat))
      | true =>
        cases seen <;> cases lo
        · exact foldl_windowStep_counts tail true inst cert
        all_goals
          change windowCounts (tail.foldl windowStep (6, inst, cert)) inst cert none
          rw [foldl_windowStep_sink]
          exact (by decide : (6 : Fin 7) ≠ 1)
termination_by bits.length
decreasing_by all_goals simp only [List.length_cons]; omega

private def countSymbol (lanes : Fin 8 → R) : Option Bool → Fragment R
  | none => skip
  | some seen => incrementBy (if seen then lanes 2 else lanes 3) 1

private def recordWindowStep (lanes : Fin 8 → R) (mode : Fin 7) (bit : Option Bool) : Fragment R :=
  (countSymbol lanes (windowTransition mode bit).2).seq
    (incrementBy (lanes 7) (windowTransition mode bit).1.val)

private def windowBody (lanes : Fin 8 → R) (stride : Nat) : Fragment R :=
  (dispatchFin (lanes 7) (fun mode : Fin 7 ↦ readRegisterBit (lanes 0) (lanes 5) (lanes 6)
    (recordWindowStep lanes mode))).seq (incrementBy (lanes 0) stride)

private def windowFinish (lanes : Fin 8 → R) : Fragment R :=
  dispatchFin (lanes 7) fun mode : Fin 7 ↦ if mode = 1 then incrementBy (lanes 4) 1 else skip

/-- Starting at a reverse offset in lane 0, scan lane 1 many strided bits.
Lanes 2 and 3 accumulate the instance and certificate lengths, respectively.
A valid window increments lane 4. Lanes 5 through 7 must start empty. -/
def packedPairWindow (lanes : Fin 8 → R) (stride : Nat) : Fragment R :=
  (countdown (lanes 1) (windowBody lanes stride)).seq (windowFinish lanes)

/-- Uniform register instruction bound for a physically in-range window. -/
@[expose] def packedPairWindowCost (inputLength width stride : Nat) : Nat :=
  width * (7 * inputLength + stride + 20) + 8

/-- The bound is polynomial for polynomial input length and logical width. -/
theorem packedPairWindowCost_polynomiallyBounded {inputLength width : Nat → Nat} (stride : Nat)
    (hInput : PolynomiallyBounded inputLength) (hWidth : PolynomiallyBounded width) :
    PolynomiallyBounded (fun n ↦ packedPairWindowCost (inputLength n) (width n) stride) :=
  (hWidth.mul ((((PolynomiallyBounded.const 7).mul hInput).add
    (PolynomiallyBounded.const stride)).add (PolynomiallyBounded.const 20))).add
    (PolynomiallyBounded.const 8)

variable [DecidableEq R]

private def countedValues (lanes : Fin 8 → R) (target : Option Bool) (v : R → Nat) : R → Nat :=
  match target with
  | none => v
  | some seen => setValue (if seen then lanes 2 else lanes 3)
      (v (if seen then lanes 2 else lanes 3) + 1) v

private def recordValues (lanes : Fin 8 → R) (mode : Fin 7) (bit : Option Bool)
    (v : R → Nat) : R → Nat :=
  setValue (lanes 7) (windowTransition mode bit).1.val
    (countedValues lanes (windowTransition mode bit).2 v)

private theorem runsValues_recordWindowStep (lanes : Fin 8 → R) (hLanes : Function.Injective lanes)
    (mode : Fin 7) (bit : Option Bool) (x : BinaryWord) (v : R → Nat) (hMode : v (lanes 7) = 0) :
    ∃ ticks ≤ 7, (recordWindowStep lanes mode bit).RunsValues x ticks v
      (recordValues lanes mode bit v) := by
  let target := (windowTransition mode bit).2
  have hDistinct (i j : Fin 8) (h : i ≠ j) : lanes i ≠ lanes j := fun e ↦ h (hLanes e)
  let counted := countedValues lanes target v
  obtain ⟨ticks, hTicks, hCount, hModeCount⟩ : ∃ ticks ≤ 1,
      (countSymbol lanes target).RunsValues x ticks v counted ∧ counted (lanes 7) = 0 := by
    cases hTarget : target with
    | none =>
      refine ⟨0, by decide, ?_, ?_⟩
      · simpa [countSymbol, counted, countedValues, hTarget] using runsValues_skip x v
      · simpa [counted, countedValues, hTarget] using hMode
    | some seen =>
      let lane := if seen then lanes 2 else lanes 3
      have hLane : lanes 7 ≠ lane := by
        cases seen
        · exact hDistinct 7 3 (by decide)
        · exact hDistinct 7 2 (by decide)
      refine ⟨1, by decide, ?_, ?_⟩
      · simpa only [countSymbol, counted, countedValues, hTarget, lane] using
          runsValues_incrementBy lane 1 x v
      · simpa only [counted, countedValues, hTarget, lane] using
          (setValue_other hLane (v lane + 1) v).trans hMode
  refine ⟨ticks + (windowTransition mode bit).1.val, ?_, ?_⟩
  · have := (windowTransition mode bit).1.isLt
    omega
  · simpa only [recordWindowStep, recordValues, counted, target, hModeCount, Nat.zero_add] using
      hCount.seq (runsValues_incrementBy (lanes 7) (windowTransition mode bit).1.val x counted)

private theorem runsValues_dispatchKey (state : R) (branches : Fin 7 → Fragment R)
    (key : Fin 7) (x : BinaryWord) (v : R → Nat) (hKey : v state = key.val)
    {ticks : Nat} {after : R → Nat}
    (hRun : (branches key).RunsValues x ticks (clearValues state v) after) :
    (dispatchFin state branches).RunsValues x (key.val + 1 + ticks) v after := by
  intro output
  let cfg : Config R Unit := ⟨none, v, none, output⟩
  have hFits : cfg.values state < 7 := by change v state < 7; rw [hKey]; exact key.isLt
  have hSame : (⟨cfg.values state, hFits⟩ : Fin 7) = key := Fin.ext hKey
  subst key
  exact run_dispatchFin state branches x cfg hFits (hRun output) rfl

private def bodyValues (lanes : Fin 8 → R) (stride : Nat) (mode : Fin 7) (bit : Bool)
    (v : R → Nat) : R → Nat :=
  setValue (lanes 0) (v (lanes 0) + stride)
    (recordValues lanes mode (some bit) (clearValues (lanes 7) v))

private theorem runsValues_windowBody (lanes : Fin 8 → R) (hLanes : Function.Injective lanes)
    (stride : Nat) (mode : Fin 7) (bit : Bool) (x : BinaryWord) (v : R → Nat)
    (hMode : v (lanes 7) = mode.val) (hLookup : x.reverse[v (lanes 0)]? = some bit)
    (hIndex : v (lanes 5) = 0) (hScratch : v (lanes 6) = 0) :
    ∃ ticks ≤ 7 * x.length + stride + 19,
      (windowBody lanes stride).RunsValues x ticks v (bodyValues lanes stride mode bit v) := by
  have hLane (i j : Fin 8) : lanes i = lanes j ↔ i = j := ⟨fun e ↦ hLanes e, congrArg lanes⟩
  have hDistinct (i j : Fin 8) (h : i ≠ j) : lanes i ≠ lanes j := fun e ↦ h (hLanes e)
  let cleared := clearValues (lanes 7) v
  have hClearMode : cleared (lanes 7) = 0 := by simp [cleared, clearValues]
  have hClearPos : cleared (lanes 0) = v (lanes 0) := by simp [cleared, clearValues, hLane]
  have hClearIndex : cleared (lanes 5) = 0 := by simp [cleared, clearValues, hLane, hIndex]
  have hClearScratch : cleared (lanes 6) = 0 := by simp [cleared, clearValues, hLane, hScratch]
  obtain ⟨writeTicks, hWriteTicks, hWrite⟩ :=
    runsValues_recordWindowStep lanes hLanes mode (some bit) x cleared hClearMode
  have hRead := runsValues_readRegisterBit (lanes 0) (lanes 5) (lanes 6)
    (recordWindowStep lanes mode) x cleared
    (hDistinct 0 5 (by decide)) (hDistinct 0 6 (by decide)) (hDistinct 5 6 (by decide))
    hClearIndex hClearScratch (by simpa only [hClearPos, hLookup] using hWrite)
  let recorded := recordValues lanes mode (some bit) cleared
  have hDispatch := runsValues_dispatchKey (lanes 7)
    (fun key ↦ readRegisterBit (lanes 0) (lanes 5) (lanes 6) (recordWindowStep lanes key))
    mode x v hMode hRead
  have hReadPos : recorded (lanes 0) = v (lanes 0) := by
    cases h : (windowTransition mode (some bit)).2 with
    | none => simp [recorded, recordValues, countedValues, h, setValue, hLane, hClearPos]
    | some which =>
      cases which <;> simp [recorded, recordValues, countedValues, h, setValue, hLane, hClearPos]
  have hRun := hDispatch.seq (runsValues_incrementBy (lanes 0) stride x recorded)
  refine ⟨_, ?_, by simpa only [windowBody, bodyValues, hReadPos, recorded, cleared] using hRun⟩
  have hPos := (List.getElem?_eq_some_iff.mp hLookup).choose
  simp only [List.length_reverse] at hPos
  have hReadCost := inputAtCost_le (cleared (lanes 0)) x.length
  have hModeBound := mode.isLt
  change mode.val + 1 + (5 * cleared (lanes 0) + 2 +
    (inputAtCost (cleared (lanes 0)) x.length + writeTicks)) + stride ≤ _
  rw [hClearPos] at hReadCost ⊢
  omega

private def windowLoopCost (inputLength width stride : Nat) : Nat :=
  width * (7 * inputLength + stride + 20) + 1

private theorem runsValues_windowLoop (lanes : Fin 8 → R) (hLanes : Function.Injective lanes)
    (stride : Nat) (x bits : BinaryWord) (v : R → Nat) (mode : Fin 7)
    (hMode : v (lanes 7) = mode.val) (hWidth : v (lanes 1) = bits.length)
    (hIndex : v (lanes 5) = 0) (hScratch : v (lanes 6) = 0)
    (hRead : ∀ i, i < bits.length → x.reverse[v (lanes 0) + stride * i]? = bits[i]?) :
    let result := bits.foldl windowStep (mode, v (lanes 2), v (lanes 3))
    ∃ ticks ≤ windowLoopCost x.length bits.length stride, ∃ after : R → Nat,
      (countdown (lanes 1) (windowBody lanes stride)).RunsValues x ticks v after ∧
      after (lanes 0) = v (lanes 0) + stride * bits.length ∧ after (lanes 1) = 0 ∧
      after (lanes 2) = result.2.1 ∧ after (lanes 3) = result.2.2 ∧
      after (lanes 7) = result.1.val ∧
      ∀ r, r ≠ lanes 0 → r ≠ lanes 1 → r ≠ lanes 2 → r ≠ lanes 3 → r ≠ lanes 7 → after r = v r := by
  have hLane (i j : Fin 8) : lanes i = lanes j ↔ i = j := ⟨fun e ↦ hLanes e, congrArg lanes⟩
  induction bits generalizing v mode with
  | nil =>
    simp only [List.foldl_nil, List.length_nil, Nat.mul_zero, Nat.add_zero]
    refine ⟨1, by simp [windowLoopCost], v, ?_, rfl, hWidth, rfl, rfl, hMode,
      fun _ _ _ _ _ _ ↦ rfl⟩
    intro output
    let frag := countdown (lanes 1) (windowBody lanes stride)
    let cfg := frag.enter (⟨none, v, none, output⟩ : Config R Unit)
    exact run_countdown_zero (counter := lanes 1) (body := windowBody lanes stride)
      (cfg := cfg) rfl hWidth
  | cons bit bits ih =>
    let tested := decrementValues (lanes 1) v
    let advanced := bodyValues lanes stride mode bit tested
    let next := windowStep (mode, v (lanes 2), v (lanes 3)) bit
    have hTestPos : tested (lanes 0) = v (lanes 0) := by simp [tested, decrementValues, hLane]
    have hTestMode : tested (lanes 7) = mode.val := by simp [tested, decrementValues, hLane, hMode]
    have hTestIndex : tested (lanes 5) = 0 := by simp [tested, decrementValues, hLane, hIndex]
    have hTestScratch : tested (lanes 6) = 0 := by simp [tested, decrementValues, hLane, hScratch]
    obtain ⟨bodyTicks, hBodyCost, hBody⟩ := runsValues_windowBody lanes hLanes stride mode bit x
      tested hTestMode (by simpa [hTestPos] using hRead 0 (by simp)) hTestIndex hTestScratch
    have hNextPos : advanced (lanes 0) = v (lanes 0) + stride := by
      simp [advanced, bodyValues, hTestPos]
    have hAdvanceFrame (r : R) (h0 : r ≠ lanes 0) (h2 : r ≠ lanes 2)
        (h3 : r ≠ lanes 3) (h7 : r ≠ lanes 7) : advanced r = tested r := by
      cases h : (windowTransition mode (some bit)).2 with
      | none => simp [advanced, bodyValues, recordValues, countedValues, setValue,
          clearValues, h, h0, h7]
      | some which => cases which <;> simp [advanced, bodyValues, recordValues, countedValues,
          setValue, clearValues, h, h0, h2, h3, h7]
    have hNextCount : advanced (lanes 1) = bits.length := by
      rw [hAdvanceFrame _ (by simp [hLane]) (by simp [hLane]) (by simp [hLane]) (by simp [hLane])]
      simp [tested, decrementValues, hWidth]
    have hNextMode : advanced (lanes 7) = next.1.val := by
      simp only [advanced, bodyValues, setValue_other (show lanes 7 ≠ lanes 0 by simp [hLane]),
        recordValues, setValue_same]
      cases h : windowTransition mode (some bit) with
      | mk q which =>
        cases which with
        | none => simp [next, windowStep, h]
        | some yes => cases yes <;> simp [next, windowStep, h]
    have hNextCounts : (advanced (lanes 2), advanced (lanes 3)) = next.2 := by
      cases h : windowTransition mode (some bit) with
      | mk q which =>
        cases which with
        | none =>
          simp [advanced, bodyValues, recordValues, countedValues, setValue, clearValues,
            tested, decrementValues, h, hLane, next, windowStep]
        | some yes =>
          cases yes <;> simp [advanced, bodyValues, recordValues, countedValues, setValue,
            clearValues, tested, decrementValues, h, hLane, next, windowStep]
    have hNextInst : advanced (lanes 2) = next.2.1 := congrArg Prod.fst hNextCounts
    have hNextCert : advanced (lanes 3) = next.2.2 := congrArg Prod.snd hNextCounts
    have hNextIndex : advanced (lanes 5) = 0 := by
      rw [hAdvanceFrame _ (by simp [hLane]) (by simp [hLane]) (by simp [hLane]) (by simp [hLane])]
      exact hTestIndex
    have hNextScratch : advanced (lanes 6) = 0 := by
      rw [hAdvanceFrame _ (by simp [hLane]) (by simp [hLane]) (by simp [hLane]) (by simp [hLane])]
      exact hTestScratch
    have hTailBit (i : Nat) (hi : i < bits.length) :
        x.reverse[advanced (lanes 0) + stride * i]? = bits[i]? := by
      rw [hNextPos, show v (lanes 0) + stride + stride * i = v (lanes 0) + stride * (i + 1) by
        rw [Nat.mul_succ]; omega]
      exact hRead (i + 1) (by simpa using hi)
    obtain ⟨tailTicks, hTailCost, after, hTail, hPos, hZero, hInst, hCert, hFinalMode, hFrame⟩ :=
      ih advanced next.1 hNextMode hNextCount hNextIndex hNextScratch hTailBit
    simp only [hNextInst, hNextCert, Prod.eta] at hInst hCert hFinalMode
    refine ⟨1 + bodyTicks + tailTicks, ?_, after, ?_, ?_, hZero, hInst, hCert, hFinalMode, ?_⟩
    · rw [windowLoopCost, List.length_cons, Nat.succ_mul]
      unfold windowLoopCost at hTailCost
      omega
    · intro output
      let frag := countdown (lanes 1) (windowBody lanes stride)
      let start := frag.enter (⟨none, v, none, output⟩ : Config R Unit)
      let mid := frag.enter (⟨none, advanced, none, output⟩ : Config R Unit)
      have hPositive : 0 < v (lanes 1) := by rw [hWidth]; simp
      have hStep := run_countdown_iteration (counter := lanes 1) (cfg := start)
        rfl hPositive (hBody output) rfl
      change RegisterMachine.run frag.close x (1 + bodyTicks) start = some mid at hStep
      change RegisterMachine.run frag.close x _ start = _
      rw [RegisterMachine.run_add, hStep, Option.bind_some]
      exact hTail output
    · rw [hPos, hNextPos, List.length_cons, Nat.mul_succ]
      omega
    · intro r h0 h1 h2 h3 h7
      rw [hFrame r h0 h1 h2 h3 h7, hAdvanceFrame r h0 h2 h3 h7]
      simp [tested, decrementValues, h1]

private theorem runsValues_windowFinish (lanes : Fin 8 → R) (hLanes : Function.Injective lanes)
    (mode : Fin 7) (x : BinaryWord) (v : R → Nat) (hMode : v (lanes 7) = mode.val) :
    ∃ ticks ≤ 7, (windowFinish lanes).RunsValues x ticks v
      (setValue (lanes 4) (v (lanes 4) + (decide (mode = 1)).toNat) (clearValues (lanes 7) v)) := by
  let cleared := clearValues (lanes 7) v
  have hOther : cleared (lanes 4) = v (lanes 4) := by
    have h : lanes 4 ≠ lanes 7 := fun e ↦ (by decide : (4 : Fin 8) ≠ 7) (hLanes e)
    simp [cleared, clearValues, h]
  by_cases hGood : mode = 1
  · subst mode
    refine ⟨3, by decide, ?_⟩
    have hRun := runsValues_dispatchKey (lanes 7)
      (fun key : Fin 7 ↦ if key = 1 then incrementBy (lanes 4) 1 else skip)
      1 x v hMode (ticks := 1) (by simpa using runsValues_incrementBy (lanes 4) 1 x cleared)
    have hTime : (1 : Fin 7).val + 1 + 1 = 3 := rfl
    simpa only [windowFinish, hTime, hOther, decide_true, Bool.toNat_true] using hRun
  · refine ⟨mode.val + 1, by have := mode.isLt; omega, ?_⟩
    have hRun := runsValues_dispatchKey (lanes 7)
      (fun key : Fin 7 ↦ if key = 1 then incrementBy (lanes 4) 1 else skip)
      mode x v hMode (ticks := 0) (by simpa [hGood] using runsValues_skip x cleared)
    have hRestore : setValue (lanes 4) (v (lanes 4)) (clearValues (lanes 7) v) = cleared := by
      change setValue (lanes 4) (v (lanes 4)) cleared = cleared
      rw [← hOther, setValue_current]
    simpa only [windowFinish, hGood, decide_false, Bool.toNat_false, Nat.add_zero,
      hRestore] using hRun

/-- The left field of a packed input occupies every other position after the
right field and separator in reverse input order. -/
theorem packedPairWindow_read_left (left right : BinaryWord) {i : Nat} (hi : i < left.length) :
    (packedPair left right).reverse[2 * (right.length + 1) + 2 * i]? = left.reverse[i]? := by
  let j := left.length - 1 - i
  have hj : j < left.length := by dsimp [j]; omega
  have hSum : (2 * (right.length + 1) + 2 * i) + (2 * j + 1) + 1 =
      (packedPair left right).length := by
    rw [length_packedPair]
    dsimp [j]
    omega
  rw [List.getElem?_reverse' hSum, getElem?_packedPair_left _ _ hj]
  exact (List.getElem?_reverse' (l := left) (i := i) (j := j) (by dsimp [j]; omega)).symm

/-- Scan all logical bits in a prepared reverse strided window. On malformed data,
validity stays unchanged. On a canonical pair, the two lengths are added and
validity increases by one. Both the width and the internal mode are consumed. -/
theorem runsValues_packedPairWindow (lanes : Fin 8 → R) (hLanes : Function.Injective lanes)
    (stride : Nat) (x raw : BinaryWord) (start : Nat) (v : R → Nat)
    (hStart : v (lanes 0) = start) (hWidth : v (lanes 1) = raw.length)
    (hIndex : v (lanes 5) = 0) (hScratch : v (lanes 6) = 0) (hMode : v (lanes 7) = 0)
    (hRead : ∀ i, i < raw.length → x.reverse[start + stride * i]? = raw.reverse[i]?) :
    ∃ ticks ≤ packedPairWindowCost x.length raw.length stride, ∃ after : R → Nat,
      (packedPairWindow lanes stride).RunsValues x ticks v after ∧
      after (lanes 0) = start + stride * raw.length ∧ after (lanes 1) = 0 ∧ after (lanes 7) = 0 ∧
      (match decodePackedPair raw with
       | none => after (lanes 4) = v (lanes 4)
       | some (u, w) => after (lanes 4) = v (lanes 4) + 1 ∧
           after (lanes 2) = v (lanes 2) + u.length ∧ after (lanes 3) = v (lanes 3) + w.length) ∧
      ∀ r, r ≠ lanes 0 → r ≠ lanes 1 → r ≠ lanes 2 → r ≠ lanes 3 → r ≠ lanes 4 →
        r ≠ lanes 7 → after r = v r := by
  let progress := raw.reverse.foldl windowStep (boundary false, v (lanes 2), v (lanes 3))
  obtain ⟨loopTicks, hLoopCost, mid, hLoop, hPos, hZero, hInst, hCert, hMidMode, hFrame⟩ :=
    runsValues_windowLoop lanes hLanes stride x raw.reverse v (boundary false) hMode
      (by simpa only [List.length_reverse] using hWidth) hIndex hScratch
      (by simpa only [hStart, List.length_reverse] using hRead)
  obtain ⟨finishTicks, hFinishCost, hFinish⟩ :=
    runsValues_windowFinish lanes hLanes progress.1 x mid hMidMode
  let after := setValue (lanes 4) (mid (lanes 4) + (decide (progress.1 = 1)).toNat)
    (clearValues (lanes 7) mid)
  have hLane (i j : Fin 8) : lanes i = lanes j ↔ i = j := ⟨fun e ↦ hLanes e, congrArg lanes⟩
  have hValid : mid (lanes 4) = v (lanes 4) := by
    apply hFrame <;> simp [hLane]
  refine ⟨loopTicks + finishTicks, ?_, after, hLoop.seq hFinish, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_reverse, windowLoopCost] at hLoopCost
    unfold packedPairWindowCost
    omega
  · simp [after, setValue, clearValues, hLane, hPos, hStart]
  · simp [after, setValue, clearValues, hLane, hZero]
  · simp [after, setValue, clearValues, hLane]
  · have hCounts : windowCounts progress (v (lanes 2)) (v (lanes 3)) (scanReverse false raw.reverse)
        := foldl_windowStep_counts raw.reverse false (v (lanes 2)) (v (lanes 3))
    cases hDecoded : decodePackedPair raw with
    | none =>
      have hScan : scanReverse false raw.reverse = none := by
        cases hParsed : scanReverse false raw.reverse with
        | none => rfl
        | some pair =>
          obtain ⟨u, w⟩ := pair
          have hParsed' :
              scanReverse false raw.reverse = some (u.reverse.reverse, w.reverse.reverse) := by
            simpa only [List.reverse_reverse] using hParsed
          have hOther := scanReverse_eq_some_iff.mp hParsed'
          rw [hDecoded] at hOther
          contradiction
      have hBad : progress.1 ≠ 1 := by simpa only [hScan, windowCounts] using hCounts
      simp [after, hValid, hBad]
    | some pair =>
      obtain ⟨u, w⟩ := pair
      have hScan := scanReverse_eq_some_iff.mpr hDecoded
      have hGood : progress = (1, v (lanes 2) + u.length, v (lanes 3) + w.length) := by
        simpa only [hScan, windowCounts, List.length_reverse] using hCounts
      change mid (lanes 2) = progress.2.1 at hInst
      change mid (lanes 3) = progress.2.2 at hCert
      rw [hGood] at hInst hCert
      simp [after, setValue, clearValues, hLane, hGood, hValid, hInst, hCert]
  · intro r h0 h1 h2 h3 h4 h7
    simp [after, setValue, clearValues, h4, h7, hFrame r h0 h1 h2 h3 h7]

end PvsNP.RegisterMachine.Fragment
