module

public import PvsNP.TuringMachine.Registers.Lookup
public import PvsNP.TuringMachine.Registers.Clear

/-! # Lookup in the original input order

The cursor reads in reverse order. A copied input length is consumed alongside
the requested index to convert an in-range index before the cursor is used.
-/

@[expose] public section

namespace PvsNP.RegisterMachine.Fragment

variable {R : Type}

/-- Control phases for subtracting the index and clearing an out-of-range request. -/
inductive ForwardLookupPhase where
  | takeWork | takeIndex | clearIndex

private def forwardLookupPhaseCode : ForwardLookupPhase → Fin 3
  | .takeWork => 0
  | .takeIndex => 1
  | .clearIndex => 2

instance : Finite ForwardLookupPhase :=
  Finite.of_injective forwardLookupPhaseCode (by
    intro a b h
    cases a <;> cases b <;> simp_all [forwardLookupPhaseCode])

/-- Convert a copied length into a reverse offset before following the selected exit. -/
abbrev forwardLookupTail (work index : R) (found missing : Fragment R) : Fragment R where
  Label := ForwardLookupPhase ⊕ (found.Label ⊕ missing.Label)
  entry := some (.inl .takeWork)
  code
    | .inl .takeWork => .dec work (some (.inl .clearIndex)) (some (.inl .takeIndex))
    | .inl .takeIndex => .dec index (found.entry.map (Sum.inr ∘ Sum.inl))
        (some (.inl .takeWork))
    | .inl .clearIndex => .dec index (missing.entry.map (Sum.inr ∘ Sum.inr))
        (some (.inl .clearIndex))
    | .inr (.inl label) => (found.code label).map (Option.map (Sum.inr ∘ Sum.inl))
    | .inr (.inr label) => (missing.code label).map (Option.map (Sum.inr ∘ Sum.inr))

/-- Select a continuation on a bit at an ordinary, zero-based input index. -/
abbrev forwardLookup (length index work scratch : R) (branches : Option Bool → Fragment R) :
    Fragment R :=
  (add length work scratch).seq
    (forwardLookupTail work index (lookup work branches) (branches none))

/-- Total lookup instructions before entering the selected continuation. -/
def forwardLookupCost (length index : Nat) : Nat :=
  if index < length then 7 * length + 5 else 6 * length + index + 4

theorem forwardLookupCost_le (length index : Nat) :
    forwardLookupCost length index ≤ 7 * length + index + 5 := by
  unfold forwardLookupCost
  split <;> omega

theorem forwardLookupCost_polynomiallyBounded {length index : Nat → Nat}
    (hLength : PolynomiallyBounded length) (hIndex : PolynomiallyBounded index) :
    PolynomiallyBounded (fun n ↦ forwardLookupCost (length n) (index n)) :=
  ((((PolynomiallyBounded.const 7).mul hLength).add hIndex).add
    (PolynomiallyBounded.const 5)).mono (fun n ↦ forwardLookupCost_le (length n) (index n))

variable [DecidableEq R]

private def pairedValues (work index : R) (n : Nat) (values : R → Nat) : R → Nat :=
  fun r ↦ if r = work ∨ r = index then values r - n else values r

private theorem run_forwardPairs (work index : R) (found missing : Fragment R) (x : BinaryWord)
    (hIW : index ≠ work) (n : Nat) {cfg : (forwardLookupTail work index found missing).Cfg}
    (hPC : cfg.pc = some (some (.inl .takeWork))) (hW : n ≤ cfg.values work)
    (hI : n ≤ cfg.values index) :
    (forwardLookupTail work index found missing).run x (2 * n) cfg =
      some { cfg with values := pairedValues work index n cfg.values } := by
  induction n generalizing cfg with
  | zero =>
    have hValues : pairedValues work index 0 cfg.values = cfg.values := by
      funext r
      simp [pairedValues]
    simp [hValues]
  | succ n ih =>
    let P := (forwardLookupTail work index found missing).close
    let mid : (forwardLookupTail work index found missing).Cfg := { cfg with
      pc := some (some (.inl .takeIndex))
      values := decrementValues work cfg.values }
    let next : (forwardLookupTail work index found missing).Cfg := { cfg with
      pc := some (some (.inl .takeWork))
      values := decrementValues index mid.values }
    have hMidIndex : mid.values index = cfg.values index := by
      simp [mid, decrementValues, hIW]
    have hNextIndex : next.values index = cfg.values index - 1 := by
      simp [next, decrementValues, hMidIndex]
    have hNextWork : next.values work = cfg.values work - 1 := by
      simp [next, mid, decrementValues, hIW.symm]
    have hStepWork : step P x cfg = some mid := step_dec_pos hPC rfl (by omega)
    have hStepIndex : step P x mid = some next := step_dec_pos rfl rfl (by omega)
    have hRest := ih (cfg := next) rfl (by omega) (by omega)
    have hValues : pairedValues work index n next.values =
        pairedValues work index (n + 1) cfg.values := by
      funext r
      by_cases hWork : r = work
      · subst r
        simp only [pairedValues, true_or, ite_true, hNextWork]
        omega
      · by_cases hIndex : r = index
        · subst r
          simp only [pairedValues, or_true, ite_true, hNextIndex]
          omega
        · simp [pairedValues, next, mid, decrementValues, hWork, hIndex]
    change RegisterMachine.run P x (2 * (n + 1)) cfg = _
    change RegisterMachine.run P x (2 * n) next = _ at hRest
    rw [show 2 * (n + 1) = 2 + 2 * n by omega, RegisterMachine.run_add,
      RegisterMachine.run_succ P x 1, hStepWork, Option.bind_some,
      RegisterMachine.run_succ P x 0, hStepIndex, Option.bind_some, RegisterMachine.run_zero,
      Option.bind_some, hRest, hValues]
    simp [next, hPC]

private theorem run_forwardTail_found (work index : R) (found missing : Fragment R)
    (x : BinaryWord) (before : R → Nat) (output : BinaryWord) (hIW : index ≠ work)
    (hIn : before index < before work) {n : Nat} {after : R → Nat} {nextOutput : BinaryWord}
    (hFound : found.run x n (found.enter (⟨none,
        setValue work (before work - 1 - before index) (setValue index 0 before),
        none, output⟩ : Config R Unit)) = some ⟨some none, after, none, nextOutput⟩) :
    (forwardLookupTail work index found missing).run x (2 * before index + 2 + n)
      ((forwardLookupTail work index found missing).enter (⟨none, before, none, output⟩ :
        Config R Unit)) = some ⟨some none, after, none, nextOutput⟩ := by
  let fragment := forwardLookupTail work index found missing
  let P := fragment.close
  let cfg : Config R Unit := ⟨none, before, none, output⟩
  let start := fragment.enter cfg
  let pairs := { start with values := pairedValues work index (before index) before }
  have hPairs : RegisterMachine.run P x (2 * before index) start = some pairs :=
    run_forwardPairs work index found missing x hIW (before index) rfl (Nat.le_of_lt hIn) (by rfl)
  let mid : fragment.Cfg := { pairs with
    pc := some (some (.inl .takeIndex))
    values := decrementValues work pairs.values }
  have hWork : 0 < pairs.values work := by simp [pairs, pairedValues, Nat.sub_pos_of_lt hIn]
  have hIndex : mid.values index = 0 := by simp [mid, pairs, decrementValues, pairedValues, hIW]
  have hStepWork : step P x pairs = some mid := step_dec_pos rfl rfl hWork
  let f : Option found.Label → Option fragment.Label := Option.map (Sum.inr ∘ Sum.inl)
  have hValues : mid.values =
      setValue work (before work - 1 - before index) (setValue index 0 before) := by
    funext r
    by_cases hW : r = work
    · subst r
      simp [mid, pairs, pairedValues, decrementValues, Nat.sub_right_comm]
    · by_cases hI : r = index
      · subst r
        simp [hIndex, setValue, hIW]
      · simp [mid, pairs, pairedValues, decrementValues, setValue, hW, hI]
  let foundStart : Config R Unit := ⟨none, mid.values, none, output⟩
  have hStepIndex : step P x mid = some ((found.enter foundStart).map f) := by
    exact step_dec_zero rfl rfl hIndex
  have hSource : found.run x n (found.enter foundStart) =
      some ⟨some none, after, none, nextOutput⟩ := by
    simpa only [foundStart, hValues] using hFound
  have hBody := run_link f (target := P) (fun _ ↦ rfl) hSource rfl
  change RegisterMachine.run P x (2 * before index + 2 + n) start = _
  rw [Nat.add_assoc (2 * before index) 2 n]
  rw [RegisterMachine.run_add, hPairs, Option.bind_some, RegisterMachine.run_add,
    RegisterMachine.run_succ P x 1, hStepWork, Option.bind_some,
    RegisterMachine.run_succ P x 0, hStepIndex, Option.bind_some,
    RegisterMachine.run_zero, Option.bind_some]
  exact hBody

private theorem run_forwardTail_missing (work index : R) (found missing : Fragment R)
    (x : BinaryWord) (before : R → Nat) (output : BinaryWord) (hIW : index ≠ work)
    (hOut : before work ≤ before index) {n : Nat} {after : R → Nat} {nextOutput : BinaryWord}
    (hMissing : missing.run x n (missing.enter (⟨none,
        setValue work 0 (setValue index 0 before), none, output⟩ : Config R Unit)) =
      some ⟨some none, after, none, nextOutput⟩) :
    (forwardLookupTail work index found missing).run x (before work + before index + 2 + n)
      ((forwardLookupTail work index found missing).enter (⟨none, before, none, output⟩ :
        Config R Unit)) = some ⟨some none, after, none, nextOutput⟩ := by
  let fragment := forwardLookupTail work index found missing
  let P := fragment.close
  let cfg : Config R Unit := ⟨none, before, none, output⟩
  let start := fragment.enter cfg
  let pairs := { start with values := pairedValues work index (before work) before }
  have hPairs : RegisterMachine.run P x (2 * before work) start = some pairs :=
    run_forwardPairs work index found missing x hIW (before work) rfl (by rfl) hOut
  let clear : fragment.Cfg := { pairs with pc := some (some (.inl .clearIndex)) }
  have hWork : pairs.values work = 0 := by simp [pairs, pairedValues]
  have hToClear : RegisterMachine.run P x (2 * before work + 1) start = some clear := by
    rw [RegisterMachine.run_add, hPairs, Option.bind_some, RegisterMachine.run_succ,
      step_dec_zero (program := P) (x := x) (cfg := pairs) rfl rfl hWork]
    rfl
  let f : Option missing.Label → Option fragment.Label := Option.map (Sum.inr ∘ Sum.inr)
  have hValues : clearValues index clear.values =
      setValue work 0 (setValue index 0 before) := by
    funext r
    by_cases hW : r = work
    · subst r
      simp [clear, pairs, pairedValues, clearValues, hIW.symm]
    · by_cases hI : r = index
      · subst r
        simp [clearValues, setValue, hIW]
      · simp [clear, pairs, pairedValues, clearValues, setValue, hW, hI]
  let missingStart : Config R Unit := ⟨none, clearValues index clear.values, none, output⟩
  have hClear : RegisterMachine.run P x (clear.values index + 1) clear =
      some ((missing.enter missingStart).map f) :=
    run_clear x (program := P) (entry := some (.inl .clearIndex)) (next := f missing.entry)
      (cfg := clear) rfl rfl
  have hSource : missing.run x n (missing.enter missingStart) =
      some ⟨some none, after, none, nextOutput⟩ := by
    simpa only [missingStart, hValues] using hMissing
  have hBody := run_link f (target := P) (fun _ ↦ rfl) hSource rfl
  have hTime : before work + before index + 2 + n =
      (2 * before work + 1) + ((clear.values index + 1) + n) := by
    have hRest : clear.values index = before index - before work := by
      simp [clear, pairs, pairedValues]
    omega
  change RegisterMachine.run P x (before work + before index + 2 + n) start = _
  rw [hTime, RegisterMachine.run_add, hToClear, Option.bind_some,
    RegisterMachine.run_add, hClear, Option.bind_some]
  exact hBody

/-- A successful forward lookup consumes the index, restores both scratch lanes, and
runs the continuation for the ordinary input element (or for `none` past the input). -/
theorem run_forwardLookup (length index work scratch : R)
    (branches : Option Bool → Fragment R) (x : BinaryWord) (before : R → Nat)
    (output : BinaryWord)
    (hLW : length ≠ work) (hLS : length ≠ scratch) (hIW : index ≠ work) (hWS : work ≠ scratch)
    (hLength : before length = x.length) (hWork : before work = 0)
    (hScratch : before scratch = 0) {n : Nat} {after : R → Nat} {nextOutput : BinaryWord}
    (hBody : (branches x[before index]?).run x n ((branches x[before index]?).enter
        (⟨none, setValue index 0 before, none, output⟩ : Config R Unit)) =
      some ⟨some none, after, none, nextOutput⟩) :
    (forwardLookup length index work scratch branches).run x
      (forwardLookupCost x.length (before index) + n)
      ((forwardLookup length index work scratch branches).enter (⟨none, before, none, output⟩ :
        Config R Unit)) = some ⟨some none, after, none, nextOutput⟩ := by
  let copied := setValue work x.length before
  have hCopy : (add length work scratch).RunsValues x (5 * x.length + 2) before copied := by
    simpa [hLength, hWork, copied] using
      runsValues_add length work scratch x before hLW hLS hWS hScratch
  have hCopiedIndex : copied index = before index := setValue_other hIW _ _
  have hCopiedWork : copied work = x.length := setValue_same _ _ _
  have hClear : ∀ offset, clearInputAtIndex work
      (setValue work offset (setValue index 0 copied)) = setValue index 0 before := by
    intro offset
    funext r
    by_cases hW : r = work
    · subst r
      simp [clearInputAtIndex, setValue, hIW.symm, hWork]
    · by_cases hI : r = index
      · subst r
        simp [clearInputAtIndex, setValue, hIW]
      · simp [clearInputAtIndex, setValue, copied, hW, hI]
  by_cases hIn : before index < x.length
  · let converted := setValue work (x.length - 1 - before index) (setValue index 0 copied)
    let convertedCfg : Config R Unit := ⟨none, converted, none, output⟩
    have hConverted : converted work = x.length - 1 - before index := setValue_same _ _ _
    have hIndex : x.reverse[converted work]? = x[before index]? := by
      rw [hConverted]
      exact List.getElem?_reverse' (by omega)
    have hBranch : (branches x.reverse[converted work]?).run x n
        ((branches x.reverse[converted work]?).enter (⟨none, clearInputAtIndex work converted,
          none, output⟩ : Config R Unit)) = some ⟨some none, after, none, nextOutput⟩ := by
      rw [hIndex, hClear]
      exact hBody
    have hLookup := run_lookup work branches x convertedCfg rfl hBranch rfl
    change (lookup work branches).run x (inputAtCost (converted work) x.length + n)
      ((lookup work branches).enter convertedCfg) =
        some ⟨some none, after, none, nextOutput⟩ at hLookup
    have hLookupTime : inputAtCost (converted work) x.length =
        2 * (x.length - 1 - before index) + 3 := by
      rw [hConverted, inputAtCost, ite_eq_left (by omega)]
    rw [hLookupTime] at hLookup
    have hConvertedRun := run_forwardTail_found work index
      (lookup work branches) (branches none) x copied output hIW
      (by simpa only [hCopiedIndex, hCopiedWork] using hIn)
      (by simpa only [hCopiedWork, hCopiedIndex, convertedCfg, converted] using hLookup)
    have hRun := run_seq (hCopy output) rfl hConvertedRun rfl
    have hCost : forwardLookupCost x.length (before index) + n =
        5 * x.length + 2 +
          (2 * copied index + 2 + (2 * (x.length - 1 - before index) + 3 + n)) := by
      rw [forwardLookupCost, ite_eq_left hIn, hCopiedIndex]
      omega
    rw [hCost]
    exact hRun
  · have hOut : x.length ≤ before index := Nat.le_of_not_gt hIn
    have hIndex : x[before index]? = none := List.getElem?_eq_none hOut
    have hValues : setValue work 0 (setValue index 0 copied) = setValue index 0 before := by
      have hEq : clearInputAtIndex work (setValue work 0 (setValue index 0 copied)) =
          setValue work 0 (setValue index 0 copied) := by
        funext r
        by_cases h : r = work <;> simp [clearInputAtIndex, setValue, h]
      exact hEq.symm.trans (hClear 0)
    have hMissing : (branches none).run x n ((branches none).enter (⟨none,
        setValue work 0 (setValue index 0 copied), none, output⟩ : Config R Unit)) =
      some ⟨some none, after, none, nextOutput⟩ := by
      rw [hValues, ← hIndex]
      exact hBody
    have hMissingRun := run_forwardTail_missing work index
      (lookup work branches) (branches none) x copied output hIW
      (by simpa only [hCopiedIndex, hCopiedWork] using hOut) hMissing
    have hRun := run_seq (hCopy output) rfl hMissingRun rfl
    have hCost : forwardLookupCost x.length (before index) + n =
        (5 * x.length + 2) + (copied work + copied index + 2 + n) := by
      rw [forwardLookupCost, ite_eq_right hIn, hCopiedIndex, hCopiedWork]
      omega
    rw [hCost]
    exact hRun

/-- Compose input lookup with a continuation that preserves output. -/
theorem runsValues_forwardLookup (length index work scratch : R)
    (branches : Option Bool → Fragment R) (x : BinaryWord) (before : R → Nat)
    (hLW : length ≠ work) (hLS : length ≠ scratch) (hIW : index ≠ work) (hWS : work ≠ scratch)
    (hLength : before length = x.length) (hWork : before work = 0)
    (hScratch : before scratch = 0) {n : Nat} {after : R → Nat}
    (hBody : (branches x[before index]?).RunsValues x n (setValue index 0 before) after) :
    (forwardLookup length index work scratch branches).RunsValues x
      (forwardLookupCost x.length (before index) + n) before after := by
  intro output
  exact run_forwardLookup length index work scratch branches x before output
    hLW hLS hIW hWS hLength hWork hScratch (hBody output)

end PvsNP.RegisterMachine.Fragment
