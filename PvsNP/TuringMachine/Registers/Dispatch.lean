module

public import PvsNP.TuringMachine.Registers.Clear
public import PvsNP.TuringMachine.Registers.Fragments

import Mathlib.Basic.Finite.Sigma

/-! # Dispatch on a finite register key -/

@[expose] public section

namespace PvsNP.RegisterMachine.Fragment

variable {R K : Type} {n : Nat}

/-- Dispatch has one test per key and separate labels for every branch body. -/
abbrev DispatchLabel (branches : Fin n → Fragment R) :=
  Fin n ⊕ (Σ key, (branches key).Label)

instance (branches : Fin n → Fragment R) : Finite (DispatchLabel branches) := by
  unfold DispatchLabel
  let _ : ∀ key, Finite (branches key).Label := fun key ↦ (branches key).finiteLabel
  infer_instance

/-- Link a branch's labels into the common control, sharing the fragment exit. -/
abbrev dispatchBranchMap (branches : Fin n → Fragment R) (key : Fin n) :
    Option (branches key).Label → Option (DispatchLabel branches) :=
  Option.map fun label ↦ .inr ⟨key, label⟩

/-- Decrement the key until its zero test selects the linked branch. With no available
key (or a key beyond the last test), the control goes directly to the exit. -/
abbrev dispatchFin (index : R) (branches : Fin n → Fragment R) : Fragment R where
  Label := DispatchLabel branches
  entry := if h : 0 < n then some (.inl ⟨0, h⟩) else none
  code
    | .inl key =>
      .dec index (dispatchBranchMap branches key (branches key).entry)
        (if h : key.val + 1 < n then some (.inl ⟨key.val + 1, h⟩) else none)
    | .inr ⟨key, label⟩ => ((branches key).code label).map (dispatchBranchMap branches key)

variable [DecidableEq R]

/-- The selected branch starts with the key lane cleared. -/
def dispatchBranchInput (index : R) (cfg : Config R K) : Config R Unit :=
  ⟨none, clearValues index cfg.values, cfg.cursor, cfg.output⟩

private theorem run_dispatchFrom (index : R) (branches : Fin n → Fragment R) (x : BinaryWord)
    (remaining : Nat) (test selected : Fin n) (hPosition : test.val + remaining = selected.val)
    {cfg : (dispatchFin index branches).Cfg} (hPC : cfg.pc = some (some (.inl test)))
    (hKey : cfg.values index = remaining) :
    (dispatchFin index branches).run x (remaining + 1) cfg =
      some { cfg with
        pc := some (dispatchBranchMap branches selected (branches selected).entry)
        values := clearValues index cfg.values } := by
  let P := (dispatchFin index branches).close
  induction remaining generalizing test cfg with
  | zero =>
    have hSame : test = selected := Fin.ext (by omega)
    subst selected
    have hStep : step P x cfg =
        some { cfg with pc := some (dispatchBranchMap branches test (branches test).entry) } :=
      step_dec_zero hPC rfl hKey
    change RegisterMachine.run P x (0 + 1) cfg = _
    rw [RegisterMachine.run_succ, hStep, Option.bind_some, RegisterMachine.run_zero,
      clearValues_of_zero hKey]
  | succ remaining ih =>
    have hAdvance : test.val + 1 < n := by have := selected.isLt; omega
    let nextTest : Fin n := ⟨test.val + 1, hAdvance⟩
    let mid : (dispatchFin index branches).Cfg := { cfg with
      pc := some (some (.inl nextTest))
      values := decrementValues index cfg.values }
    have hCode : P (some (.inl test)) =
        .dec index (dispatchBranchMap branches test (branches test).entry)
          (some (.inl nextTest)) := by
      change Instruction.dec index (dispatchBranchMap branches test (branches test).entry)
        (if h : test.val + 1 < n then
          some (Sum.inl ⟨test.val + 1, h⟩ : DispatchLabel branches) else none) = _
      rw [dite_eq_left hAdvance]
    have hStep : step P x cfg = some mid := step_dec_pos hPC hCode (by omega)
    have hMid : mid.values index = remaining := by simp [mid, decrementValues, hKey]
    have hNextPosition : nextTest.val + remaining = selected.val := by
      dsimp [nextTest]
      omega
    have hRest := ih nextTest hNextPosition (cfg := mid) rfl hMid
    have hClear : clearValues index mid.values = clearValues index cfg.values := by
      funext r
      by_cases h : r = index <;> simp [mid, clearValues, decrementValues, h]
    change RegisterMachine.run P x (remaining + 1) mid = _ at hRest
    change RegisterMachine.run P x ((remaining + 1) + 1) cfg = _
    rw [RegisterMachine.run_succ, hStep, Option.bind_some, hRest, hClear]

/-- The dispatch selects the branch at the valid key in one instruction per unit and
one final zero test. Its cursor, output, and all other registers retain their values. -/
theorem run_dispatchFin_start (index : R) (branches : Fin n → Fragment R) (x : BinaryWord)
    (cfg : Config R K) (hKey : cfg.values index < n) :
    let selected : Fin n := ⟨cfg.values index, hKey⟩
    (dispatchFin index branches).run x (cfg.values index + 1)
        ((dispatchFin index branches).enter cfg) =
      some (((branches selected).enter (dispatchBranchInput index cfg)).map
        (dispatchBranchMap branches selected)) := by
  let selected : Fin n := ⟨cfg.values index, hKey⟩
  have hPositive : 0 < n := by omega
  let first : Fin n := ⟨0, hPositive⟩
  have hStart : ((dispatchFin index branches).enter cfg).pc = some (some (.inl first)) := by
    simp [enter, dispatchFin, hPositive, first]
  exact run_dispatchFrom index branches x (cfg.values index) first selected
    (Nat.zero_add _) hStart rfl

/-- Execute the selected branch after dispatch with no instruction at the boundary. -/
theorem run_dispatchFin (index : R) (branches : Fin n → Fragment R) (x : BinaryWord)
    (cfg : Config R K) (hKey : cfg.values index < n) {cost : Nat}
    {next : (branches ⟨cfg.values index, hKey⟩).Cfg}
    (hRun : (branches ⟨cfg.values index, hKey⟩).run x cost
      ((branches ⟨cfg.values index, hKey⟩).enter (dispatchBranchInput index cfg)) = some next)
    (hExit : next.pc = some none) :
    (dispatchFin index branches).run x (cfg.values index + 1 + cost)
        ((dispatchFin index branches).enter cfg) =
      some (next.map (dispatchBranchMap branches ⟨cfg.values index, hKey⟩)) := by
  let selected : Fin n := ⟨cfg.values index, hKey⟩
  have hStart := run_dispatchFin_start index branches x cfg hKey
  have hBranch := run_link (dispatchBranchMap branches selected)
    (target := (dispatchFin index branches).close) (fun _ ↦ rfl) hRun hExit
  change RegisterMachine.run (dispatchFin index branches).close x _ _ = _ at hStart ⊢
  rw [RegisterMachine.run_add, hStart, Option.bind_some]
  exact hBranch

end PvsNP.RegisterMachine.Fragment
