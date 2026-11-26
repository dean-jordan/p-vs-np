module

public import PvsNP.Circuits.Enumerate
public import PvsNP.Circuits.TruthTable

import Init.Data.List.Find

/-! # Exact bounded circuit search

The complete-table question uses the repository's false-first truth-table
order. The restricted question asks for agreement only on selected inputs.
Both searches enumerate circuits of exactly the budgeted size because extra
constant gates can pad any smaller circuit without changing its output.
-/

public section

namespace PvsNP.MCSP

open AssignmentQueryTree (allAssignments mem_allAssignments)
open Circuits

/-- The complete table is realized by a circuit using at most `s` gates. -/
@[expose] def SizeBounded (n s : Nat) (table : BinaryWord) : Prop :=
  ∃ c : BooleanCircuit n, c.size ≤ s ∧ truthTable n c.eval = table

/-- A circuit of at most `s` gates agrees with `f` on every selected input. -/
@[expose] def BoundedAgreement (n s : Nat) (selected : (Fin n → Bool) → Prop)
    (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ c : BooleanCircuit n, c.size ≤ s ∧ ∀ x, selected x → c.eval x = f x

/-- Any condition on the output function can be tested on the exact-size list. -/
theorem exists_eval_mem_enumerateCircuits_iff (n s : Nat)
    (p : ((Fin n → Bool) → Bool) → Prop) :
    (∃ c ∈ enumerateCircuits n s, p c.eval) ↔
      ∃ c : BooleanCircuit n, c.size ≤ s ∧ p c.eval := by
  constructor
  · rintro ⟨c, hc, hp⟩
    exact ⟨c, by simp only [size_eq_of_mem_enumerateCircuits hc, Nat.le_refl], hp⟩
  · rintro ⟨c, hSize, hp⟩
    obtain ⟨d, hd, hEval⟩ := exists_mem_enumerateCircuits_of_size_le c hSize
    exact ⟨d, hd, (funext hEval).symm ▸ hp⟩

theorem sizeBounded_iff_enumerated (n s : Nat) (table : BinaryWord) :
    SizeBounded n s table ↔
      ∃ c ∈ enumerateCircuits n s, truthTable n c.eval = table :=
  (exists_eval_mem_enumerateCircuits_iff n s (fun f ↦ truthTable n f = table)).symm

theorem sizeBounded_iff_mem_circuitTables (n s : Nat) (table : BinaryWord) :
    SizeBounded n s table ↔
      table ∈ (enumerateCircuits n s).map (fun c ↦ truthTable n c.eval) := by
  rw [sizeBounded_iff_enumerated, List.mem_map]

theorem length_of_sizeBounded {n s : Nat} {table : BinaryWord}
    (h : SizeBounded n s table) : table.length = 2 ^ n := by
  obtain ⟨c, _, rfl⟩ := h
  exact length_truthTable n c.eval

theorem boundedAgreement_iff_enumerated (n s : Nat) (selected : (Fin n → Bool) → Prop)
    (f : (Fin n → Bool) → Bool) :
    BoundedAgreement n s selected f ↔
      ∃ c ∈ enumerateCircuits n s, ∀ x, selected x → c.eval x = f x :=
  (exists_eval_mem_enumerateCircuits_iff n s (fun g ↦ ∀ x, selected x → g x = f x)).symm

/-- For a full table, the complete-table question is agreement on every input. -/
theorem sizeBounded_iff_lookup (n s : Nat) (table : BinaryWord) (h : table.length = 2 ^ n) :
    SizeBounded n s table ↔
      BoundedAgreement n s (fun _ ↦ True) (fun x ↦ tableLookup n table (List.ofFn x)) := by
  constructor
  · rintro ⟨c, hSize, hTable⟩
    refine ⟨c, hSize, fun x _ ↦ ?_⟩
    change c.eval x = tableLookup n table (List.ofFn x)
    rw [← hTable, tableLookup_truthTable]
  · rintro ⟨c, hSize, hAgree⟩
    refine ⟨c, hSize, ?_⟩
    calc
      truthTable n c.eval = truthTable n (fun x ↦ tableLookup n table (List.ofFn x)) :=
        congrArg (truthTable n) (funext fun x ↦ hAgree x True.intro)
      _ = table := truthTable_tableLookup n table h

/-- Search the circuit list for an exact match to the supplied table. -/
@[expose] def decideSizeBounded (n s : Nat) (table : BinaryWord) : Bool :=
  (enumerateCircuits n s).any fun c ↦ truthTable n c.eval == table

theorem decideSizeBounded_eq_true_iff (n s : Nat) (table : BinaryWord) :
    decideSizeBounded n s table = true ↔ SizeBounded n s table := by
  rw [sizeBounded_iff_enumerated]
  simp only [decideSizeBounded, List.any_eq_true, beq_iff_eq]

/-- Return the first listed circuit agreeing on all selected inputs. -/
@[expose] def findBoundedAgreement (n s : Nat) (selected f : (Fin n → Bool) → Bool) :
    Option (BooleanCircuit n) :=
  (enumerateCircuits n s).find? fun c ↦ (allAssignments n).all fun x ↦
    !selected x || (c.eval x == f x)

private theorem all_agrees_eq_true_iff {n : Nat} (selected f g : (Fin n → Bool) → Bool) :
    ((allAssignments n).all fun x ↦ !selected x || (g x == f x)) = true ↔
      ∀ x, selected x = true → g x = f x := by
  rw [List.all_eq_true]
  constructor
  · intro h x hSelected
    simpa [hSelected] using h x (mem_allAssignments x)
  · intro h x _
    cases hSelected : selected x with
    | false => simp
    | true => simp [h x hSelected]

theorem size_eq_and_agrees_of_findBoundedAgreement_eq_some {n s : Nat}
    {selected f : (Fin n → Bool) → Bool} {c : BooleanCircuit n}
    (h : findBoundedAgreement n s selected f = some c) :
    c.size = s ∧ ∀ x, selected x = true → c.eval x = f x := by
  unfold findBoundedAgreement at h
  have hPassed := List.find?_some h
  exact ⟨size_eq_of_mem_enumerateCircuits (List.mem_of_find?_eq_some h),
    (all_agrees_eq_true_iff selected f c.eval).mp hPassed⟩

theorem findBoundedAgreement_isSome_iff (n s : Nat) (selected f : (Fin n → Bool) → Bool) :
    (findBoundedAgreement n s selected f).isSome = true ↔
      BoundedAgreement n s (fun x ↦ selected x = true) f := by
  rw [boundedAgreement_iff_enumerated]
  simp only [findBoundedAgreement, List.find?_isSome, all_agrees_eq_true_iff]

/-- Decide whether there is a bounded circuit agreeing on all selected inputs. -/
@[expose] def decideBoundedAgreement (n s : Nat) (selected f : (Fin n → Bool) → Bool) : Bool :=
  (findBoundedAgreement n s selected f).isSome

theorem decideBoundedAgreement_eq_true_iff (n s : Nat) (selected f : (Fin n → Bool) → Bool) :
    decideBoundedAgreement n s selected f = true ↔
      BoundedAgreement n s (fun x ↦ selected x = true) f :=
  findBoundedAgreement_isSome_iff n s selected f

end PvsNP.MCSP
