module

public import PvsNP.Circuits.BooleanChain
public import PvsNP.Circuits.InputSupport

import Mathlib.Data.Fintype.Basic

/-! # A negation lower bound for Boolean circuits

We count steps where any previously computed wire falls along a chain. A monotone gate
preserves this set, and a NOT gate can introduce only steps where its operand rises.
-/

public section

namespace PvsNP.Circuits

variable {k n m : Nat}

/-- The steps at which at least one wire changes from true to false. -/
def badSteps (x : Fin (k + 1) → Fin n → Bool) : Finset (Fin k) :=
  Finset.univ.filter fun i ↦ ∃ j : Fin n, x i.castSucc j = true ∧ x i.succ j = false

@[simp] theorem mem_badSteps {x : Fin (k + 1) → Fin n → Bool} {i : Fin k} :
    i ∈ badSteps x ↔ ∃ j : Fin n, x i.castSucc j = true ∧ x i.succ j = false := by
  simp [badSteps]

theorem fallSteps_subset_badSteps (x : Fin (k + 1) → Fin n → Bool) (j : Fin n) :
    fallSteps (fun i ↦ x i j) ⊆ badSteps x := by
  intro i hi
  exact mem_badSteps.mpr ⟨j, mem_fallSteps.mp hi⟩

theorem badSteps_eq_empty_of_mono (x : Fin (k + 1) → Fin n → Bool)
    (hMono : ∀ (i : Fin k) (j : Fin n), x i.castSucc j = true → x i.succ j = true) :
    badSteps x = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  obtain ⟨j, hBefore, hAfter⟩ := mem_badSteps.mp hi
  exact Bool.noConfusion ((hMono i j hBefore).symm.trans hAfter)

private theorem mono_at_step_of_notMem_badSteps (x : Fin (k + 1) → Fin n → Bool) (i : Fin k)
    (hMissing : i ∉ badSteps x) (j : Fin n) : x i.castSucc j = true → x i.succ j = true := by
  intro hBefore
  cases hAfter : x i.succ j with
  | false => exact (hMissing (mem_badSteps.mpr ⟨j, hBefore, hAfter⟩)).elim
  | true => rfl

private theorem badSteps_extend_subset_of_mono (gate : Gate n)
    (hMono : ∀ x y : Fin n → Bool, (∀ j, x j = true → y j = true) →
      gate.eval x = true → gate.eval y = true) (x : Fin (k + 1) → Fin n → Bool) :
    badSteps (fun i ↦ gate.extend (x i)) ⊆ badSteps x := by
  intro i hi
  obtain ⟨j, hBefore, hAfter⟩ := mem_badSteps.mp hi
  revert hBefore hAfter
  refine Fin.lastCases ?_ (fun w ↦ ?_) j
  · intro hBefore hAfter
    rw [Gate.extend_last] at hBefore hAfter
    by_contra hMissing
    have hTrue := hMono _ _ (mono_at_step_of_notMem_badSteps x i hMissing) hBefore
    exact Bool.noConfusion (hTrue.symm.trans hAfter)
  · intro hBefore hAfter
    rw [Gate.extend_castSucc] at hBefore hAfter
    exact mem_badSteps.mpr ⟨w, hBefore, hAfter⟩

private theorem badSteps_extend_not_subset (x : Fin (k + 1) → Fin n → Bool) (src : Fin n) :
    badSteps (fun i ↦ (Gate.not src).extend (x i)) ⊆ badSteps x ∪ riseSteps (fun i ↦ x i src) := by
  intro i hi
  obtain ⟨j, hBefore, hAfter⟩ := mem_badSteps.mp hi
  revert hBefore hAfter
  refine Fin.lastCases ?_ (fun w ↦ ?_) j
  · intro hBefore hAfter
    simp only [Gate.extend_last, Gate.eval, Bool.not_eq_true', Bool.not_eq_false'] at hBefore hAfter
    exact Finset.mem_union_right _ (mem_riseSteps.mpr ⟨hBefore, hAfter⟩)
  · intro hBefore hAfter
    rw [Gate.extend_castSucc] at hBefore hAfter
    exact Finset.mem_union_left _ (mem_badSteps.mpr ⟨w, hBefore, hAfter⟩)

private def gateNegationCount : Gate n → Nat
  | .not _ => 1
  | _ => 0

private theorem negationSize_cons (gate : Gate n) (rest : Network (n + 1) m) :
    (Network.cons gate rest).negationSize = gateNegationCount gate + rest.negationSize := by
  cases gate <;> simp [Network.negationSize, gateNegationCount]

private theorem badSteps_extend_card_le (gate : Gate n) (x : Fin (k + 1) → Fin n → Bool) :
    (badSteps (fun i ↦ gate.extend (x i))).card + 1 ≤
      ((badSteps x).card + 1) * 2 ^ gateNegationCount gate := by
  cases gate with
  | const value =>
    have h := badSteps_extend_subset_of_mono (.const value) (fun _ _ _ h ↦ h) x
    simpa only [gateNegationCount, Nat.pow_zero, Nat.mul_one] using
      Nat.add_le_add_right (Finset.card_le_card h) 1
  | binary op left right =>
    have hMono (a b : Fin n → Bool) (h : ∀ i, a i = true → b i = true) :
        (Gate.binary op left right).eval a = true →
          (Gate.binary op left right).eval b = true := by
      cases op with
      | and =>
        simp only [Gate.eval, BinaryOp.eval, Bool.and_eq_true]
        exact fun ha ↦ ⟨h left ha.1, h right ha.2⟩
      | or =>
        simp only [Gate.eval, BinaryOp.eval, Bool.or_eq_true]
        exact Or.imp (h left) (h right)
    have h := badSteps_extend_subset_of_mono (.binary op left right) hMono x
    simpa only [gateNegationCount, Nat.pow_zero, Nat.mul_one] using
      Nat.add_le_add_right (Finset.card_le_card h) 1
  | not src =>
    have hAdded := Finset.card_le_card (badSteps_extend_not_subset x src)
    have hUnion := Finset.card_union_le (badSteps x) (riseSteps (fun i ↦ x i src))
    have hRise := riseSteps_card_le_fallSteps_add_one (fun i ↦ x i src)
    have hFalls := Finset.card_le_card (fallSteps_subset_badSteps x src)
    simp only [gateNegationCount, Nat.pow_one]
    omega

namespace Network

/-- One more than the number of falling steps grows by at most two per NOT gate. -/
theorem badSteps_eval_add_one_le (network : Network n m) (x : Fin (k + 1) → Fin n → Bool) :
    (badSteps (fun i ↦ network.eval (x i))).card + 1 ≤
      ((badSteps x).card + 1) * 2 ^ network.negationSize := by
  induction network with
  | empty => simp only [eval, negationSize, Nat.pow_zero, Nat.mul_one, le_refl]
  | cons gate rest ih =>
    let extended := fun i ↦ gate.extend (x i)
    calc
      _ ≤ ((badSteps extended).card + 1) * 2 ^ rest.negationSize := ih extended
      _ ≤ (((badSteps x).card + 1) * 2 ^ gateNegationCount gate) * 2 ^ rest.negationSize :=
        Nat.mul_le_mul_right _ (badSteps_extend_card_le gate x)
      _ = _ := by rw [negationSize_cons, Nat.pow_add, Nat.mul_assoc]

end Network

namespace BooleanCircuit

/-- Along a nondecreasing input chain, one more than the number of output falls is at most
two to the power of the number of NOT gates. -/
theorem falls_add_one_le_pow_negationSize (c : BooleanCircuit n) (x : Fin (k + 1) → Fin n → Bool)
    (hMono : ∀ (i : Fin k) (j : Fin n), x i.castSucc j = true → x i.succ j = true) :
    (fallSteps (fun i ↦ c.eval (x i))).card + 1 ≤ 2 ^ c.network.negationSize := by
  have hFalls := Finset.card_le_card
    (fallSteps_subset_badSteps (fun i ↦ c.network.eval (x i)) c.output)
  have hTotal := c.network.badSteps_eval_add_one_le x
  rw [badSteps_eq_empty_of_mono x hMono, Finset.card_empty, Nat.zero_add, Nat.one_mul] at hTotal
  exact (Nat.add_le_add_right hFalls 1).trans hTotal

end BooleanCircuit

end PvsNP.Circuits

