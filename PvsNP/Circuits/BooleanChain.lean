module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic

/-! # Changes along Boolean sequences -/

public section

namespace PvsNP.Circuits

/-- The positions at which a Boolean sequence changes from false to true. -/
def riseSteps {k : Nat} (b : Fin (k + 1) → Bool) : Finset (Fin k) :=
  Finset.univ.filter fun i : Fin k ↦ b i.castSucc = false ∧ b i.succ = true

/-- The positions at which a Boolean sequence changes from true to false. -/
def fallSteps {k : Nat} (b : Fin (k + 1) → Bool) : Finset (Fin k) :=
  Finset.univ.filter fun i : Fin k ↦ b i.castSucc = true ∧ b i.succ = false

@[simp] theorem mem_riseSteps {k : Nat} {b : Fin (k + 1) → Bool} {i : Fin k} :
    i ∈ riseSteps b ↔ b i.castSucc = false ∧ b i.succ = true := by
  simp [riseSteps]

@[simp] theorem mem_fallSteps {k : Nat} {b : Fin (k + 1) → Bool} {i : Fin k} :
    i ∈ fallSteps b ↔ b i.castSucc = true ∧ b i.succ = false := by
  simp [fallSteps]

private theorem card_filter_succ {k : Nat} (p : Fin (k + 1) → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card =
      if p 0 then (Finset.univ.filter fun i : Fin k ↦ p i.succ).card + 1
      else (Finset.univ.filter fun i : Fin k ↦ p i.succ).card := by
  rw [Fin.univ_succ, Finset.filter_cons, apply_ite Finset.card, Finset.card_cons,
    Finset.filter_map, Finset.card_map]
  rfl

/-- The rise and fall counts balance after including the initial and final values. -/
theorem riseSteps_card_balance {k : Nat} (b : Fin (k + 1) → Bool) :
    (riseSteps b).card + (b 0).toNat = (fallSteps b).card + (b (Fin.last k)).toNat := by
  induction k with
  | zero => simp [riseSteps, fallSteps, Fin.eq_zero]
  | succ k ih =>
    let tail (i : Fin (k + 1)) := b i.succ
    have hTail := ih tail
    have hRise : (riseSteps b).card =
        if b 0 = false ∧ b (0 : Fin (k + 1)).succ = true then (riseSteps tail).card + 1
        else (riseSteps tail).card := by
      simp only [riseSteps, card_filter_succ, Fin.castSucc_zero, Fin.castSucc_succ, tail]
    have hFall : (fallSteps b).card =
        if b 0 = true ∧ b (0 : Fin (k + 1)).succ = false then (fallSteps tail).card + 1
        else (fallSteps tail).card := by
      simp only [fallSteps, card_filter_succ, Fin.castSucc_zero, Fin.castSucc_succ, tail]
    have hFirst : tail 0 = b (1 : Fin (k + 2)) := rfl
    have hLast : tail (Fin.last k) = b (Fin.last (k + 1)) := rfl
    rw [hFirst, hLast] at hTail
    rw [hRise, hFall]
    cases b 0 <;> cases h₁ : b (1 : Fin (k + 2)) <;>
      simp [h₁] at hTail ⊢ <;> omega

/-- A Boolean sequence rises at most one more time than it falls. -/
theorem riseSteps_card_le_fallSteps_add_one {k : Nat} (b : Fin (k + 1) → Bool) :
    (riseSteps b).card ≤ (fallSteps b).card + 1 := by
  have hBalance := riseSteps_card_balance b
  have hLast := Bool.toNat_le (b (Fin.last k))
  omega

end PvsNP.Circuits
