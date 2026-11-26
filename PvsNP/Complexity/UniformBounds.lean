module

public import PvsNP.Complexity.TimeBounds
public import Mathlib.Basic.Finite.Defs

import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Pi

/-! # Uniform polynomial bounds for measured register values -/

namespace PvsNP.PolynomiallyBounded

/-- A cost that is polynomial for every polynomially bounded parameter profile
has one polynomial clock uniform over finitely many parameters that fit a
common per-length bound. The chosen clock is used only in the run proof. -/
public theorem exists_uniform {K : Type} [Finite K] (cost : Nat → (K → Nat) → Nat)
    (limit : Nat → Nat) (hLimit : PolynomiallyBounded limit)
    (hCost : ∀ profile : Nat → K → Nat,
      (∀ k, PolynomiallyBounded (fun n ↦ profile n k)) →
      PolynomiallyBounded (fun n ↦ cost n (profile n))) :
    ∃ clock : Nat → Nat, PolynomiallyBounded clock ∧
      ∀ n values, (∀ k, values k ≤ limit n) → cost n values ≤ clock n := by
  classical
  let : Fintype K := Fintype.ofFinite K
  have hMaximum (n : Nat) : ∃ best : K → Fin (limit n + 1),
      ∀ choices : K → Fin (limit n + 1),
        cost n (fun k ↦ (choices k).val) ≤ cost n (fun k ↦ (best k).val) := by
    have hNonempty : (Finset.univ : Finset (K → Fin (limit n + 1))).Nonempty :=
      ⟨fun _ ↦ ⟨0, Nat.succ_pos _⟩, Finset.mem_univ _⟩
    obtain ⟨best, _, hBest⟩ := Finset.exists_max_image Finset.univ
      (fun choices : K → Fin (limit n + 1) ↦ cost n (fun k ↦ (choices k).val)) hNonempty
    exact ⟨best, fun choices ↦ hBest choices (Finset.mem_univ choices)⟩
  let best (n : Nat) := Classical.choose (hMaximum n)
  have hBest (n : Nat) := Classical.choose_spec (hMaximum n)
  let profile := fun n k ↦ (best n k).val
  refine ⟨fun n ↦ cost n (profile n), hCost profile (fun k ↦ ?_), ?_⟩
  · exact hLimit.mono (fun n ↦ Nat.le_of_lt_succ (best n k).isLt)
  · intro n values hValues
    exact hBest n (fun k ↦ ⟨values k, Nat.lt_succ_of_le (hValues k)⟩)

end PvsNP.PolynomiallyBounded
