module

public import PvsNP.Complexity.TimeBounds

import Init.Data.Nat.Lemmas

/-! # A logarithmic deficit bound for binary certificate lengths -/

namespace PvsNP

/-- A polynomial factor in a binary certificate count can cover only a logarithmic
deficit between the length cap and the input length. -/
public theorem binaryCertificateLength_lower_of_pow_bound {cap g : Nat → Nat}
    (hg : PolynomiallyBounded g) (cutoff : Nat) (h : ∀ n ≥ cutoff, 2 ^ n ≤ 2 ^ cap n * g n) :
    ∃ C d : Nat, ∀ n ≥ cutoff, n ≤ cap n + C + d * (Nat.log2 (n + 1) + 1) := by
  obtain ⟨C, d, hBound⟩ := hg
  refine ⟨C, d, fun n hn ↦ ?_⟩
  have hCoefficient : C ≤ 2 ^ C := Nat.le_of_lt Nat.lt_two_pow_self
  have hBase : n + 1 ≤ 2 ^ (Nat.log2 (n + 1) + 1) := Nat.le_of_lt Nat.lt_log2_self
  have hPolynomial : g n ≤ 2 ^ (C + d * (Nat.log2 (n + 1) + 1)) := calc
    g n ≤ C * (n + 1) ^ d := hBound n
    _ ≤ 2 ^ C * (2 ^ (Nat.log2 (n + 1) + 1)) ^ d :=
      Nat.mul_le_mul hCoefficient (Nat.pow_le_pow_left hBase d)
    _ = _ := by rw [Nat.pow_add 2 C, Nat.pow_mul']
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  rw [Nat.add_assoc (cap n), Nat.pow_add 2 (cap n)]
  exact Nat.le_trans (h n hn) (Nat.mul_le_mul_left _ hPolynomial)

end PvsNP
