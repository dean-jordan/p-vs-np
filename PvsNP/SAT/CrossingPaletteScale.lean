module

import Init.Data.Nat.Lemmas

/-! # Numerical bound for the palette crossing family -/

namespace PvsNP.SATCrossing

/-- A palette of `r` bits per address turns the crossing bound into an
encoded-length bound with one logarithmic factor. -/
public theorem square_length_le_log_crossing_time (r B q T : Nat) (hr : 1 ≤ r)
    (hLower : 2 ^ r ≤ B) (hUpper : B ≤ 48 * (r + 1) ^ 2 * 2 ^ r) (hq : 0 < q)
    (hCross : 8 * B * ((r * 2 ^ r - 1) / q) ≤ 2 * T) :
    let n := 10 * B + 1
    n ^ 2 ≤ 11616 * (n.log2 + 1) * q * (T + n) := by
  let n := 10 * B + 1
  let m := r * 2 ^ r
  let ℓ := (m - 1) / q
  let factor := n.log2 + 1
  change n ^ 2 ≤ 11616 * factor * q * (T + n)
  have hm : 0 < m := Nat.mul_pos hr (Nat.two_pow_pos r)
  have hRest := Nat.mod_lt (m - 1) hq
  have hDivision : (m - 1) % q + q * ℓ = m - 1 := Nat.mod_add_div _ _
  have hRows : m ≤ q * ℓ + q := by omega
  change 8 * B * ℓ ≤ 2 * T at hCross
  rw [Nat.mul_assoc] at hCross
  have hTime : B * ℓ ≤ T := by omega
  have hBN : B ≤ n := by omega
  have hBT : B * m ≤ q * (T + n) := calc
    B * m ≤ B * (q * ℓ + q) := Nat.mul_le_mul_left B hRows
    _ = q * (B * ℓ + B) := by
      simp only [Nat.mul_add]
      ac_rfl
    _ ≤ q * (T + n) := Nat.mul_le_mul_left q (Nat.add_le_add hTime hBN)
  have hLog : r ≤ n.log2 := (Nat.le_log2 (by omega : n ≠ 0)).mpr (Nat.le_trans hLower hBN)
  have hWidth : B ≤ 96 * factor * m := calc
    B ≤ 48 * (r + 1) ^ 2 * 2 ^ r := hUpper
    _ = (48 * (r + 1) * 2 ^ r) * (r + 1) := by rw [Nat.pow_two]; ac_rfl
    _ ≤ (48 * (r + 1) * 2 ^ r) * (2 * r) := Nat.mul_le_mul_left _ (by omega)
    _ = (48 * 2) * (r + 1) * m := by dsimp only [m]; ac_rfl
    _ ≤ 96 * factor * m :=
      Nat.mul_le_mul_right m (Nat.mul_le_mul_left 96 (Nat.add_le_add_right hLog 1))
  have hn : n ≤ 11 * B := by
    have hPositive := Nat.two_pow_pos r
    omega
  calc
    n ^ 2 ≤ (11 * B) ^ 2 := Nat.pow_le_pow_left hn 2
    _ = 121 * (B * B) := by rw [Nat.mul_pow, Nat.pow_two B]
    _ ≤ 121 * (B * (96 * factor * m)) := Nat.mul_le_mul_left 121 (Nat.mul_le_mul_left B hWidth)
    _ = (121 * 96) * factor * (B * m) := by ac_rfl
    _ ≤ 11616 * factor * (q * (T + n)) := Nat.mul_le_mul_left _ hBT
    _ = _ := (Nat.mul_assoc ..).symm

end PvsNP.SATCrossing
