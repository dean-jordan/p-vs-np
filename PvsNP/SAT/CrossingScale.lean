module

import Init.Data.Nat.Lemmas

/-! # Numerical bounds for the SAT crossing family -/

namespace PvsNP.SATCrossing

/-- The transcript threshold fits among the `2^m` rows. -/
public theorem twice_pow_div_le_pow_two (m q : Nat) (hm : 0 < m) :
    2 * q ^ ((m - 1) / q) ≤ 2 ^ m := by
  let d := (m - 1) / q
  have hQuotient : q * d ≤ m - 1 := by
    rw [Nat.mul_comm q d]
    exact Nat.div_mul_le_self _ _
  calc
    2 * q ^ d ≤ 2 * (2 ^ q) ^ d :=
      Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (Nat.le_of_lt Nat.lt_two_pow_self) d)
    _ = 2 ^ (1 + q * d) := by rw [Nat.pow_add 2 1, Nat.pow_one, Nat.pow_mul]
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) (by omega)

/-- Convert the crossing count to an explicit bound in the encoded length. -/
public theorem square_length_le_crossing_time (r B q T : Nat)
    (hLower : 2 ^ r ≤ B) (hUpper : B ≤ 2 ^ r * (2 + (r + 1) * (r + 3)))
    (hq : 0 < q) (hCross : 8 * B * ((2 ^ r - 1) / q) ≤ 2 * T) :
    let N := 10 * B + 1
    N ^ 2 ≤ 121 * (2 + (Nat.log2 N + 1) * (Nat.log2 N + 3)) * q * (T + N) := by
  let N := 10 * B + 1
  let m := 2 ^ r
  let d := (m - 1) / q
  let factor := 2 + (N.log2 + 1) * (N.log2 + 3)
  change N ^ 2 ≤ 121 * factor * q * (T + N)
  have hm : 0 < m := Nat.two_pow_pos r
  have hRemainder := Nat.mod_lt (m - 1) hq
  have hDivision : (m - 1) % q + q * d = m - 1 := Nat.mod_add_div _ _
  have hRows : m ≤ q * d + q := by omega
  change 8 * B * d ≤ 2 * T at hCross
  rw [Nat.mul_assoc] at hCross
  have hTime : B * d ≤ T := by omega
  have hBN : B ≤ N := by omega
  have hBT : B * m ≤ q * (T + N) := calc
    B * m ≤ B * (q * d + q) := Nat.mul_le_mul_left B hRows
    _ = q * (B * d + B) := by
      simp only [Nat.mul_add]
      ac_rfl
    _ ≤ q * (T + N) := Nat.mul_le_mul_left q (Nat.add_le_add hTime hBN)
  have hLog : r ≤ N.log2 :=
    (Nat.le_log2 (by omega : N ≠ 0)).mpr (Nat.le_trans hLower hBN)
  have hFactors : (r + 1) * (r + 3) ≤ (N.log2 + 1) * (N.log2 + 3) :=
    Nat.mul_le_mul (Nat.add_le_add_right hLog 1) (Nat.add_le_add_right hLog 3)
  have hScale : B ≤ m * factor :=
    Nat.le_trans hUpper (Nat.mul_le_mul_left _ (Nat.add_le_add_left hFactors 2))
  have hN : N ≤ 11 * B := by omega
  calc
    N ^ 2 ≤ (11 * B) ^ 2 := Nat.pow_le_pow_left hN 2
    _ = 121 * (B * B) := by rw [Nat.mul_pow, Nat.pow_two B]
    _ ≤ 121 * (B * (m * factor)) := Nat.mul_le_mul_left 121 (Nat.mul_le_mul_left B hScale)
    _ = 121 * factor * (B * m) := by ac_rfl
    _ ≤ 121 * factor * (q * (T + N)) := Nat.mul_le_mul_left _ hBT
    _ = 121 * factor * q * (T + N) := (Nat.mul_assoc ..).symm

end PvsNP.SATCrossing
