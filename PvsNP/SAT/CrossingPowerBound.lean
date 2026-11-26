module

public import PvsNP.SAT.CrossingTimeLowerBound

import Mathlib.Data.Finset.Max
import PvsNP.Complexity.TimeBounds

/-! # Exact power-clock consequences of the SAT crossing bound -/

namespace PvsNP.SATCrossing

private theorem width_mul_rows_le_time {B m q T : Nat} (hq : 0 < q)
    (hLarge : 2 * q ≤ m) (hCross : 8 * B * ((m - 1) / q) ≤ 2 * T) :
    B * m ≤ (2 * q) * T := by
  let ℓ := (m - 1) / q
  have hRest := Nat.mod_lt (m - 1) hq
  have hDivision : (m - 1) % q + q * ℓ = m - 1 := Nat.mod_add_div _ _
  have hOne : 1 ≤ ℓ := by
    apply (Nat.le_div_iff_mul_le hq).mpr
    rw [Nat.one_mul]
    omega
  have hqLe : q ≤ q * ℓ := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left q hOne
  have hRows : m ≤ (2 * q) * ℓ := by
    rw [Nat.mul_assoc, Nat.two_mul]
    omega
  change 8 * B * ℓ ≤ 2 * T at hCross
  rw [Nat.mul_assoc] at hCross
  have hTime : B * ℓ ≤ T := by omega
  calc
    B * m ≤ B * ((2 * q) * ℓ) := Nat.mul_le_mul_left B hRows
    _ = (2 * q) * (B * ℓ) := by ac_rfl
    _ ≤ (2 * q) * T := Nat.mul_le_mul_left _ hTime

private theorem row_bound_of_power_clock {B m q T K C e : Nat}
    (hB : 0 < B) (hm : 0 < m) (hWidth : B ≤ m * K)
    (hRows : B * m ≤ (2 * q) * T)
    (hPower : T ^ (e + 1) ≤ C * (10 * B + 2) ^ (2 * e + 1)) :
    m ≤ C * (2 * q) ^ (e + 1) * 12 ^ (2 * e + 1) * K ^ e := by
  let coeff := C * (2 * q) ^ (e + 1) * 12 ^ (2 * e + 1)
  have hN : 10 * B + 2 ≤ 12 * B := by omega
  have hSplit : B ^ (2 * e + 1) = B ^ (e + 1) * B ^ e := by
    rw [show 2 * e + 1 = (e + 1) + e by omega, Nat.pow_add]
  have hProduct : B ^ (e + 1) * m ^ (e + 1) ≤ B ^ (e + 1) * (coeff * B ^ e) := calc
    _ = (B * m) ^ (e + 1) := (Nat.mul_pow ..).symm
    _ ≤ ((2 * q) * T) ^ (e + 1) := Nat.pow_le_pow_left hRows _
    _ = (2 * q) ^ (e + 1) * T ^ (e + 1) := Nat.mul_pow ..
    _ ≤ (2 * q) ^ (e + 1) * (C * (10 * B + 2) ^ (2 * e + 1)) :=
      Nat.mul_le_mul_left _ hPower
    _ ≤ (2 * q) ^ (e + 1) * (C * (12 * B) ^ (2 * e + 1)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hN _))
    _ = _ := by
      rw [Nat.mul_pow 12 B, hSplit]
      let Q := (2 * q) ^ (e + 1)
      let P := 12 ^ (2 * e + 1)
      calc
        _ = (Q * C) * (P * (B ^ (e + 1) * B ^ e)) := (Nat.mul_assoc ..).symm
        _ = (C * Q * P) * (B ^ (e + 1) * B ^ e) := by
          rw [Nat.mul_comm Q C, Nat.mul_assoc (C * Q)]
        _ = _ := Nat.mul_left_comm ..
  have hCancelB := Nat.le_of_mul_le_mul_left hProduct (Nat.pow_pos hB)
  have hPowerM : m ^ e * m ≤ m ^ e * (coeff * K ^ e) := calc
    _ = m ^ (e + 1) := (Nat.pow_succ ..).symm
    _ ≤ coeff * B ^ e := hCancelB
    _ ≤ coeff * (m * K) ^ e := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hWidth _)
    _ = _ := by rw [Nat.mul_pow m K]; ac_rfl
  exact Nat.le_of_mul_le_mul_left hPowerM (Nat.pow_pos hm)

/-- Every fixed power exponent below two fails on a rejecting binary CNF word.
The clock comparison uses natural powers, with exponent `(2 * d - 1) / d`. -/
public theorem cnfsat_no_subquadratic_power_clock (M : Machine Bool) (hDecides : M.Decides CNFSAT)
    (C d : Nat) (hd : 1 ≤ d) :
    ∃ word : BinaryWord, word ∉ CNFSAT ∧
      ∀ t, M.HaltsWithin word t → C * (word.length + 1) ^ (2 * d - 1) < t ^ d := by
  classical
  cases d with
  | zero => omega
  | succ e =>
    by_contra hFailure
    have hFast (word : BinaryWord) (hReject : word ∉ CNFSAT) :
        ∃ t, M.HaltsWithin word t ∧ t ^ (e + 1) ≤ C * (word.length + 1) ^ (2 * e + 1) := by
      by_contra hNoClock
      apply hFailure
      refine ⟨word, hReject, fun t hStop ↦ ?_⟩
      rw [show 2 * (e + 1) - 1 = 2 * e + 1 by omega]
      exact Nat.lt_of_not_ge (fun hLe ↦ hNoClock ⟨t, hStop, hLe⟩)
    let q := Nat.card M.State + 3
    let coeff := C * (2 * q) ^ (e + 1) * 12 ^ (2 * e + 1)
    let K (r : Nat) := 2 + (r + 1) * (r + 3)
    have hq : 0 < q := by dsimp only [q]; omega
    have hPolyK : PolynomiallyBounded K :=
      (PolynomiallyBounded.const 2).add
        ((PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)).mul
          (PolynomiallyBounded.id.add (PolynomiallyBounded.const 3)))
    have hPoly : PolynomiallyBounded (fun r ↦ coeff * K r ^ e + 2 * q) :=
      ((PolynomiallyBounded.const coeff).mul (hPolyK.pow e)).add
        (PolynomiallyBounded.const (2 * q))
    apply pow_two_not_polynomiallyBounded
    apply hPoly.mono
    intro r
    let m := 2 ^ r
    let B := blockWidth r
    by_cases hLarge : 2 * q ≤ m
    · have hFamily (a : Table r) :
          ∃ t, M.HaltsWithin (crossingWord r B a a) t ∧
            t ^ (e + 1) ≤ C * (10 * B + 2) ^ (2 * e + 1) := by
        have hLength : (crossingWord r B a a).length + 1 = 10 * B + 2 := by
          rw [length_crossingWord]
          change 2 * B + 8 * B + 1 + 1 = 10 * B + 2
          omega
        simpa only [hLength] using
          hFast (crossingWord r B a a) (crossingWord_diagonal_not_mem_CNFSAT r B a)
      choose clock hStop hPower using hFamily
      obtain ⟨aMax, _, hMax⟩ := Finset.exists_max_image
        (Finset.univ : Finset (Table r)) clock Finset.univ_nonempty
      let T := clock aMax
      have hCommon (a : Table r) : M.HaltsWithin (crossingWord r B a a) T := by
        obtain ⟨t, ht, answer, hHalt⟩ := hStop a
        exact ⟨t, ht.trans (hMax a (Finset.mem_univ a)), answer, hHalt⟩
      have hm : 0 < m := Nat.two_pow_pos r
      have hCross := crossing_clock_lower_bound M hDecides r B T ((m - 1) / q)
        (twice_pow_div_le_pow_two m q hm) hCommon
      have hBound : m ≤ coeff * K r ^ e :=
        row_bound_of_power_clock (blockWidth_pos r) hm (blockWidth_le r)
          (width_mul_rows_le_time hq hLarge hCross) (hPower aMax)
      exact hBound.trans (Nat.le_add_right ..)
    · exact (Nat.le_of_lt (Nat.lt_of_not_ge hLarge)).trans (Nat.le_add_left ..)

/-- Each rational exponent `e / d` below two fails on a rejecting word. -/
public theorem cnfsat_no_subquadratic_rational_clock (M : Machine Bool)
    (hDecides : M.Decides CNFSAT) (C e d : Nat) (hd : 1 ≤ d) (hExp : e < 2 * d) :
    ∃ word : BinaryWord, word ∉ CNFSAT ∧
      ∀ t, M.HaltsWithin word t → C * (word.length + 1) ^ e < t ^ d := by
  obtain ⟨word, hReject, hClock⟩ := cnfsat_no_subquadratic_power_clock M hDecides C d hd
  refine ⟨word, hReject, fun t ht ↦ ?_⟩
  have hExponent : e ≤ 2 * d - 1 := by omega
  have hPower := Nat.pow_le_pow_right (Nat.succ_pos word.length) hExponent
  exact (Nat.mul_le_mul_left C hPower).trans_lt (hClock t ht)

end PvsNP.SATCrossing
