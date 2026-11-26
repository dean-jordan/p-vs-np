module

/-! # The numerical counting bound for Boolean circuits -/

public section

namespace PvsNP.Circuits

private theorem twice_succ_lt_two_pow (m : Nat) (hm : 5 ≤ m) : 2 * (m + 1) < 2 ^ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction k with
  | zero => decide
  | succ k ih =>
    have hOld := ih (by omega)
    change 2 * (((5 + k) + 1) + 1) < 2 ^ ((5 + k) + 1)
    rw [Nat.pow_succ]
    omega

/-- The gate budget used for counting at input length `n`. -/
@[expose] def countingBudget (n : Nat) : Nat := 2 ^ n / (8 * n)

/-- The circuit codes at this gate budget are fewer than the truth tables. -/
theorem countingBudget_circuit_count_lt (n : Nat) (hn : 5 ≤ n) :
    (n + countingBudget n) * (8 * (n + countingBudget n + 1) ^ 2) ^ countingBudget n <
      2 ^ (2 ^ n) := by
  let s := countingBudget n
  change (n + s) * (8 * (n + s + 1) ^ 2) ^ s < 2 ^ (2 ^ n)
  have hGrowth := twice_succ_lt_two_pow n hn
  have hBudgetLe : s ≤ 2 ^ n := Nat.div_le_self _ _
  have hWires : n + s + 1 ≤ 2 ^ (n + 1) := by
    rw [Nat.pow_succ]
    omega
  have hGate : 8 * (n + s + 1) ^ 2 ≤ 2 ^ (4 * n) := by
    calc
      _ ≤ 8 * (2 ^ (n + 1)) ^ 2 := Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left hWires 2)
      _ = 2 ^ (2 * n + 5) := by
        rw [← Nat.pow_mul]
        change 2 ^ 3 * 2 ^ ((n + 1) * 2) = _
        rw [← Nat.pow_add]
        congr 1
        omega
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have hBudget : 8 * n * s ≤ 2 ^ n := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_le_self _ _
  have hHalf : 2 * (4 * n * s) ≤ 2 ^ n := by
    rw [← Nat.mul_assoc 2 (4 * n) s, ← Nat.mul_assoc 2 4 n]
    exact hBudget
  have hExponent : n + 1 + 4 * n * s < 2 ^ n := by omega
  calc
    _ ≤ 2 ^ (n + 1) * (2 ^ (4 * n)) ^ s :=
      Nat.mul_le_mul (Nat.le_trans (Nat.le_succ _) hWires) (Nat.pow_le_pow_left hGate _)
    _ = 2 ^ (n + 1 + 4 * n * s) := by rw [← Nat.pow_mul, ← Nat.pow_add]
    _ < _ := Nat.pow_lt_pow_right (by decide) hExponent

private theorem sixteen_mul_le_two_pow (m : Nat) (hm : 8 ≤ m) : 16 * m ≤ 2 ^ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction k with
  | zero => decide
  | succ k ih =>
    have hOld := ih (by omega)
    change 16 * ((8 + k) + 1) ≤ 2 ^ ((8 + k) + 1)
    rw [Nat.pow_succ]
    omega

/-- The counting budget on `2 * m` input bits dominates `2^m`. -/
theorem pow_two_le_countingBudget_double (m : Nat) (hm : 8 ≤ m) :
    2 ^ m ≤ countingBudget (2 * m) := by
  rw [countingBudget, Nat.le_div_iff_mul_le (by omega)]
  calc
    _ = 2 ^ m * (16 * m) := by congr 1 <;> omega
    _ ≤ 2 ^ m * 2 ^ m := Nat.mul_le_mul_left _ (sixteen_mul_le_two_pow m hm)
    _ = _ := by rw [← Nat.pow_add, Nat.two_mul]

end PvsNP.Circuits
