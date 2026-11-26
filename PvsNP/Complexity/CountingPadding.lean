module

public import PvsNP.Complexity.CountingLowerBound
public import PvsNP.Complexity.Padding

/-! # Exactly when padding erases the counting circuit lower bound -/

public section

namespace PvsNP.Circuits

/-- Two constant choices at each gate give an exponential lower bound on the list length. -/
theorem pow_two_le_length_enumerateNetworks (n s : Nat) :
    2 ^ s ≤ (enumerateNetworks n s).length := by
  induction s generalizing n with
  | zero => simp [length_enumerateNetworks_zero]
  | succ s ih =>
    have hGates : 2 ≤ (allGates n).length := by
      rw [length_allGates]
      omega
    rw [Nat.pow_succ, length_enumerateNetworks_succ, Nat.mul_comm (allGates n).length]
    exact Nat.mul_le_mul (ih (n + 1)) hGates

/-- With an available output wire, every listed network contributes a circuit. -/
theorem pow_two_le_length_enumerateCircuits (n s : Nat) (hWires : 0 < n + s) :
    2 ^ s ≤ (enumerateCircuits n s).length := by
  rw [length_enumerateCircuits_eq]
  calc
    _ ≤ (enumerateNetworks n s).length := pow_two_le_length_enumerateNetworks n s
    _ = (enumerateNetworks n s).length * 1 := (Nat.mul_one _).symm
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hWires)

private theorem eight_mul_square_le_two_pow (n : Nat) (hn : 10 ≤ n) : 8 * n * n ≤ 2 ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hPrev : 10 ≤ n
    · have hOld := ih hPrev
      have hProduct := Nat.mul_le_mul_right n (show 3 ≤ n by omega)
      have hSquare : (n + 1) * (n + 1) ≤ 2 * (n * n) := by
        rw [Nat.add_mul n 1 (n + 1), Nat.mul_add n n 1, Nat.mul_one, Nat.one_mul]
        omega
      rw [Nat.pow_succ]
      calc
        _ = 8 * ((n + 1) * (n + 1)) := Nat.mul_assoc ..
        _ ≤ 8 * (2 * (n * n)) := Nat.mul_le_mul_left 8 hSquare
        _ = (8 * n * n) * 2 := by ac_rfl
        _ ≤ _ := Nat.mul_le_mul_right 2 hOld
    · have hNine : n = 9 := by omega
      subst n
      decide

theorem le_countingBudget (n : Nat) (hn : 10 ≤ n) : n ≤ countingBudget n := by
  rw [countingBudget, Nat.le_div_iff_mul_le (by omega)]
  calc
    _ = 8 * n * n := by ac_rfl
    _ ≤ _ := eight_mul_square_le_two_pow n hn

/-- At the counting budget, the circuit list already has at least `2^n` entries. -/
theorem pow_two_le_length_countingCircuits (n : Nat) (hn : 10 ≤ n) :
    2 ^ n ≤ (enumerateCircuits n (countingBudget n)).length := by
  calc
    _ ≤ 2 ^ countingBudget n := Nat.pow_le_pow_right (by decide) (le_countingBudget n hn)
    _ ≤ _ := pow_two_le_length_enumerateCircuits _ _ (by omega)

end PvsNP.Circuits

namespace PvsNP

open Circuits

/-- A polynomial bound on the number of enumerated tables in the padded length
also polynomially bounds `2^n` in that length. -/
theorem padded_pow_two_bound_of_truth_table_count (N : Nat → Nat)
    (h : ∃ f, PolynomiallyBounded f ∧ ∀ n, (allTruthTables n).length ≤ f (N n)) :
    ∃ g, PolynomiallyBounded g ∧ ∀ n, 2 ^ n ≤ g (N n) := by
  obtain ⟨f, hPoly, hCount⟩ := h
  refine ⟨f, hPoly, fun n ↦ ?_⟩
  have hBound := hCount n
  rw [allTruthTables_length] at hBound
  apply Nat.le_trans ?_ hBound
  exact Nat.le_of_lt (Nat.lt_pow_self (by decide))

/-- An eventual polynomial bound on the full circuit list in the padded length
gives a uniform polynomial bound on `2^n` in that length. -/
theorem padded_pow_two_bound_of_circuit_count (N : Nat → Nat) (cutoff : Nat)
    (h : ∃ f, PolynomiallyBounded f ∧ ∀ n ≥ cutoff,
      (enumerateCircuits n (countingBudget n)).length ≤ f (N n)) :
    ∃ g, PolynomiallyBounded g ∧ ∀ n, 2 ^ n ≤ g (N n) := by
  obtain ⟨f, hPoly, hCount⟩ := h
  let start := max cutoff 10
  refine ⟨fun t ↦ f t + 2 ^ start, hPoly.add (PolynomiallyBounded.const _), fun n ↦ ?_⟩
  by_cases hn : start ≤ n
  · have hCut := Nat.le_trans (Nat.le_max_left cutoff 10) hn
    have hStart := Nat.le_trans (Nat.le_max_right cutoff 10) hn
    exact Nat.le_trans (pow_two_le_length_countingCircuits n hStart)
      (Nat.le_trans (hCount n hCut) (Nat.le_add_right ..))
  · have hPow : 2 ^ n ≤ 2 ^ start := Nat.pow_le_pow_right (by decide) (by omega)
    exact Nat.le_trans hPow (Nat.le_add_left ..)

/-- The counting language padded to length `N n` has polynomial-size circuits
exactly when the number of possible length-`n` inputs is polynomially bounded
at the padded length. -/
theorem zeroPaddedCountingHard_mem_PPoly_iff {N : Nat → Nat} (hLength : ∀ n, n ≤ N n)
    (hInjective : Function.Injective N) :
    zeroPaddedLanguage N countingHardLanguage ∈ PPoly ↔
      ∃ g, PolynomiallyBounded g ∧ ∀ n, 2 ^ n ≤ g (N n) := by
  refine ⟨fun h ↦ ?_,
    zeroPaddedLanguage_mem_PPoly_of_pow_two_bound countingHardLanguage hLength hInjective⟩
  obtain ⟨family, g, hg, hSize, hCorrect⟩ :=
    exists_circuits_of_zeroPaddedLanguage_mem_PPoly hLength hInjective h
  have hLinear : PolynomiallyBounded (fun m ↦ 8 * m) :=
    (PolynomiallyBounded.const 8).mul PolynomiallyBounded.id
  refine ⟨fun m ↦ g m * (8 * m) + 2 ^ 5,
    (hg.mul hLinear).add (PolynomiallyBounded.const _), fun n ↦ ?_⟩
  by_cases hn : 5 ≤ n
  · have hLower := countingHardLanguage_size_gt n hn (family n) (hCorrect n)
    unfold countingBudget at hLower
    have hPow := (Nat.div_lt_iff_lt_mul (by omega : 0 < 8 * n)).mp hLower
    calc
      2 ^ n ≤ (family n).size * (8 * n) := hPow.le
      _ ≤ g (N n) * (8 * N n) :=
        Nat.mul_le_mul (hSize n) (Nat.mul_le_mul_left 8 (hLength n))
      _ ≤ _ := Nat.le_add_right ..
  · exact (Nat.pow_le_pow_right (by decide) (by omega : n ≤ 5)).trans (Nat.le_add_left ..)

theorem zeroPaddedCountingHard_mem_PPoly_of_truth_table_count {N : Nat → Nat}
    (hLength : ∀ n, n ≤ N n) (hInjective : Function.Injective N)
    (h : ∃ f, PolynomiallyBounded f ∧ ∀ n, (allTruthTables n).length ≤ f (N n)) :
    zeroPaddedLanguage N countingHardLanguage ∈ PPoly :=
  (zeroPaddedCountingHard_mem_PPoly_iff hLength hInjective).mpr
    (padded_pow_two_bound_of_truth_table_count N h)

theorem zeroPaddedCountingHard_mem_PPoly_of_circuit_count {N : Nat → Nat}
    (hLength : ∀ n, n ≤ N n) (hInjective : Function.Injective N) (cutoff : Nat)
    (h : ∃ f, PolynomiallyBounded f ∧ ∀ n ≥ cutoff,
      (enumerateCircuits n (countingBudget n)).length ≤ f (N n)) :
    zeroPaddedLanguage N countingHardLanguage ∈ PPoly :=
  (zeroPaddedCountingHard_mem_PPoly_iff hLength hInjective).mpr
    (padded_pow_two_bound_of_circuit_count N cutoff h)

/-- Padding enough to bound the full-table certificates on the accepted
padded words also gives polynomial-size circuits for the padded language. -/
theorem zeroPaddedCountingHard_mem_PPoly_of_full_table_certificates {N : Nat → Nat}
    (hLength : ∀ n, n ≤ N n) (hInjective : Function.Injective N)
    (h : ∃ k : Nat, ∀ w ∈ countingHardLanguage,
      (hardTruthTable w.length (countingBudget w.length)).length ≤ (zeroPad N w).length ^ k) :
    zeroPaddedLanguage N countingHardLanguage ∈ PPoly := by
  obtain ⟨k, hCert⟩ := h
  apply (zeroPaddedCountingHard_mem_PPoly_iff hLength hInjective).mpr
  refine ⟨fun m ↦ m ^ k + 2 ^ 10,
    (PolynomiallyBounded.id.pow k).add (PolynomiallyBounded.const _), fun n ↦ ?_⟩
  by_cases hn : 10 ≤ n
  · obtain ⟨w, hw, hMem⟩ := exists_countingHardLanguage_of_one_le_budget n (by omega)
      ((show 1 ≤ n by omega).trans (le_countingBudget n hn))
    have hBound := hCert w hMem
    rw [length_hardTruthTable, length_zeroPad hLength, hw] at hBound
    exact hBound.trans (Nat.le_add_right ..)
  · exact (Nat.pow_le_pow_right (by decide) (by omega : n ≤ 10)).trans (Nat.le_add_left ..)

theorem zeroPaddedCountingHard_not_mem_PPoly_of_polynomial {N : Nat → Nat}
    (hLength : ∀ n, n ≤ N n) (hInjective : Function.Injective N)
    (hPoly : PolynomiallyBounded N) : zeroPaddedLanguage N countingHardLanguage ∉ PPoly :=
  fun h ↦ countingHardLanguage_not_mem_PPoly
    ((zeroPaddedLanguage_mem_PPoly_iff hLength hInjective hPoly).mp h)

/-- A Cook NP verifier for polynomially padded counting words would
separate Cook's classes. -/
theorem p_ne_np_of_zeroPaddedCountingHard_mem_NP {N : Nat → Nat}
    (hLength : ∀ n, n ≤ N n) (hInjective : Function.Injective N) (hPoly : PolynomiallyBounded N)
    (hNP : zeroPaddedLanguage N countingHardLanguage ∈ NP) : P ≠ NP :=
  p_ne_np_of_CNFSAT_not_mem_PPoly (CNFSAT_not_mem_PPoly_of_mem_NP hNP
    (zeroPaddedCountingHard_not_mem_PPoly_of_polynomial hLength hInjective hPoly))

end PvsNP
