module

public import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
public import PvsNP.Complexity.Classes
public import PvsNP.MCSP.ConstantFreeThreshold
public import PvsNP.TuringMachine.OneWayInput

/-! # Exact threshold and one-way time arithmetic for MCSP -/

public section

namespace PvsNP.MCSP

open Circuits

/-- For positive `k`, the largest admissible gate count at threshold `2^(n/k)`. -/
@[expose] def magnificationGateCap (k n : Nat) : Nat :=
  Nat.nthRoot k (2 ^ n)

theorem le_magnificationGateCap_iff {k n gates : Nat} (hk : 0 < k) :
    gates ≤ magnificationGateCap k n ↔ gates ^ k ≤ 2 ^ n :=
  Nat.le_nthRoot_iff (Nat.ne_of_gt hk)

theorem magnificationGateCap_le (k n : Nat) (hk : 0 < k) :
    magnificationGateCap k n ≤ 2 ^ n :=
  (Nat.le_self_pow (Nat.ne_of_gt hk) _).trans
    ((le_magnificationGateCap_iff hk).mp le_rfl)

theorem two_le_magnificationGateCap {k n : Nat} (hk : 0 < k) (hn : k ≤ n) :
    2 ≤ magnificationGateCap k n :=
  (le_magnificationGateCap_iff hk).mpr (Nat.pow_le_pow_right (by decide) hn)

private theorem arity_add_one_le_cap {k n : Nat} (hk : 0 < k) (hn : 4 * k * k ≤ n) :
    n + 1 ≤ magnificationGateCap k n := by
  let quotient := n / k
  let half := quotient / 2
  have hQuotient : 4 * k ≤ quotient := (Nat.le_div_iff_mul_le hk).mpr hn
  have hHalf : 2 * k ≤ half + 1 := by dsimp only [half]; omega
  have hTwice : quotient + 1 ≤ 2 * (half + 1) := by dsimp only [half]; omega
  have hFirst : n + 1 ≤ k * (quotient + 1) := by
    have hMod := Nat.mod_add_div n k
    have hRem := Nat.mod_lt n hk
    change n % k + k * quotient = n at hMod
    rw [Nat.mul_succ]
    omega
  have hExp : half + 1 ≤ 2 ^ half := Nat.lt_two_pow_self
  calc
    n + 1 ≤ k * (quotient + 1) := hFirst
    _ ≤ k * (2 * (half + 1)) := Nat.mul_le_mul_left k hTwice
    _ = (2 * k) * (half + 1) := by ac_rfl
    _ ≤ (half + 1) * (half + 1) := Nat.mul_le_mul_right _ hHalf
    _ ≤ 2 ^ half * 2 ^ half := Nat.mul_le_mul hExp hExp
    _ = 2 ^ (half + half) := (Nat.pow_add ..).symm
    _ ≤ 2 ^ quotient := Nat.pow_le_pow_right (by decide) (by dsimp only [half]; omega)
    _ ≤ magnificationGateCap k n := by
      apply (le_magnificationGateCap_iff hk).mpr
      rw [← Nat.pow_mul]
      exact Nat.pow_le_pow_right (by decide) (Nat.div_mul_le_self n k)

/-- The exact integer time bound with exponent `101/100` in the input length. -/
@[expose] def magnificationTime (length : Nat) : Nat :=
  Nat.nthRoot 100 (length ^ 101)

theorem le_magnificationTime_iff {ticks length : Nat} :
    ticks ≤ magnificationTime length ↔ ticks ^ 100 ≤ length ^ 101 :=
  Nat.le_nthRoot_iff (by decide)

theorem length_le_magnificationTime (length : Nat) : length ≤ magnificationTime length := by
  apply le_magnificationTime_iff.mpr
  cases length with
  | zero => decide
  | succ length => exact Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)

/-- A fixed degree leaves room for its coefficient if the threshold denominator
is at least twice that degree times the time exponent's denominator. -/
theorem magnification_clock_of_polynomial {k n C d : Nat} (hk : 0 < k) (hDegree : 200 * d ≤ k)
    (hArity : 4 * k * k ≤ n) (hCoefficient : 200 * (C + d) ≤ n) :
    2 ^ n * (C * (n + magnificationGateCap k n + 1) ^ d) ≤ magnificationTime (2 ^ n) := by
  let cap := magnificationGateCap k n
  have hArityCap : n + 1 ≤ cap := arity_add_one_le_cap hk hArity
  have hCapPos : 0 < cap := by omega
  have hGatePower : cap ^ (200 * d) ≤ 2 ^ n :=
    (Nat.pow_le_pow_right hCapPos hDegree).trans
      ((le_magnificationGateCap_iff hk).mp le_rfl)
  have hCoeffPower : (C * 2 ^ d) ^ 200 ≤ 2 ^ n := by
    calc
      _ ≤ (2 ^ C * 2 ^ d) ^ 200 :=
        Nat.pow_le_pow_left (Nat.mul_le_mul_right _ (Nat.le_of_lt Nat.lt_two_pow_self)) _
      _ = 2 ^ ((C + d) * 200) := by rw [← Nat.pow_add, ← Nat.pow_mul]
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
  have hSquare : (C * (n + cap + 1) ^ d) ^ 200 ≤ (2 ^ n) ^ 2 := by
    calc
      _ ≤ (C * (2 * cap) ^ d) ^ 200 :=
        Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)) _
      _ = (C * 2 ^ d) ^ 200 * cap ^ (200 * d) := by
        rw [Nat.mul_pow 2, ← Nat.mul_assoc, Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm d 200]
      _ ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul hCoeffPower hGatePower
      _ = _ := (Nat.pow_two _).symm
  have hRow : (C * (n + cap + 1) ^ d) ^ 100 ≤ 2 ^ n := by
    apply (Nat.pow_le_pow_iff_left (n := 2) (by decide)).mp
    rw [← Nat.pow_mul]
    exact hSquare
  apply le_magnificationTime_iff.mpr
  rw [Nat.mul_pow, Nat.pow_succ (2 ^ n) 100]
  exact Nat.mul_le_mul_left _ hRow

/-- Any fixed polynomial charge per row yields the magnification clock for all
sufficiently large arities at every sufficiently large fixed denominator. -/
theorem eventually_magnification_clock {rowCost : Nat → Nat}
    (hCost : PolynomiallyBounded rowCost) :
    ∃ k₀ > 0, ∀ k ≥ k₀, ∃ n₀, ∀ n ≥ n₀,
      2 ^ n * rowCost (n + magnificationGateCap k n) ≤ magnificationTime (2 ^ n) := by
  obtain ⟨C, d, hPoly⟩ := hCost
  refine ⟨max 1 (200 * d), by omega, fun k hk ↦
    ⟨max (4 * k * k) (200 * (C + d)), fun n hn ↦ ?_⟩⟩
  have hPos : 0 < k := (Nat.le_max_left 1 _).trans hk
  exact (Nat.mul_le_mul_left _ (hPoly _)).trans
    (magnification_clock_of_polynomial hPos ((Nat.le_max_right _ _).trans hk)
      ((Nat.le_max_left _ _).trans hn) ((Nat.le_max_right _ _).trans hn))

/-- Truth tables realizable at the exact threshold over binary AND, OR and NOT. -/
@[expose] def magnificationThresholdLanguage (k : Nat) : BinaryLanguage :=
  {bits | ∃ (n : Nat) (c : BooleanCircuit n),
    c.ConstantFree ∧ c.size ≤ magnificationGateCap k n ∧ truthTable n c.eval = bits}

theorem not_mem_magnificationThresholdLanguage_of_length {k : Nat} {bits : BinaryWord}
    (hLength : ¬ ∃ n : Nat, bits.length = 2 ^ n) :
    bits ∉ magnificationThresholdLanguage k := by
  rintro ⟨n, c, _, _, hTable⟩
  exact hLength ⟨n, hTable ▸ length_truthTable n c.eval⟩

theorem mem_magnificationThresholdLanguage_iff {k n : Nat} {bits : BinaryWord}
    (hLength : bits.length = 2 ^ n) :
    bits ∈ magnificationThresholdLanguage k ↔
      ∃ c : BooleanCircuit n, c.ConstantFree ∧ c.size ≤ magnificationGateCap k n ∧
        truthTable n c.eval = bits := by
  constructor
  · rintro ⟨arity, c, hFree, hCap, hTable⟩
    have hPow : 2 ^ arity = 2 ^ n := by
      rw [← length_truthTable arity c.eval, hTable, hLength]
    have hArity : arity = n :=
      Nat.le_antisymm ((Nat.pow_le_pow_iff_right (by decide)).mp hPow.le)
        ((Nat.pow_le_pow_iff_right (by decide)).mp hPow.ge)
    subst arity
    exact ⟨c, hFree, hCap, hTable⟩
  · rintro ⟨c, hFree, hCap, hTable⟩
    exact ⟨n, c, hFree, hCap, hTable⟩

theorem searchStream_isSome_iff_magnificationThreshold {k n : Nat} (hk : 0 < k) (hn : k ≤ n)
    {merge : MergeOracle n} (hCorrect : CorrectMerge merge (magnificationGateCap k n))
    {bits : BinaryWord} (hLength : bits.length = 2 ^ n) :
    (searchStream n merge bits).isSome = true ↔ bits ∈ magnificationThresholdLanguage k :=
  (searchStream_isSome_iff_constantFree hCorrect (Nat.lt_of_lt_of_le hk hn)
    (two_le_magnificationGateCap hk hn) bits).trans
      (mem_magnificationThresholdLanguage_iff hLength).symm

/-- A machine has a common per-row bound on truth-table lengths and the
magnification clock up to a fixed factor on the remaining lengths. -/
@[expose] def MagnificationRowsBounded (M : OneWayMachine) (k : Nat) (rowCost : Nat → Nat) : Prop :=
  (∀ (n : Nat) (word : BinaryWord), word.length = 2 ^ n →
    M.HaltsWithin word (2 ^ n * rowCost (n + magnificationGateCap k n))) ∧
  ∃ scale : Nat, ∀ word : BinaryWord, (¬ ∃ n : Nat, word.length = 2 ^ n) →
    M.HaltsWithin word (scale * (magnificationTime word.length + 1))

/-- A per-row transition bound and an eventual exact arithmetic bound yield a
global one-way time bound, including small and malformed lengths. -/
theorem mem_oneWayDTIME_magnification_of_rows {M : OneWayMachine} {L : BinaryLanguage}
    {k cutoff : Nat} {rowCost : Nat → Nat} (hk : 0 < k) (hDecides : M.Decides L)
    (hCost : PolynomiallyBounded rowCost) (hRows : MagnificationRowsBounded M k rowCost)
    (hEventually : ∀ n ≥ cutoff,
      2 ^ n * rowCost (n + magnificationGateCap k n) ≤ magnificationTime (2 ^ n)) :
    L ∈ OneWayMachine.DTIME magnificationTime := by
  obtain ⟨C, degree, hPoly⟩ := hCost
  obtain ⟨hFull, otherScale, hOther⟩ := hRows
  let small := 2 ^ cutoff * (C * (cutoff + 2 ^ cutoff + 1) ^ degree)
  let scale := max 1 (max small otherScale)
  refine ⟨M, hDecides, scale, fun word ↦ ?_⟩
  let budget := scale * (magnificationTime word.length + 1)
  have hScale : 1 ≤ scale := Nat.le_max_left _ _
  have hWeaken {ticks : Nat} (hRun : M.HaltsWithin word ticks) (hTicks : ticks ≤ budget) :
      M.HaltsWithin word budget := by
    obtain ⟨steps, hSteps, answer, hAnswer⟩ := hRun
    exact ⟨steps, hSteps.trans hTicks, answer, hAnswer⟩
  by_cases hLength : ∃ n : Nat, word.length = 2 ^ n
  · obtain ⟨n, hLength⟩ := hLength
    apply hWeaken (hFull n word hLength)
    by_cases hLarge : cutoff ≤ n
    · calc
        _ ≤ magnificationTime (2 ^ n) := hEventually n hLarge
        _ ≤ magnificationTime word.length + 1 := by rw [hLength]; exact Nat.le_succ _
        _ ≤ budget := Nat.le_mul_of_pos_left _ hScale
    · have hBelow : n ≤ cutoff := by omega
      have hPow : 2 ^ n ≤ 2 ^ cutoff := Nat.pow_le_pow_right (by decide) hBelow
      have hInput : n + magnificationGateCap k n + 1 ≤ cutoff + 2 ^ cutoff + 1 :=
        Nat.add_le_add_right (Nat.add_le_add hBelow ((magnificationGateCap_le k n hk).trans hPow)) 1
      calc
        _ ≤ small := Nat.mul_le_mul hPow ((hPoly _).trans
          (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hInput degree)))
        _ ≤ scale := (Nat.le_max_left small otherScale).trans (Nat.le_max_right _ _)
        _ ≤ budget := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  · exact hWeaken (hOther word hLength) (Nat.mul_le_mul
      ((Nat.le_max_right small otherScale).trans (Nat.le_max_right _ _))
      (Nat.le_refl _))

/-- With a uniform polynomial per-row bound under `P = NP`, a lower bound at
every positive reciprocal-integer threshold suffices for separation. -/
theorem p_ne_np_of_magnification_rows_and_lower
    (hUpper : P = NP → ∃ rowCost : Nat → Nat, PolynomiallyBounded rowCost ∧
      ∀ k > 0, ∃ M : OneWayMachine, M.Decides (magnificationThresholdLanguage k) ∧
        MagnificationRowsBounded M k rowCost)
    (hLower : ∀ k > 0, magnificationThresholdLanguage k ∉ OneWayMachine.DTIME magnificationTime) :
    P ≠ NP := by
  intro hEqual
  obtain ⟨rowCost, hCost, hMachines⟩ := hUpper hEqual
  obtain ⟨k, hk, hClock⟩ := eventually_magnification_clock hCost
  obtain ⟨cutoff, hEventually⟩ := hClock k le_rfl
  obtain ⟨M, hDecides, hRows⟩ := hMachines k hk
  exact hLower k hk
    (mem_oneWayDTIME_magnification_of_rows hk hDecides hCost hRows hEventually)

end PvsNP.MCSP
