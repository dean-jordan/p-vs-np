module

/-! # Polynomial bounds on input length -/

namespace PvsNP

/-- A bound by one fixed polynomial at all input lengths, including length zero. -/
@[expose] public def PolynomiallyBounded (f : Nat → Nat) : Prop :=
  ∃ C d : Nat, ∀ n : Nat, f n ≤ C * (n + 1) ^ d

namespace PolynomiallyBounded

/-- A pointwise smaller function inherits the bound. -/
public theorem mono {f g : Nat → Nat} (hg : PolynomiallyBounded g)
    (hfg : ∀ n, f n ≤ g n) : PolynomiallyBounded f := by
  obtain ⟨C, d, h⟩ := hg
  exact ⟨C, d, fun n ↦ Nat.le_trans (hfg n) (h n)⟩

/-- A fixed constant is a degree-zero bound. -/
public theorem const (C : Nat) : PolynomiallyBounded (fun _ ↦ C) := by
  exact ⟨C, 0, fun n ↦ by simp⟩

/-- Input length has a linear bound. -/
public theorem id : PolynomiallyBounded (fun n ↦ n) := by
  exact ⟨1, 1, fun n ↦ by simp⟩

/-- The sum of two polynomially bounded functions is polynomially bounded. -/
public theorem add {f g : Nat → Nat} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n ↦ f n + g n) := by
  obtain ⟨C, d, hC⟩ := hf
  obtain ⟨D, e, hD⟩ := hg
  refine ⟨C + D, max d e, fun n ↦ ?_⟩
  have hd := Nat.pow_le_pow_right (Nat.succ_pos n) (Nat.le_max_left d e)
  have he := Nat.pow_le_pow_right (Nat.succ_pos n) (Nat.le_max_right d e)
  calc
    f n + g n ≤ C * (n + 1) ^ d + D * (n + 1) ^ e := Nat.add_le_add (hC n) (hD n)
    _ ≤ C * (n + 1) ^ max d e + D * (n + 1) ^ max d e :=
      Nat.add_le_add (Nat.mul_le_mul_left C hd) (Nat.mul_le_mul_left D he)
    _ = (C + D) * (n + 1) ^ max d e := (Nat.add_mul ..).symm

/-- The product of two polynomially bounded functions is polynomially bounded. -/
public theorem mul {f g : Nat → Nat} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n ↦ f n * g n) := by
  obtain ⟨C, d, hC⟩ := hf
  obtain ⟨D, e, hD⟩ := hg
  refine ⟨C * D, d + e, fun n ↦ ?_⟩
  calc
    f n * g n ≤ (C * (n + 1) ^ d) * (D * (n + 1) ^ e) := Nat.mul_le_mul (hC n) (hD n)
    _ = (C * D) * (n + 1) ^ (d + e) := by
      rw [Nat.pow_add]
      ac_rfl

/-- Each fixed natural power of a polynomially bounded function is polynomially bounded. -/
public theorem pow {f : Nat → Nat} (hf : PolynomiallyBounded f) (k : Nat) :
    PolynomiallyBounded (fun n ↦ f n ^ k) := by
  induction k with
  | zero => simpa only [Nat.pow_zero] using const 1
  | succ k ih => simpa only [Nat.pow_succ] using ih.mul hf

/-- A polynomial bound at a polynomially bounded input length is still polynomial. -/
public theorem comp {f g : Nat → Nat} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n ↦ f (g n)) := by
  obtain ⟨C, d, hC⟩ := hf
  obtain ⟨D, e, hD⟩ := hg
  refine ⟨C * (D + 1) ^ d, e * d, fun n ↦ ?_⟩
  have hpow : 1 ≤ (n + 1) ^ e := by
    simpa only [Nat.pow_zero] using
      Nat.pow_le_pow_right (Nat.succ_pos n) (Nat.zero_le e)
  have hsize : g n + 1 ≤ (D + 1) * (n + 1) ^ e := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add (hD n) hpow
  calc
    f (g n) ≤ C * (g n + 1) ^ d := hC (g n)
    _ ≤ C * ((D + 1) * (n + 1) ^ e) ^ d :=
      Nat.mul_le_mul_left C (Nat.pow_le_pow_left hsize d)
    _ = (C * (D + 1) ^ d) * (n + 1) ^ (e * d) := by
      rw [Nat.mul_pow, Nat.pow_mul, Nat.mul_assoc]

end PolynomiallyBounded

/-- No polynomial in the exponent bounds the function `n ↦ 2^n`. -/
public theorem pow_two_not_polynomiallyBounded :
    ¬ PolynomiallyBounded (fun k ↦ 2 ^ k) := by
  rintro ⟨C, d, h⟩
  let a := C + 3 * d + 1
  let n := 2 ^ (a + a)
  have ha : 0 < a := Nat.succ_pos _
  have hn : 0 < n := Nat.pow_pos (by decide)
  have hCa : C ≤ C * a := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left C ha
  have hExponent : C + (a + a + 1) * d < n := by
    calc
      _ ≤ C * a + (3 * a) * d :=
        Nat.add_le_add hCa (Nat.mul_le_mul_right d (by omega))
      _ = (C + 3 * d) * a := by rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm a d]
      _ < a * a := Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) ha
      _ ≤ n := by
        change _ ≤ 2 ^ (a + a)
        rw [Nat.pow_add]
        exact Nat.mul_le_mul (Nat.le_of_lt (Nat.lt_pow_self (by decide)))
          (Nat.le_of_lt (Nat.lt_pow_self (by decide)))
  have hPoly : C * (n + 1) ^ d ≤ 2 ^ (C + (a + a + 1) * d) := by
    calc
      _ ≤ 2 ^ C * (n * 2) ^ d :=
        Nat.mul_le_mul (Nat.le_of_lt (Nat.lt_pow_self (by decide)))
          (Nat.pow_le_pow_left (by omega) d)
      _ = 2 ^ (C + (a + a + 1) * d) := by
        change 2 ^ C * (2 ^ (a + a) * 2) ^ d = _
        rw [← Nat.pow_succ, ← Nat.pow_mul, ← Nat.pow_add]
  exact (Nat.not_lt_of_ge (Nat.le_trans (h n) hPoly)) (Nat.pow_lt_pow_right (by decide) hExponent)

/-- The coefficient-and-degree bound is equivalent to Cook's `n ^ k + k` bound. -/
public theorem polynomiallyBounded_iff_cook (f : Nat → Nat) :
    PolynomiallyBounded f ↔ ∃ k : Nat, ∀ n : Nat, f n ≤ n ^ k + k := by
  constructor
  · rintro ⟨C, d, h⟩
    let B := C * 2 ^ d
    refine ⟨d + (B + 1), fun n ↦ ?_⟩
    by_cases hn : n ≤ 1
    · have hn' : n + 1 ≤ 2 := Nat.add_le_add_right hn 1
      calc
        f n ≤ C * (n + 1) ^ d := h n
        _ ≤ B := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hn' d)
        _ ≤ n ^ (d + (B + 1)) + (d + (B + 1)) := by omega
    · have hn' : 2 ≤ n := by omega
      have hdouble : n + 1 ≤ 2 * n := by rw [Nat.two_mul]; omega
      have hB : B ≤ n ^ (B + 1) := by
        exact Nat.le_trans (Nat.le_succ B) (Nat.le_of_lt (Nat.lt_pow_self hn'))
      calc
        f n ≤ C * (n + 1) ^ d := h n
        _ ≤ C * (2 * n) ^ d := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hdouble d)
        _ = n ^ d * B := by rw [Nat.mul_pow, ← Nat.mul_assoc, Nat.mul_comm (C * 2 ^ d)]
        _ ≤ n ^ d * n ^ (B + 1) := Nat.mul_le_mul_left (n ^ d) hB
        _ = n ^ (d + (B + 1)) := (Nat.pow_add ..).symm
        _ ≤ n ^ (d + (B + 1)) + (d + (B + 1)) := Nat.le_add_right ..
  · rintro ⟨k, h⟩
    refine ⟨1 + k, k, fun n ↦ ?_⟩
    have hpow : 1 ≤ (n + 1) ^ k := by
      simpa only [Nat.pow_zero] using
        Nat.pow_le_pow_right (Nat.succ_pos n) (Nat.zero_le k)
    calc
      f n ≤ n ^ k + k := h n
      _ ≤ (n + 1) ^ k + k * (n + 1) ^ k := by
        exact Nat.add_le_add (Nat.pow_le_pow_left (Nat.le_succ n) k)
          (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left k hpow)
      _ = (1 + k) * (n + 1) ^ k := by rw [Nat.add_mul, Nat.one_mul]

end PvsNP
