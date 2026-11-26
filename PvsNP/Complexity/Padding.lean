module

public import PvsNP.Circuits.InputLayout
public import PvsNP.Circuits.TruthTableUpperBound
public import PvsNP.Complexity.CircuitLowerBound

import Init.Data.List.Nat.TakeDrop

/-! # Zero padding and polynomial-size circuits -/

public section

namespace PvsNP

open Circuits

/-- Append false bits to reach the prescribed target length. -/
@[expose] def zeroPad (length : Nat → Nat) (word : BinaryWord) : BinaryWord :=
  word ++ List.replicate (length word.length - word.length) false

/-- The image of a binary language under zero padding. -/
@[expose] def zeroPaddedLanguage (length : Nat → Nat) (L : BinaryLanguage) : BinaryLanguage :=
  {word | ∃ u ∈ L, zeroPad length u = word}

theorem length_zeroPad {length : Nat → Nat} (hLength : ∀ n, n ≤ length n)
    (word : BinaryWord) : (zeroPad length word).length = length word.length := by
  simp only [zeroPad, List.length_append, List.length_replicate, Nat.add_sub_of_le (hLength _)]

/-- At a length in the image of an injective profile, membership tests the
unique prefix length and verifies that the suffix is all false. -/
theorem mem_zeroPaddedLanguage_iff {length : Nat → Nat} {L : BinaryLanguage}
    (hLength : ∀ n, n ≤ length n) (hInjective : Function.Injective length)
    {n : Nat} {word : BinaryWord} (h : length n = word.length) :
    word ∈ zeroPaddedLanguage length L ↔
      word.take n ∈ L ∧ ∀ b ∈ word.drop n, b = false := by
  constructor
  · rintro ⟨u, hPrefix, rfl⟩
    have hPrefixLength : u.length = n :=
      hInjective ((length_zeroPad hLength u).symm.trans h.symm)
    rw [← hPrefixLength]
    simp only [zeroPad, List.take_left, List.drop_left]
    exact ⟨hPrefix, fun _ ↦ List.eq_of_mem_replicate⟩
  · rintro ⟨hPrefix, hSuffix⟩
    have hn : n ≤ word.length := (hLength n).trans h.le
    have hTake : (word.take n).length = n := List.length_take_of_le hn
    have hDrop : word.drop n = List.replicate (length n - n) false :=
      List.eq_replicate_iff.mpr ⟨by rw [List.length_drop, h], hSuffix⟩
    refine ⟨word.take n, hPrefix, ?_⟩
    rw [zeroPad, hTake, ← hDrop, List.take_append_drop]

theorem zeroPad_mem_zeroPaddedLanguage_iff {length : Nat → Nat} {L : BinaryLanguage}
    (hLength : ∀ n, n ≤ length n) (hInjective : Function.Injective length)
    (word : BinaryWord) : zeroPad length word ∈ zeroPaddedLanguage length L ↔ word ∈ L := by
  rw [mem_zeroPaddedLanguage_iff hLength hInjective (length_zeroPad hLength word).symm]
  simp only [zeroPad, List.take_left, List.drop_left]
  exact ⟨And.left, fun h ↦ ⟨h, fun _ ↦ List.eq_of_mem_replicate⟩⟩

private theorem take_ofFn_eq {n m : Nat} (h : n ≤ m) (x : Fin m → Bool) :
    (List.ofFn x).take n = List.ofFn (x ∘ Fin.castLE h) := by
  apply List.ext_getElem
  · rw [List.length_take, List.length_ofFn, List.length_ofFn, Nat.min_eq_left h]
  · intro i hi hj
    simp only [List.getElem_take, List.getElem_ofFn, Function.comp_apply]
    rfl

private theorem drop_ofFn_all_false_iff {n m : Nat} (x : Fin m → Bool) :
    (∀ b ∈ (List.ofFn x).drop n, b = false) ↔ ∀ i : Fin m, n ≤ i.val → x i = false := by
  have hDrop : ((List.ofFn x).drop n).length = m - n := by simp
  constructor
  · intro h i hi
    have hj : i.val - n < ((List.ofFn x).drop n).length := by rw [hDrop]; omega
    have hb := h _ (List.getElem_mem hj)
    simp only [List.getElem_drop, List.getElem_ofFn] at hb
    convert hb using 2
    exact Fin.ext (show i.val = n + (i.val - n) by omega)
  · intro h b hb
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hb
    simp only [List.getElem_drop, List.getElem_ofFn]
    exact h _ (show n ≤ n + j from Nat.le_add_right n j)

/-- A circuit for each original slice gives a circuit for the corresponding
padded slice. The bound is measured at the padded length. -/
theorem zeroPaddedLanguage_mem_PPoly_of_circuits {length : Nat → Nat} {L : BinaryLanguage}
    (hLength : ∀ n, n ≤ length n) (hInjective : Function.Injective length)
    (family : (n : Nat) → BooleanCircuit n) {g : Nat → Nat} (hg : PolynomiallyBounded g)
    (hSize : ∀ n, (family n).size ≤ g (length n))
    (hCorrect : ∀ n (x : Fin n → Bool), (family n).eval x = true ↔ List.ofFn x ∈ L) :
    zeroPaddedLanguage length L ∈ PPoly := by
  classical
  let circuit (m : Nat) : BooleanCircuit m :=
    if hm : ∃ n, length n = m then
      (family (Classical.choose hm)).liftPrefixWithFalseSuffix
        ((hLength _).trans (Classical.choose_spec hm).le)
    else BooleanCircuit.const m false
  have hOverhead : PolynomiallyBounded (fun m ↦ 2 * m + 2) :=
    ((PolynomiallyBounded.const 2).mul PolynomiallyBounded.id).add
      (PolynomiallyBounded.const 2)
  refine ⟨circuit, (hg.add hOverhead).mono ?_, ?_⟩
  · intro m
    by_cases hm : ∃ n, length n = m
    · simp only [circuit, dite_eq_left hm]
      have hBound := hSize (Classical.choose hm)
      rw [Classical.choose_spec hm] at hBound
      exact (BooleanCircuit.size_liftPrefixWithFalseSuffix_le _ _).trans
        (Nat.add_le_add_right hBound _)
    · simp only [circuit, dite_eq_right hm, BooleanCircuit.size_const]
      omega
  · intro m x
    by_cases hm : ∃ n, length n = m
    · let n := Classical.choose hm
      have h : length n = m := Classical.choose_spec hm
      have hx : length n = (List.ofFn x).length := h.trans List.length_ofFn.symm
      simp only [circuit, dite_eq_left hm]
      rw [BooleanCircuit.eval_liftPrefixWithFalseSuffix_eq_true, hCorrect,
        ← take_ofFn_eq, ← drop_ofFn_all_false_iff,
        mem_zeroPaddedLanguage_iff hLength hInjective hx]
    · simp only [circuit, dite_eq_right hm, BooleanCircuit.eval_const, Bool.false_eq_true,
        false_iff]
      rintro ⟨u, _, hPad⟩
      apply hm
      exact ⟨u.length, (length_zeroPad hLength u).symm.trans
        ((congrArg List.length hPad).trans List.length_ofFn)⟩

/-- If the padded length polynomially dominates the number of possible
unpadded inputs, any padded language has polynomial-size circuits. -/
theorem zeroPaddedLanguage_mem_PPoly_of_pow_two_bound {length : Nat → Nat}
    (L : BinaryLanguage) (hLength : ∀ n, n ≤ length n)
    (hInjective : Function.Injective length)
    (hBound : ∃ g, PolynomiallyBounded g ∧ ∀ n, 2 ^ n ≤ g (length n)) :
    zeroPaddedLanguage length L ∈ PPoly := by
  classical
  obtain ⟨g, hg, hSize⟩ := hBound
  let family (n : Nat) :=
    truthTableCircuit n (fun x ↦ decide (List.ofFn x ∈ L))
  apply zeroPaddedLanguage_mem_PPoly_of_circuits hLength hInjective family
    ((PolynomiallyBounded.const 5).mul hg)
  · intro n
    exact (truthTableCircuit_size_le n _).trans (Nat.mul_le_mul_left 5 (hSize n))
  · intro n x
    simp only [family, truthTableCircuit_eval, decide_eq_true_eq]

private theorem ofFn_zeroExtend {length : Nat → Nat} (hLength : ∀ n, n ≤ length n)
    {n : Nat} (x : Fin n → Bool) :
    List.ofFn (zeroExtend (hLength n) x) = zeroPad length (List.ofFn x) := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, length_zeroPad hLength]
  · intro i hi hj
    simp only [List.getElem_ofFn]
    change i < (List.ofFn x ++
      List.replicate (length (List.ofFn x).length - (List.ofFn x).length) false).length at hj
    unfold zeroPad
    by_cases h : i < n
    · change zeroExtend (hLength n) x ((⟨i, h⟩ : Fin n).castLE (hLength n)) = _
      have hPrefix : i < (List.ofFn x).length := by simpa only [List.length_ofFn] using h
      rw [zeroExtend_castLE, List.getElem_append_left hPrefix, List.getElem_ofFn]
    · have hSuffix : (List.ofFn x).length ≤ i := by
        simpa only [List.length_ofFn] using Nat.le_of_not_gt h
      rw [zeroExtend_of_le _ _ (Nat.le_of_not_gt h), List.getElem_append_right hSuffix,
        List.getElem_replicate]

/-- Fixing a padded circuit's suffix inputs to false gives a circuit for the
original slice, with a polynomial bound in the padded length. -/
theorem exists_circuits_of_zeroPaddedLanguage_mem_PPoly {length : Nat → Nat} {L : BinaryLanguage}
    (hLength : ∀ n, n ≤ length n) (hInjective : Function.Injective length)
    (hPadded : zeroPaddedLanguage length L ∈ PPoly) :
    ∃ (family : (n : Nat) → BooleanCircuit n) (g : Nat → Nat), PolynomiallyBounded g ∧
      (∀ n, (family n).size ≤ g (length n)) ∧
      ∀ n (x : Fin n → Bool), (family n).eval x = true ↔ List.ofFn x ∈ L := by
  obtain ⟨padded, hSize, hCorrect⟩ := hPadded
  let circuit (n : Nat) := (padded (length n)).restrictFalseSuffix (hLength n)
  refine ⟨circuit, _, hSize.add (PolynomiallyBounded.const 1), ?_, ?_⟩
  · intro n
    simp only [circuit, BooleanCircuit.size_restrictFalseSuffix, Nat.le_refl]
  · intro n x
    simp only [circuit, BooleanCircuit.eval_restrictFalseSuffix, hCorrect, ofFn_zeroExtend hLength,
      zeroPad_mem_zeroPaddedLanguage_iff hLength hInjective]

/-- Polynomially bounded injective length padding preserves polynomial
circuit size in both directions. -/
theorem zeroPaddedLanguage_mem_PPoly_iff {length : Nat → Nat} {L : BinaryLanguage}
    (hLength : ∀ n, n ≤ length n) (hInjective : Function.Injective length)
    (hPoly : PolynomiallyBounded length) :
    zeroPaddedLanguage length L ∈ PPoly ↔ L ∈ PPoly := by
  constructor
  · intro hPadded
    obtain ⟨family, _, hBound, hSize, hCorrect⟩ :=
      exists_circuits_of_zeroPaddedLanguage_mem_PPoly hLength hInjective hPadded
    exact ⟨family, (hBound.comp hPoly).mono hSize, hCorrect⟩
  · rintro ⟨family, ⟨C, d, hSize⟩, hCorrect⟩
    have hBound : PolynomiallyBounded (fun n ↦ C * (n + 1) ^ d) := ⟨C, d, fun _ ↦ le_rfl⟩
    refine zeroPaddedLanguage_mem_PPoly_of_circuits hLength hInjective family hBound ?_ hCorrect
    intro n
    exact (hSize n).trans (Nat.mul_le_mul_left C
      (Nat.pow_le_pow_left (Nat.add_le_add_right (hLength n) 1) d))

end PvsNP
