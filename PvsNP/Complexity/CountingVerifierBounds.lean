module

public import PvsNP.Complexity.CertificateEnumeration
public import PvsNP.Complexity.CertificateLengthBound
public import PvsNP.Complexity.CountingPadding
public import PvsNP.Complexity.VerifierCircuits

import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Card

/-! # Certificate bounds for the counting language -/

public section

namespace PvsNP

open Circuits

/-- Any correct Cook verifier using candidate lists of polynomially bounded
certificate length requires exponentially many candidates up to a polynomial factor. -/
theorem countingHardLanguage_candidateCount_lower (A : CheckingAlphabet)
    (V : Machine A.Symbol) (hTime : V.PolyTime) (candidates : Nat → List (List A.Certificate))
    {cap : Nat → Nat} (hCap : PolynomiallyBounded cap)
    (hLength : ∀ n y, y ∈ candidates n → y.length ≤ cap n)
    (hCorrect : ∀ x : BinaryWord,
      x ∈ countingHardLanguage ↔ ∃ y ∈ candidates x.length, V.Accepts (A.encode x y)) :
    ∃ g, PolynomiallyBounded g ∧ ∀ n ≥ 10, 2 ^ n ≤ (candidates n).length * g n := by
  obtain ⟨family, g, hg, hSize, hEval⟩ :=
    V.exists_candidateProjectionCircuits A hTime candidates hCap hLength
  have hLinear : PolynomiallyBounded (fun n ↦ 8 * n) :=
    (PolynomiallyBounded.const 8).mul PolynomiallyBounded.id
  refine ⟨fun n ↦ (g n + 1) * (8 * n), (hg.add (PolynomiallyBounded.const 1)).mul hLinear,
    fun n hn ↦ ?_⟩
  have hCorrectSlice (x : Fin n → Bool) : (family n).eval x = true ↔
      List.ofFn x ∈ countingHardLanguage :=
    (hEval n x).trans (by simpa only [List.length_ofFn] using (hCorrect (List.ofFn x)).symm)
  have hCircuit := countingHardLanguage_size_gt n (by omega) (family n) hCorrectSlice
  have hLower := hCircuit.trans_le (hSize n)
  have hPos : 1 ≤ (candidates n).length := by
    by_contra! hZero
    have hBudget := le_countingBudget n hn
    simp only [Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hZero), Nat.zero_mul,
      Nat.zero_add] at hLower
    omega
  have hCount : (candidates n).length * g n + 1 ≤ (candidates n).length * (g n + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    exact Nat.add_le_add_left hPos _
  unfold countingBudget at hLower
  have hPower := (Nat.div_lt_iff_lt_mul (by omega : 0 < 8 * n)).mp hLower
  exact hPower.le.trans ((Nat.mul_le_mul_right (8 * n) hCount).trans_eq (Nat.mul_assoc ..))

/-- The distinct listed certificates that accept at least one input of length `n`. -/
noncomputable def acceptingCertificatesAtLength (A : CheckingAlphabet)
    (V : Machine A.Symbol) (n : Nat) (candidates : List (List A.Certificate)) :
    Finset (List A.Certificate) := by
  classical
  exact candidates.toFinset.filter fun y ↦ ∃ x : Fin n → Bool, V.Accepts (A.encode (List.ofFn x) y)

theorem mem_acceptingCertificatesAtLength (A : CheckingAlphabet)
    (V : Machine A.Symbol) (n : Nat) (candidates : List (List A.Certificate))
    (y : List A.Certificate) :
    y ∈ acceptingCertificatesAtLength A V n candidates ↔
      y ∈ candidates ∧ ∃ x : Fin n → Bool, V.Accepts (A.encode (List.ofFn x) y) := by
  classical
  simp only [acceptingCertificatesAtLength, Finset.mem_filter, List.mem_toFinset]

/-- The lower bound still holds after discarding duplicate certificates and
those that cannot accept any input at the given length. -/
theorem countingHardLanguage_acceptingCertificateCount_lower (A : CheckingAlphabet)
    (V : Machine A.Symbol) (hTime : V.PolyTime) (candidates : Nat → List (List A.Certificate))
    {cap : Nat → Nat} (hCap : PolynomiallyBounded cap)
    (hLength : ∀ n y, y ∈ candidates n → y.length ≤ cap n)
    (hCorrect : ∀ x : BinaryWord,
      x ∈ countingHardLanguage ↔ ∃ y ∈ candidates x.length, V.Accepts (A.encode x y)) :
    ∃ g, PolynomiallyBounded g ∧ ∀ n ≥ 10,
      2 ^ n ≤ (acceptingCertificatesAtLength A V n (candidates n)).card * g n := by
  let eligible (n : Nat) := (acceptingCertificatesAtLength A V n (candidates n)).toList
  have hMem {n} {y : List A.Certificate} : y ∈ eligible n ↔
      y ∈ candidates n ∧ ∃ x : Fin n → Bool, V.Accepts (A.encode (List.ofFn x) y) :=
    Finset.mem_toList.trans (mem_acceptingCertificatesAtLength A V n (candidates n) y)
  have hEligible (x : BinaryWord) :
      x ∈ countingHardLanguage ↔ ∃ y ∈ eligible x.length, V.Accepts (A.encode x y) := by
    rw [hCorrect x]
    constructor
    · rintro ⟨y, hy, hAccept⟩
      let bits (i : Fin x.length) := x[i.val]
      have hBits : List.ofFn bits = x := List.ofFn_getElem
      exact ⟨y, hMem.mpr ⟨hy, bits, by simpa only [hBits] using hAccept⟩, hAccept⟩
    · rintro ⟨y, hy, hAccept⟩
      exact ⟨y, (hMem.mp hy).1, hAccept⟩
  obtain ⟨g, hg, hLower⟩ := countingHardLanguage_candidateCount_lower A V hTime eligible hCap
    (fun n y h ↦ hLength n y (hMem.mp h).1) hEligible
  exact ⟨g, hg, by simpa only [eligible, Finset.length_toList] using hLower⟩

/-- Over an alphabet with `q` symbols, allowing every certificate up to
length `cap n` gives at most a polynomial factor times `q ^ cap n` candidates. -/
theorem countingHardLanguage_certificateLength_lower (A : CheckingAlphabet) [Fintype A.Certificate]
    (V : Machine A.Symbol) (hTime : V.PolyTime) {cap : Nat → Nat}
    (hCap : PolynomiallyBounded cap)
    (hCorrect : ∀ x : BinaryWord, x ∈ countingHardLanguage ↔
      ∃ y, y.length ≤ cap x.length ∧ V.Accepts (A.encode x y)) :
    ∃ g, PolynomiallyBounded g ∧ ∀ n ≥ 10, 2 ^ n ≤ Fintype.card A.Certificate ^ cap n * g n := by
  classical
  let alphabet : List A.Certificate := List.ofFn (Fintype.equivFin A.Certificate).symm
  let candidates (n : Nat) := wordsUpToLength alphabet (cap n)
  have hCovers (a : A.Certificate) : a ∈ alphabet :=
    List.mem_ofFn.mpr ⟨Fintype.equivFin A.Certificate a, (Fintype.equivFin _).symm_apply_apply _⟩
  have hMember {n : Nat} {y : List A.Certificate} : y ∈ candidates n ↔ y.length ≤ cap n :=
    mem_wordsUpToLength_iff_of_covers hCovers
  have hPositive : 0 < alphabet.length := by
    obtain ⟨a⟩ := A.certificateNonempty
    exact List.length_pos_of_mem (hCovers a)
  obtain ⟨g, hg, hLower⟩ := countingHardLanguage_candidateCount_lower A V hTime candidates
    hCap (fun _ _ ↦ hMember.mp) (fun x ↦ by simpa only [hMember] using hCorrect x)
  have hFactor := (hCap.add (PolynomiallyBounded.const 1)).mul hg
  refine ⟨fun n ↦ (cap n + 1) * g n, hFactor, fun n hn ↦ ?_⟩
  have hLength : (candidates n).length ≤ (cap n + 1) * Fintype.card A.Certificate ^ cap n := by
    simpa only [alphabet, candidates, List.length_ofFn] using
      length_wordsUpToLength_le alphabet (cap n) hPositive
  calc
    2 ^ n ≤ (candidates n).length * g n := hLower n hn
    _ ≤ ((cap n + 1) * Fintype.card A.Certificate ^ cap n) * g n :=
      Nat.mul_le_mul_right _ hLength
    _ = Fintype.card A.Certificate ^ cap n * ((cap n + 1) * g n) := by ac_rfl

/-- For binary certificates, any polynomial-time verifier for the counting
language needs a cap of at least `n` minus a logarithmic term. -/
theorem countingHardLanguage_binaryCertificateLength_lower (V : Machine VerifierSymbol)
    (hTime : V.PolyTime) {cap : Nat → Nat} (hCap : PolynomiallyBounded cap)
    (hCorrect : ∀ x : BinaryWord, x ∈ countingHardLanguage ↔
      ∃ y : BinaryWord, y.length ≤ cap x.length ∧ V.Accepts (encodePair x y)) :
    ∃ C d : Nat, ∀ n ≥ 10, n ≤ cap n + C + d * (Nat.log2 (n + 1) + 1) := by
  let _ : Fintype binaryCheckingAlphabet.Certificate := inferInstanceAs (Fintype Bool)
  have hPairs (x y : BinaryWord) : encodePair x y = binaryCheckingAlphabet.encode x y := by
    rw [encodePair_eq]
    rfl
  have hExact (x : BinaryWord) : x ∈ countingHardLanguage ↔
      ∃ y : List binaryCheckingAlphabet.Certificate,
        y.length ≤ cap x.length ∧ V.Accepts (binaryCheckingAlphabet.encode x y) := by
    constructor
    · intro hx
      obtain ⟨y, hy, ha⟩ := (hCorrect x).mp hx
      exact ⟨y, hy, (hPairs x y) ▸ ha⟩
    · rintro ⟨y, hy, ha⟩
      exact (hCorrect x).mpr ⟨y, hy, (hPairs x y).symm ▸ ha⟩
  obtain ⟨g, hg, hPower⟩ :=
    countingHardLanguage_certificateLength_lower binaryCheckingAlphabet V hTime hCap hExact
  apply binaryCertificateLength_lower_of_pow_bound hg 10
  intro n hn
  have hCard : Fintype.card binaryCheckingAlphabet.Certificate = 2 := by decide
  simpa only [hCard] using hPower n hn

/-- Over a unary alphabet, polynomially bounded lengths give too few
certificate candidates for any polynomial-time verifier of the counting language. -/
theorem countingHardLanguage_no_unaryCertificateVerifier (A : CheckingAlphabet)
    [Fintype A.Certificate] (hCard : Fintype.card A.Certificate = 1)
    (V : Machine A.Symbol) (hTime : V.PolyTime) {cap : Nat → Nat}
    (hCap : PolynomiallyBounded cap) :
    ¬ ∀ x : BinaryWord, x ∈ countingHardLanguage ↔
      ∃ y, y.length ≤ cap x.length ∧ V.Accepts (A.encode x y) := by
  intro hCorrect
  obtain ⟨g, hg, hPower⟩ :=
    countingHardLanguage_certificateLength_lower A V hTime hCap hCorrect
  simp only [hCard, Nat.one_pow, Nat.one_mul] at hPower
  apply pow_two_not_polynomiallyBounded
  refine (hg.add (PolynomiallyBounded.const (2 ^ 10))).mono fun n ↦ ?_
  by_cases hn : 10 ≤ n
  · exact (hPower n hn).trans (Nat.le_add_right ..)
  · exact (Nat.pow_le_pow_right (by decide) (by omega : n ≤ 10)).trans (Nat.le_add_left ..)

end PvsNP
