module

public import PvsNP.Complexity.CircuitLowerBound

/-! # Circuits for Cook verifiers with fixed certificates -/

public section

namespace PvsNP

open Circuits

/-- At a fixed instance length, hardwire a certificate into the exact Cook input.
One polynomial bounds circuit size uniformly over every certificate below the cap. -/
theorem Machine.exists_boundedCertificateCircuits (A : CheckingAlphabet) (V : Machine A.Symbol)
    (hTime : V.PolyTime) {cap : Nat → Nat} (hCap : PolynomiallyBounded cap) :
    ∃ (family : (n : Nat) → List A.Certificate → BooleanCircuit n) (g : Nat → Nat),
      PolynomiallyBounded g ∧ ∀ n y, y.length ≤ cap n →
        (family n y).size ≤ g n ∧
        ∀ x : Fin n → Bool, (family n y).eval x = true ↔ V.Accepts (A.encode (List.ofFn x) y) := by
  classical
  let _ : Finite V.State := V.stateFinite
  let _ : Finite V.Symbol := V.symbolFinite
  let _ : Fintype V.State := Fintype.ofFinite _
  let _ : Fintype V.Symbol := Fintype.ofFinite _
  obtain ⟨k, hRun⟩ := hTime
  let clock (n : Nat) := (n + cap n + 1) ^ k + k
  let width (n : Nat) := 2 * clock n + 1
  let initial (n : Nat) (y : List A.Certificate) : Layer n (windowBitCount V (width n)) :=
    fun i ↦ windowMappedStartExpr V A.bit (A.separator :: y.map A.certificate) n
      (Machine.windowCenter (clock n)) ((windowIndex V (width n)).symm i)
  let family (n : Nat) (y : List A.Certificate) :=
    (machineFromWindowLayered V (clock n) (initial n y)).toBooleanCircuit 0
  have hClock : PolynomiallyBounded clock :=
    (((PolynomiallyBounded.id.add hCap).add (PolynomiallyBounded.const 1)).pow k).add
      (PolynomiallyBounded.const k)
  have hWidth : PolynomiallyBounded width :=
    ((PolynomiallyBounded.const 2).mul hClock).add (PolynomiallyBounded.const 1)
  have hInitBound := (windowBitCount_polynomiallyBounded V hWidth).mul
    (PolynomiallyBounded.const 8)
  refine ⟨family, _, hInitBound.add (machineWindowGateOverhead_polynomiallyBounded V hClock),
    fun n y hy ↦ ⟨?_, ?_⟩⟩
  · have hInitSize : (initial n y).size ≤ windowBitCount V (width n) * 8 :=
      Layer.size_le_of_forall _ 8 (fun _ ↦ windowMappedStartExpr_size_le V _ _ _ _ _)
    exact (Layered.size_toBooleanCircuit_le _ _).trans
      ((machineFromWindowLayered_size_le V (clock n) (initial n y)).trans
        (Nat.add_le_add_right hInitSize _))
  · intro x
    let input := A.encode (List.ofFn x) y
    have hLength : input.length ≤ n + cap n + 1 := by
      simp only [input, CheckingAlphabet.length_encode, List.length_ofFn]
      omega
    obtain ⟨t, ht, b, hb⟩ := hRun input
    have hHalt : V.HaltsWithin input (clock n) :=
      ⟨t, ht.trans (Nat.add_le_add_right (Nat.pow_le_pow_left hLength k) k), b, hb⟩
    have hInit : (initial n y).eval x =
        encodeWindow V (V.windowStart (Machine.windowCenter (clock n)) input) ∘
          (windowIndex V (width n)).symm := by
      funext i
      exact windowMappedStartExpr_eval V _ _ _ x _
    change (family n y).eval x = true ↔ V.Accepts input
    simp only [family, Layered.eval_toBooleanCircuit]
    rw [machineFromWindowLayered_eval V _ _ x _ hInit,
      V.windowRun_start_state (clock n) (clock n) (Nat.le_refl _) input]
    exact (V.accepts_iff_at_bound input hHalt).symm

/-- Taking the disjunction over a fixed list of certificate candidates costs
one verifier circuit per entry, all with the same polynomial gate bound. -/
theorem Machine.exists_candidateProjectionCircuits (A : CheckingAlphabet) (V : Machine A.Symbol)
    (hTime : V.PolyTime) (candidates : Nat → List (List A.Certificate))
    {cap : Nat → Nat} (hCap : PolynomiallyBounded cap)
    (hLength : ∀ n y, y ∈ candidates n → y.length ≤ cap n) :
    ∃ (family : (n : Nat) → BooleanCircuit n) (g : Nat → Nat), PolynomiallyBounded g ∧
      (∀ n, (family n).size ≤ (candidates n).length * g n + 1) ∧
      ∀ n (x : Fin n → Bool), (family n).eval x = true ↔
        ∃ y ∈ candidates n, V.Accepts (A.encode (List.ofFn x) y) := by
  obtain ⟨verify, g, hg, hVerify⟩ := V.exists_boundedCertificateCircuits A hTime hCap
  let family (n : Nat) := BooleanCircuit.orList ((candidates n).map (verify n))
  refine ⟨family, fun n ↦ g n + 1, hg.add (PolynomiallyBounded.const 1), ?_, ?_⟩
  · intro n
    have hSize := BooleanCircuit.size_orList_le ((candidates n).map (verify n)) (g n) (by
      intro c hc
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hc
      exact (hVerify n y (hLength n y hy)).1)
    simpa only [family, List.length_map] using hSize
  · intro n x
    simp only [family, BooleanCircuit.eval_orList_eq_true]
    constructor
    · rintro ⟨c, hc, hAccept⟩
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hc
      exact ⟨y, hy, ((hVerify n y (hLength n y hy)).2 x).mp hAccept⟩
    · rintro ⟨y, hy, hAccept⟩
      exact ⟨verify n y, List.mem_map_of_mem hy, ((hVerify n y (hLength n y hy)).2 x).mpr hAccept⟩

/-- Polynomially many polynomial-length candidates per length give polynomial
circuit size even when choosing the candidate lists is nonuniform. -/
theorem mem_PPoly_of_polynomialCertificateCandidates {L : BinaryLanguage}
    (A : CheckingAlphabet) (V : Machine A.Symbol) (hTime : V.PolyTime)
    (candidates : Nat → List (List A.Certificate)) {cap : Nat → Nat}
    (hCap : PolynomiallyBounded cap) (hLength : ∀ n y, y ∈ candidates n → y.length ≤ cap n)
    (hCount : PolynomiallyBounded (fun n ↦ (candidates n).length))
    (hCorrect : ∀ x : BinaryWord, x ∈ L ↔ ∃ y ∈ candidates x.length, V.Accepts (A.encode x y)) :
    L ∈ PPoly := by
  obtain ⟨family, _, hg, hSize, hEval⟩ :=
    V.exists_candidateProjectionCircuits A hTime candidates hCap hLength
  refine ⟨family, ((hCount.mul hg).add (PolynomiallyBounded.const 1)).mono hSize, fun n x ↦ ?_⟩
  exact (hEval n x).trans (by simpa only [List.length_ofFn] using (hCorrect (List.ofFn x)).symm)

end PvsNP
