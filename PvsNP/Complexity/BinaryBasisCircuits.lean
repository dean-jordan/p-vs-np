module

public import PvsNP.Circuits.BinaryBasisBridge
public import PvsNP.Complexity.CircuitLowerBound

/-! # Polynomial-size circuits over the full binary basis -/

@[expose] public section

namespace PvsNP

open Circuits

/-- Polynomial-size circuit families allowing every two-input Boolean operation. -/
def PPolyBinaryBasis : Set BinaryLanguage :=
  {L | ∃ circuit : (n : Nat) → BinaryBasisCircuit n,
    PolynomiallyBounded (fun n ↦ (circuit n).size) ∧
    ∀ n (x : Fin n → Bool), (circuit n).eval x = true ↔ List.ofFn x ∈ L}

/-- Allowing every binary operation preserves the polynomial-size circuit class. -/
theorem mem_PPolyBinaryBasis_iff (L : BinaryLanguage) : L ∈ PPolyBinaryBasis ↔ L ∈ PPoly := by
  constructor
  · rintro ⟨family, hSize, hCorrect⟩
    refine ⟨fun n ↦ (family n).toBooleanCircuit, ?_, fun n x ↦ ?_⟩
    · exact ((PolynomiallyBounded.const 4).mul hSize).mono
        (fun n ↦ (family n).size_toBooleanCircuit_le)
    · simpa only [BinaryBasisCircuit.eval_toBooleanCircuit] using hCorrect n x
  · rintro ⟨family, hSize, hCorrect⟩
    refine ⟨fun n ↦ BinaryBasisCircuit.ofBooleanCircuit (family n), hSize, fun n x ↦ ?_⟩
    simpa only [BinaryBasisCircuit.eval_ofBooleanCircuit] using hCorrect n x

theorem P_subset_PPolyBinaryBasis : P ⊆ PPolyBinaryBasis := by
  intro L hL
  exact (mem_PPolyBinaryBasis_iff L).mpr (P_subset_PPoly hL)

/-- A superpolynomial full-basis circuit lower bound for CNF-SAT would separate `P` and `NP`. -/
theorem p_ne_np_of_CNFSAT_not_mem_PPolyBinaryBasis (h : CNFSAT ∉ PPolyBinaryBasis) : P ≠ NP :=
  p_ne_np_of_CNFSAT_not_mem_PPoly (fun hSat ↦ h ((mem_PPolyBinaryBasis_iff CNFSAT).mpr hSat))

end PvsNP
