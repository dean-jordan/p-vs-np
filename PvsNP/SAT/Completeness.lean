module

public import PvsNP.CookLevin.BinaryReduction
public import PvsNP.CookLevin.Generator.VerifierProgram
public import PvsNP.SAT.VerifierMachine

import PvsNP.Complexity.Containment

/-!
# NP-completeness of binary CNF satisfiability

The deterministic checker and the tableau generator establish NP-completeness
for the project’s binary CNF encoding.
-/

public section

namespace PvsNP.SATAssignment

/-- The two machine implementations suffice to establish completeness. -/
theorem npComplete_CNFSAT_of_machines (hCompile : CookLevin.BinaryTableauxPolyTime)
    (hCheck : {pair : VerifierWord | checkEncoded pair = true} ∈ POver VerifierSymbol) :
    NPComplete CNFSAT :=
  ⟨mem_NP_of_checkEncoded_mem_P hCheck, fun _ ↦ CookLevin.mem_NP_reduces_to_CNFSAT hCompile⟩

/-- The tableau compiler and a polynomial decider for CNF together give equality. -/
theorem p_eq_np_of_CNFSAT_mem_P (hCompile : CookLevin.BinaryTableauxPolyTime)
    (hDecide : CNFSAT ∈ P) : P = NP :=
  p_eq_np_iff_np_subset_p.mpr fun _ hL ↦
    (CookLevin.mem_NP_reduces_to_CNFSAT hCompile hL).mem_P hDecide

/-- The polynomial checker and a lower bound for CNF together give separation. -/
theorem p_ne_np_of_CNFSAT_not_mem_P
    (hCheck : {pair : VerifierWord | checkEncoded pair = true} ∈ POver VerifierSymbol)
    (hLowerBound : CNFSAT ∉ P) : P ≠ NP :=
  fun hEq ↦ hLowerBound (hEq.symm ▸ mem_NP_of_checkEncoded_mem_P hCheck)

theorem p_eq_np_iff_CNFSAT_mem_P (hCompile : CookLevin.BinaryTableauxPolyTime)
    (hCheck : {pair : VerifierWord | checkEncoded pair = true} ∈ POver VerifierSymbol) :
    P = NP ↔ CNFSAT ∈ P :=
  (npComplete_CNFSAT_of_machines hCompile hCheck).p_eq_np_iff_mem_P

/-- A polynomial tableau generator suffices for completeness once the checked verifier is used. -/
theorem npComplete_CNFSAT_of_compiler (hCompile : CookLevin.BinaryTableauxPolyTime) :
    NPComplete CNFSAT :=
  npComplete_CNFSAT_of_machines hCompile SATMachine.checkEncoded_mem_POver

theorem p_eq_np_iff_CNFSAT_mem_P_of_compiler (hCompile : CookLevin.BinaryTableauxPolyTime) :
    P = NP ↔ CNFSAT ∈ P :=
  (npComplete_CNFSAT_of_compiler hCompile).p_eq_np_iff_mem_P

/-- A lower bound for binary CNF would separate the classes using the checked verifier. -/
theorem p_ne_np_of_CNFSAT_lower_bound (hLowerBound : CNFSAT ∉ P) : P ≠ NP :=
  p_ne_np_of_CNFSAT_not_mem_P SATMachine.checkEncoded_mem_POver hLowerBound

/-- Every binary language in NP reduces in polynomial time to binary CNF satisfiability. -/
theorem mem_NP_polynomiallyReducesTo_CNFSAT {L : BinaryLanguage} (hL : L ∈ NP) :
    PolynomiallyReducesTo L CNFSAT :=
  CookLevin.mem_NP_reduces_to_CNFSAT CookLevin.binaryTableauxPolyTime_verified hL

/-- Binary CNF satisfiability is NP-complete for the Cook machine model. -/
theorem npComplete_CNFSAT : NPComplete CNFSAT :=
  npComplete_CNFSAT_of_compiler CookLevin.binaryTableauxPolyTime_verified

theorem p_eq_np_iff_CNFSAT_mem_P_verified : P = NP ↔ CNFSAT ∈ P :=
  npComplete_CNFSAT.p_eq_np_iff_mem_P

theorem p_ne_np_iff_CNFSAT_not_mem_P : P ≠ NP ↔ CNFSAT ∉ P :=
  not_congr p_eq_np_iff_CNFSAT_mem_P_verified

end PvsNP.SATAssignment
