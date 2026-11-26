module

public import PvsNP.Circuits.BinaryBasisBridge
public import PvsNP.Circuits.BinaryBasisLowerBound
public import PvsNP.SAT.CircuitParitySize

/-! # A gate lower bound for binary CNF-SAT over arbitrary two-input gates -/

public section

namespace PvsNP.SATCircuitBounds

open Circuits

variable {n : Nat}

/-- Any two sufficiently interior bits admit both a parity cube and a signed
AND cube. The two cubes may use different fixed values elsewhere. -/
theorem cnfsat_binaryBasis_interior_pair (c : BinaryBasisCircuit n)
    (hDecides : ∀ x, c.eval x = true ↔ List.ofFn x ∈ CNFSAT) (i j : Fin n)
    (hEarly : 13 ≤ i.val) (hLate : j.val + 32 ≤ n) (hOrder : i.val < j.val) :
    BasisPair c.eval i j := by
  constructor
  · have hEval : c.toBooleanCircuit.eval = c.eval := funext c.eval_toBooleanCircuit
    rw [← hEval]
    exact cnfsat_interior_pair_parity c.toBooleanCircuit (by simpa only [hEval] using hDecides)
      i j hEarly (by omega) hOrder
  · by_cases hFar : 5 ≤ j.val - i.val
    · obtain ⟨x, hLeft, hRight, hFixed, hSat⟩ := cnfsat_long_pair_and i j hEarly hLate hFar
      refine ⟨false, false, false, x, hLeft, hRight, hFixed, ?_⟩
      intro a b
      apply Bool.eq_iff_iff.mpr
      exact (hDecides _).trans ((hSat a b).trans (by cases a <;> cases b <;> decide))
    · obtain ⟨x, hLeft, hRight, hFixed, hSat⟩ :=
        cnfsat_close_pair_or i j hEarly (by omega) hOrder (by omega)
      refine ⟨true, true, true, x, hLeft, hRight, hFixed, ?_⟩
      intro a b
      apply Bool.eq_iff_iff.mpr
      exact (hDecides _).trans ((hSat a b).trans (by cases a <;> cases b <;> decide))

private theorem cnfsat_binaryBasis_sensitive (c : BinaryBasisCircuit n) (hLength : 16 ≤ n)
    (hDecides : ∀ x, c.eval x = true ↔ List.ofFn x ∈ CNFSAT) (i : Fin n) :
    ∃ x y, c.eval x ≠ c.eval y ∧ ∀ j, j ≠ i → x j = y j := by
  obtain ⟨x, y, hYes, hNo, hAgree⟩ := cnfsat_all_inputs_sensitive hLength i
  refine ⟨x, y, ?_, hAgree⟩
  intro hSame
  exact hNo ((hDecides y).mp (hSame.symm.trans ((hDecides x).mpr hYes)))

private def basisInteriorWires (n k : Nat) (hSize : k + 44 ≤ n) : Fin k ↪ Fin n where
  toFun i := ⟨i.val + 13, by have hi := i.isLt; omega⟩
  inj' i j h := by
    apply Fin.ext
    have hValue := congrArg Fin.val h
    change i.val + 13 = j.val + 13 at hValue
    omega

/-- The pair certificates add almost one binary gate per interior input. -/
theorem cnfsat_binaryBasis_binarySize_lower (n k : Nat) (hSize : k + 44 ≤ n)
    (c : BinaryBasisCircuit n) (hDecides : ∀ x, c.eval x = true ↔ List.ofFn x ∈ CNFSAT) :
    n + k ≤ c.binarySize + 2 := by
  let coords := basisInteriorWires n k hSize
  apply c.card_le_binarySize_add_two_of_basisPair coords
    (cnfsat_binaryBasis_sensitive c (by omega) hDecides)
  intro i j hNe
  have hi := i.isLt
  have hj := j.isLt
  have hValues : i.val ≠ j.val := fun h ↦ hNe (Fin.ext h)
  by_cases hOrder : i.val < j.val
  · exact cnfsat_binaryBasis_interior_pair c hDecides (coords i) (coords j)
      (by change 13 ≤ i.val + 13; omega)
      (by change j.val + 13 + 32 ≤ n; omega)
      (by change i.val + 13 < j.val + 13; omega)
  · exact (cnfsat_binaryBasis_interior_pair c hDecides (coords j) (coords i)
      (by change 13 ≤ j.val + 13; omega)
      (by change i.val + 13 + 32 ≤ n; omega)
      (by change j.val + 13 < i.val + 13; omega)).swap

/-- Binary CNF-SAT requires at least `2n - 46` binary gates, even with all
two-input Boolean functions available as gates. -/
theorem cnfsat_binaryBasis_binarySize_ge_twice_sub (n : Nat) (c : BinaryBasisCircuit n)
    (hDecides : ∀ x, c.eval x = true ↔ List.ofFn x ∈ CNFSAT) :
    2 * n - 46 ≤ c.binarySize := by
  by_cases hLarge : 44 ≤ n
  · have hCount := cnfsat_binaryBasis_binarySize_lower n (n - 44) (by omega) c hDecides
    omega
  · by_cases hSmall : n ≤ 23
    · omega
    · let empty : Fin 0 ↪ Fin n := ⟨Fin.elim0, fun {i} ↦ i.elim0⟩
      have hCount := c.card_le_binarySize_add_two_of_basisPair empty
        (cnfsat_binaryBasis_sensitive c (by omega) hDecides) (fun i ↦ i.elim0)
      omega

theorem cnfsat_binaryBasis_size_ge_twice_sub (n : Nat) (c : BinaryBasisCircuit n)
    (hDecides : ∀ x, c.eval x = true ↔ List.ofFn x ∈ CNFSAT) :
    2 * n - 46 ≤ c.size :=
  (cnfsat_binaryBasis_binarySize_ge_twice_sub n c hDecides).trans c.topology.binarySize_le_size

end PvsNP.SATCircuitBounds
