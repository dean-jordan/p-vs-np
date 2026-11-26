module

public import PvsNP.Circuits.ParityBinaryLowerBound
public import PvsNP.SAT.CircuitCloseParity
public import PvsNP.SAT.CircuitNegationSize
public import PvsNP.SAT.CircuitParityRestriction

/-! # Gate lower bounds from parity on interior CNF-SAT bits -/

public section

namespace PvsNP.SATCircuitBounds

open Circuits

private def parityInteriorWires (n k : Nat) (hSize : k + 43 ≤ n) : Fin k ↪ Fin n where
  toFun i := ⟨i.val + 13, by have hi := i.isLt; omega⟩
  inj' i j h := by
    apply Fin.ext
    have hVal := congrArg Fin.val h
    change i.val + 13 = j.val + 13 at hVal
    omega

/-- Any two sufficiently interior positions have a parity restriction.
Close pairs use a change in how the CNF parser groups literals. -/
theorem cnfsat_interior_pair_parity (c : BooleanCircuit n)
    (hDecides : ∀ x, c.eval x = true ↔ List.ofFn x ∈ CNFSAT) (i j : Fin n)
    (hEarly : 13 ≤ i.val) (hLate : j.val + 30 ≤ n) (hOrder : i.val < j.val) :
    ParityRestriction c.eval i j := by
  by_cases hFar : 5 ≤ j.val - i.val
  · obtain ⟨x, hLeft, hRight, hFixed, hSat⟩ := cnfsat_long_pair_xnor i j hEarly (by omega) hFar
    refine ⟨true, x, hLeft, hRight, hFixed, fun a b ↦ Bool.eq_iff_iff.mpr ?_⟩
    exact (hDecides _).trans ((hSat a b).trans (by cases a <;> cases b <;> decide))
  · obtain ⟨x, hLeft, hRight, hFixed, hSat⟩ :=
      cnfsat_close_pair_xor i j hEarly hLate hOrder (by omega)
    refine ⟨false, x, hLeft, hRight, hFixed, fun a b ↦ Bool.eq_iff_iff.mpr ?_⟩
    exact (hDecides _).trans ((hSat a b).trans (by cases a <;> cases b <;> decide))

/-- Input relevance and pairwise parity on `k` interior coordinates
together force `n + k - 2` binary gates. -/
theorem cnfsat_parity_binarySize_lower (n k : Nat) (hSize : k + 43 ≤ n)
    (c : BooleanCircuit n) (hDecides : ∀ x, c.eval x = true ↔ List.ofFn x ∈ CNFSAT) :
    n + k ≤ c.binarySize + 2 := by
  let coords := parityInteriorWires n k hSize
  apply c.card_le_binarySize_add_two_of_parity coords
  · intro i
    obtain ⟨x, y, hYes, hNo, hAgree⟩ := cnfsat_all_inputs_sensitive (by omega) i
    refine ⟨x, y, ?_, hAgree⟩
    intro hSame
    exact hNo ((hDecides y).mp (hSame.symm.trans ((hDecides x).mpr hYes)))
  · intro i j hNe
    have hi := i.isLt
    have hj := j.isLt
    have hVal : i.val ≠ j.val := fun h ↦ hNe (Fin.ext h)
    by_cases hOrder : i.val < j.val
    · exact cnfsat_interior_pair_parity c hDecides (coords i) (coords j)
        (by change 13 ≤ i.val + 13; omega)
        (by change j.val + 13 + 30 ≤ n; omega)
        (by change i.val + 13 < j.val + 13; omega)
    · exact (cnfsat_interior_pair_parity c hDecides (coords j) (coords i)
        (by change 13 ≤ j.val + 13; omega)
        (by change i.val + 13 + 30 ≤ n; omega)
        (by change j.val + 13 < i.val + 13; omega)).swap

/-- Correct circuits also require a NOT gate. -/
theorem cnfsat_parity_size_lower (n k : Nat) (hSize : k + 43 ≤ n)
    (c : BooleanCircuit n) (hDecides : ∀ x, c.eval x = true ↔ List.ofFn x ∈ CNFSAT) :
    n + k ≤ c.size + 1 := by
  have hBinary := cnfsat_parity_binarySize_lower n k hSize c hDecides
  have hNeg := cnfsat_negationSize_pos n (by omega) c hDecides
  have hTotal : c.binarySize + c.network.negationSize ≤ c.size :=
    c.network.binarySize_add_negationSize_le_size
  omega

/-- Every correct binary CNF-SAT circuit has at least twice the input
length minus forty-four gates. -/
theorem cnfsat_size_ge_twice_sub (n : Nat) (c : BooleanCircuit n)
    (hDecides : ∀ x, c.eval x = true ↔ List.ofFn x ∈ CNFSAT) :
    2 * n - 44 ≤ c.size := by
  by_cases hLarge : 43 ≤ n
  · have hBound := cnfsat_parity_size_lower n (n - 43) (by omega) c hDecides
    omega
  · by_cases hSmall : n ≤ 22
    · omega
    · have hBound := cnfsat_size_ge n (by omega) c hDecides
      omega

/-- The monotone-chain lower bound on NOT gates combines with the
parity restriction bound on binary gates. -/
theorem cnfsat_parity_size_ge_add (n k extra : Nat) (hSize : k + 43 ≤ n)
    (hNegSize : 9 * 2 ^ extra + 17 ≤ n) (c : BooleanCircuit n)
    (hDecides : ∀ x, c.eval x = true ↔ List.ofFn x ∈ CNFSAT) :
    n + k + extra ≤ c.size + 1 := by
  have hBinary := cnfsat_parity_binarySize_lower n k hSize c hDecides
  have hDrops := cnfsat_pairChain_negationSize_lower n (2 ^ extra) hNegSize c hDecides
  have hNeg : extra < c.network.negationSize := by
    by_contra! h
    have hPow : 2 ^ c.network.negationSize ≤ 2 ^ extra := Nat.pow_le_pow_right (by decide) h
    omega
  have hTotal : c.binarySize + c.network.negationSize ≤ c.size :=
    c.network.binarySize_add_negationSize_le_size
  omega

theorem cnfsat_size_ge_twice_add_sub (n extra : Nat) (hInterior : 43 ≤ n)
    (hNegSize : 9 * 2 ^ extra + 17 ≤ n) (c : BooleanCircuit n)
    (hDecides : ∀ x, c.eval x = true ↔ List.ofFn x ∈ CNFSAT) :
    2 * n + extra - 44 ≤ c.size := by
  have hBound := cnfsat_parity_size_ge_add n (n - 43) extra (by omega) hNegSize c hDecides
  omega

end PvsNP.SATCircuitBounds
