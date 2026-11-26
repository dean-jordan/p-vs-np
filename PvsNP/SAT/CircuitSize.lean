module

public import PvsNP.Circuits.InputSupport
public import PvsNP.SAT.CircuitProjection
public import PvsNP.SAT.CircuitSensitivity
public import PvsNP.SAT.CircuitSuffixSensitivity

/-! # Linear size lower bounds for general binary CNF-SAT circuits -/

public section

namespace PvsNP.SATCircuitBounds

open Circuits

private def signWires (n : Nat) : Fin n ↪ Fin (5 * n + 6) where
  toFun i := ⟨5 * i.val + 7, by have hi := i.isLt; omega⟩
  inj' i j h := by
    apply Fin.ext
    have hv := congrArg Fin.val h
    change 5 * i.val + 7 = 5 * j.val + 7 at hv
    omega

/-- From length 16 onward, each input bit can change the binary CNF-SAT answer by itself. -/
theorem cnfsat_all_inputs_sensitive {n : Nat} (hSize : 16 ≤ n) (i : Fin n) :
    ∃ x y : Fin n → Bool, List.ofFn x ∈ CNFSAT ∧ List.ofFn y ∉ CNFSAT ∧
      ∀ j : Fin n, j ≠ i → x j = y j := by
  by_cases hEarly : i.val < 5
  · by_cases hFirst : i.val = 0
    · exact first_sensitive i (by omega) hFirst
    by_cases hSign : i.val = 2
    · exact end_sign_sensitive i hSize (Or.inl hSign)
    exact early_markers_sensitive i hSize (by omega)
  · by_cases hInterior : i.val + 6 ≤ n
    · exact interior_sensitive i (by omega) hInterior
    by_cases hLast : n ≤ i.val + 3
    · exact last_three_sensitive i (by omega) hLast
    by_cases hSign : i.val + 4 = n
    · exact end_sign_sensitive i hSize (Or.inr hSign)
    exact last_literal_marker_sensitive i hSize (by omega)

/-- Every binary CNF-SAT circuit on `n ≥ 16` inputs needs at least `n - 1` binary gates. -/
theorem cnfsat_binarySize_ge (n : Nat) (hSize : 16 ≤ n) (c : BooleanCircuit n)
    (hDecides : ∀ x : Fin n → Bool, c.eval x = true ↔ List.ofFn x ∈ CNFSAT) :
    n - 1 ≤ c.binarySize := by
  have hCount := c.card_le_binarySize_add_one_of_sensitive (Function.Embedding.refl (Fin n)) (by
    intro i
    obtain ⟨x, y, hYes, hNo, hAgree⟩ := cnfsat_all_inputs_sensitive hSize i
    refine ⟨x, y, ?_, hAgree⟩
    intro hEqual
    exact hNo ((hDecides y).mp (hEqual.symm.trans ((hDecides x).mpr hYes))))
  omega

/-- Correct binary CNF-SAT circuits of length `n ≥ 6` need a NOT gate. -/
theorem cnfsat_negationSize_pos (n : Nat) (hSize : 6 ≤ n) (c : BooleanCircuit n)
    (hDecides : ∀ x : Fin n → Bool, c.eval x = true ↔ List.ofFn x ∈ CNFSAT) :
    0 < c.network.negationSize := by
  apply Nat.pos_of_ne_zero
  intro hZero
  let i : Fin n := ⟨n - 1, by omega⟩
  have hLast : n ≤ i.val + 3 := by simp only [i]; omega
  obtain ⟨x, y, hYes, hNo, _, hMono⟩ := last_three_sensitive_monotone i hSize hLast
  apply hNo
  apply (hDecides y).mp
  exact c.network.eval_mono_of_negationSize_zero hZero x y hMono c.output
    ((hDecides x).mpr hYes)

/-- Every correct circuit on `n ≥ 16` input bits uses at least `n` gates. -/
theorem cnfsat_size_ge (n : Nat) (hSize : 16 ≤ n) (c : BooleanCircuit n)
    (hDecides : ∀ x : Fin n → Bool, c.eval x = true ↔ List.ofFn x ∈ CNFSAT) : n ≤ c.size := by
  have hBinary := cnfsat_binarySize_ge n hSize c hDecides
  have hNeg := cnfsat_negationSize_pos n (by omega) c hDecides
  have hTotal : c.binarySize + c.network.negationSize ≤ c.size :=
    c.network.binarySize_add_negationSize_le_size
  omega

/-- Even on well-formed formulas alone, `5 * n + 6` inputs require at least `n - 1` binary gates. -/
theorem cnfsat_binarySize_ge_on_valid_encodings (n : Nat) (c : BooleanCircuit (5 * n + 6))
    (hDecides : ∀ x : Fin (5 * n + 6) → Bool,
      (∃ F, CNFCode.decode (List.ofFn x) = some F) →
      (c.eval x = true ↔ List.ofFn x ∈ CNFSAT)) : n - 1 ≤ c.binarySize := by
  have hCount := c.card_le_binarySize_add_one_of_sensitive (signWires n) (by
    intro i
    obtain ⟨x, y, hx, hy, hYes, hNo, hAgree⟩ := valid_sign_sensitive n i
    refine ⟨x, y, ?_, fun j hj ↦ hAgree j (fun he ↦ hj (Fin.ext he))⟩
    intro hEqual
    exact hNo ((hDecides y hy).mp (hEqual.symm.trans ((hDecides x hx).mpr hYes))))
  omega

/-- The fixed-degree lower-bound obligation for degree zero holds for binary CNF-SAT. -/
theorem cnfsat_exceeds_constant_size (C : Nat) :
    ∃ n, ∀ c : BooleanCircuit n,
      (∀ x : Fin n → Bool, c.eval x = true ↔ List.ofFn x ∈ CNFSAT) → C < c.size := by
  refine ⟨C + 16, fun c hDecides ↦ ?_⟩
  have h := cnfsat_size_ge (C + 16) (by omega) c hDecides
  omega

end PvsNP.SATCircuitBounds
