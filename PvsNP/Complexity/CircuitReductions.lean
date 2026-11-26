module

public import PvsNP.Circuits.TransducerOutput
public import PvsNP.Complexity.BufferedCircuits

import Mathlib.Data.Fintype.EquivFin
import PvsNP.TuringMachine.OutputBound

/-! # Polynomial-time reductions preserve polynomial circuit bounds -/

public section

namespace PvsNP

open Circuits

/-- A polynomial-time map has polynomial-size circuits for its data and length wires. -/
theorem PolynomialTimeMap.exists_bufferCircuits {f : BinaryWord → BinaryWord}
    (hf : PolynomialTimeMap f) :
    ∃ B : Nat → Nat, PolynomiallyBounded B ∧
      ∃ circuit : (n : Nat) → MultiCircuit n (B n + B n),
        PolynomiallyBounded (fun n ↦ (circuit n).size) ∧
        ∀ n (x : Fin n → Bool), (f (List.ofFn x)).length ≤ B n ∧
          (circuit n).eval x = wordBuffer (B n) (f (List.ofFn x)) := by
  classical
  obtain ⟨M, ⟨k, hTime⟩, hComputes⟩ := hf
  let _ : Finite M.State := M.stateFinite
  let _ : Finite M.Symbol := M.symbolFinite
  let _ : Fintype M.State := Fintype.ofFinite _
  let _ : Fintype M.Symbol := Fintype.ofFinite _
  let clock (n : Nat) := n ^ k + k
  let B (n : Nat) := n + 2 * clock n
  let circuit (n : Nat) := (machineOutputLayered M n (clock n) (B n)).toMultiCircuit
  have hClock : PolynomiallyBounded clock :=
    (PolynomiallyBounded.id.pow k).add (PolynomiallyBounded.const k)
  have hB : PolynomiallyBounded B :=
    PolynomiallyBounded.id.add ((PolynomiallyBounded.const 2).mul hClock)
  have hSize := machineOutputLayered_size_polynomiallyBounded M hClock hB
  refine ⟨B, hB, circuit, hSize.mono (fun n ↦ Layered.size_toMultiCircuit_le _), ?_⟩
  intro n x
  let word : BinaryWord := List.ofFn x
  obtain ⟨u, hOutput⟩ := hComputes word
  have hHalt : M.HaltsWithin word (clock n) := by
    simpa only [word, List.length_ofFn, clock] using hTime word
  have hAtClock := M.outputsAt_at_bound hHalt hOutput
  constructor
  · simpa only [B, word, List.length_ofFn] using M.output_length_le word (f word) _ hAtClock.2
  · change ((machineOutputLayered M n (clock n) (B n)).toMultiCircuit).eval x = _
    rw [Layered.eval_toMultiCircuit]
    exact machineOutputLayered_eval M n (clock n) (B n) x (f word) hAtClock

/-- P/poly is closed under taking a preimage by a polynomial-time Cook transducer. -/
theorem PolynomialTimeMap.preimage_mem_PPoly {f : BinaryWord → BinaryWord}
    {K : BinaryLanguage} (hf : PolynomialTimeMap f) (hK : K ∈ PPoly) :
    {word | f word ∈ K} ∈ PPoly := by
  obtain ⟨B, hB, output, hOutputSize, hOutput⟩ := hf.exists_bufferCircuits
  obtain ⟨decider, hDecideSize, hDecide⟩ := mem_PPoly_iff_bufferCircuits.mp hK
  let circuit (n : Nat) := (output n).thenBoolean (decider (B n))
  refine ⟨circuit, ?_, ?_⟩
  · simpa only [circuit, MultiCircuit.size_thenBoolean] using hOutputSize.add (hDecideSize.comp hB)
  · intro n x
    have h := hOutput n x
    change (circuit n).eval x = true ↔ f (List.ofFn x) ∈ K
    simp only [circuit, MultiCircuit.eval_thenBoolean, h.2]
    exact hDecide (B n) _ h.1

/-- Polynomial-time many-one reductions transfer polynomial-size circuit families. -/
theorem PolynomiallyReducesTo.mem_PPoly {L K : BinaryLanguage}
    (h : PolynomiallyReducesTo L K) (hK : K ∈ PPoly) : L ∈ PPoly := by
  obtain ⟨f, hf, hMem⟩ := h
  have hEq : L = {word | f word ∈ K} := Set.ext hMem
  exact hEq.symm ▸ hf.preimage_mem_PPoly hK

theorem NPComplete.mem_PPoly_iff_np_subset {K : BinaryLanguage} (hK : NPComplete K) :
    K ∈ PPoly ↔ NP ⊆ PPoly :=
  ⟨fun h _ hL ↦ (hK.2 _ hL).mem_PPoly h, fun h ↦ h hK.1⟩

/-- Binary CNF-SAT has polynomial-size circuits exactly when every NP language does. -/
theorem CNFSAT_mem_PPoly_iff_np_subset : CNFSAT ∈ PPoly ↔ NP ⊆ PPoly :=
  SATAssignment.npComplete_CNFSAT.mem_PPoly_iff_np_subset

/-- Any NP language with superpolynomial circuit requirements forces the same for binary CNF. -/
theorem CNFSAT_not_mem_PPoly_of_mem_NP {L : BinaryLanguage}
    (hNP : L ∈ NP) (hLower : L ∉ PPoly) : CNFSAT ∉ PPoly := by
  intro hSat
  exact hLower (CNFSAT_mem_PPoly_iff_np_subset.mp hSat hNP)

end PvsNP
