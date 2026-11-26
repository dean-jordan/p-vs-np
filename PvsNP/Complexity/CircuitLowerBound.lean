module

public import PvsNP.Circuits.BooleanCircuit
public import PvsNP.Circuits.WindowSimulation
public import PvsNP.SAT.Completeness

import Mathlib.Data.Fintype.EquivFin

/-! # Polynomial-size circuits and a sufficient condition for Cook separation -/

@[expose] public section

namespace PvsNP

open Circuits

/-- The nonuniform class P/poly. Each input length has its own bounded-fan-in Boolean circuit. -/
def PPoly : Set BinaryLanguage :=
  {L | ∃ circuit : (n : Nat) → BooleanCircuit n,
    PolynomiallyBounded (fun n ↦ (circuit n).size) ∧
    ∀ n (x : Fin n → Bool), (circuit n).eval x = true ↔ List.ofFn x ∈ L}

/-- Every total polynomial-time Cook machine has a polynomial-size circuit family. -/
theorem Machine.exists_polynomialSize_circuits (M : Machine Bool) (h : M.PolyTime) :
    ∃ circuit : (n : Nat) → BooleanCircuit n,
      PolynomiallyBounded (fun n ↦ (circuit n).size) ∧
      ∀ n (x : Fin n → Bool), (circuit n).eval x = true ↔ M.Accepts (List.ofFn x) := by
  classical
  let _ : Finite M.State := M.stateFinite
  let _ : Finite M.Symbol := M.symbolFinite
  let _ : Fintype M.State := Fintype.ofFinite _
  let _ : Fintype M.Symbol := Fintype.ofFinite _
  obtain ⟨k, hTime⟩ := h
  let clock (n : Nat) := n ^ k + k
  have hClock : PolynomiallyBounded clock :=
    (PolynomiallyBounded.id.pow k).add (PolynomiallyBounded.const k)
  let circuit (n : Nat) := (machineLayered M n (clock n)).toBooleanCircuit 0
  refine ⟨circuit, (machineLayered_size_polynomiallyBounded M hClock).mono ?_, ?_⟩
  · intro n
    exact Layered.size_toBooleanCircuit_le _ _
  · intro n x
    have hHalt : M.HaltsWithin (List.ofFn x) (clock n) := by
      simpa only [List.length_ofFn, clock] using hTime (List.ofFn x)
    change ((machineLayered M n (clock n)).toBooleanCircuit 0).eval x = true ↔
      M.Accepts (List.ofFn x)
    rw [Layered.eval_toBooleanCircuit, machineLayered_eval]
    exact (M.accepts_iff_at_bound _ hHalt).symm

theorem P_subset_PPoly : P ⊆ PPoly := by
  rintro L ⟨M, hTime, hDecision⟩
  obtain ⟨circuit, hSize, hCircuit⟩ := M.exists_polynomialSize_circuits hTime
  exact ⟨circuit, hSize, fun n x ↦ (hCircuit n x).trans (hDecision (List.ofFn x)).symm⟩

/-- Failure of polynomial-size circuit families can be witnessed one polynomial at a time. -/
theorem not_mem_PPoly_iff (L : BinaryLanguage) : L ∉ PPoly ↔
    ∀ C d : Nat, ∃ n, ∀ circuit : BooleanCircuit n,
      (∀ x : Fin n → Bool, circuit.eval x = true ↔ List.ofFn x ∈ L) →
        C * (n + 1) ^ d < circuit.size := by
  classical
  constructor
  · intro h C d
    by_contra! hLocal
    choose circuit hCorrect hSize using hLocal
    exact h ⟨circuit, ⟨C, d, hSize⟩, hCorrect⟩
  · rintro h ⟨circuit, ⟨C, d, hSize⟩, hCorrect⟩
    obtain ⟨n, hLarge⟩ := h C d
    exact Nat.not_lt_of_ge (hSize n) (hLarge (circuit n) (hCorrect n))

/-- A superpolynomial circuit lower bound for binary CNF satisfiability would separate Cook's
classes. -/
theorem p_ne_np_of_CNFSAT_not_mem_PPoly (h : CNFSAT ∉ PPoly) : P ≠ NP := by
  intro hEq
  exact h (P_subset_PPoly (SATAssignment.p_eq_np_iff_CNFSAT_mem_P_verified.mp hEq))

end PvsNP
