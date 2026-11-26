module

public import PvsNP.Circuits.NegationLowerBound
public import PvsNP.SAT.CircuitNegationWitness
public import PvsNP.SAT.CircuitSize

import Mathlib.Data.Fintype.Card

/-! # A growing additive term in the gate lower bound for binary CNF-SAT -/

public section

namespace PvsNP.SATCircuitBounds

open Circuits

private def evenSteps (k : Nat) : Fin k ↪ Fin (2 * k) where
  toFun i := ⟨2 * i.val, by have hi := i.isLt; omega⟩
  inj' i j h := by
    apply Fin.ext
    have hVal := congrArg Fin.val h
    change 2 * i.val = 2 * j.val at hVal
    omega

/-- The clause signs force `k` decreases on a chain of increasing inputs. -/
theorem cnfsat_pairChain_negationSize_lower (n k : Nat) (hSize : 9 * k + 17 ≤ n)
    (c : BooleanCircuit n)
    (hDecides : ∀ x, c.eval x = true ↔ List.ofFn x ∈ CNFSAT) :
    k + 1 ≤ 2 ^ c.network.negationSize := by
  let output (i : Fin (2 * k + 1)) := c.eval (pairChain n k hSize i)
  have hSubset : (Finset.univ : Finset (Fin k)).map (evenSteps k) ⊆ fallSteps output := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
    rw [mem_fallSteps]
    constructor
    · apply (hDecides _).mpr
      apply (pairChain_mem_iff n k hSize _).mpr
      change (2 * j.val) % 2 = 0
      omega
    · apply Bool.eq_false_iff.mpr
      intro hAccept
      have hOdd := (pairChain_mem_iff n k hSize _).mp ((hDecides _).mp hAccept)
      change (2 * j.val + 1) % 2 = 0 at hOdd
      omega
  have hFalls : k ≤ (fallSteps output).card := by
    simpa only [Finset.card_map, Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card hSubset
  exact (Nat.add_le_add_right hFalls 1).trans
    (c.falls_add_one_le_pow_negationSize (pairChain n k hSize) (pairChain_monotone n k hSize))

/-- The NOT gates from the chain bound add to the binary gates from input sensitivity. -/
theorem cnfsat_size_ge_add (n extra : Nat) (hSize : 9 * 2 ^ extra + 17 ≤ n)
    (c : BooleanCircuit n)
    (hDecides : ∀ x, c.eval x = true ↔ List.ofFn x ∈ CNFSAT) :
    n + extra ≤ c.size := by
  have hBinary := cnfsat_binarySize_ge n (by omega) c hDecides
  have hDrops := cnfsat_pairChain_negationSize_lower n (2 ^ extra) hSize c hDecides
  have hNeg : extra < c.network.negationSize := by
    by_contra! h
    have hPow : 2 ^ c.network.negationSize ≤ 2 ^ extra := Nat.pow_le_pow_right (by decide) h
    omega
  have hCount : c.binarySize + c.network.negationSize ≤ c.size :=
    c.network.binarySize_add_negationSize_le_size
  omega

/-- At some input length, every CNF-SAT circuit exceeds the length by any prescribed amount. -/
theorem cnfsat_circuit_size_unbounded_additive (extra : Nat) :
    ∃ n, 16 ≤ n ∧ ∀ c : BooleanCircuit n,
      (∀ x, c.eval x = true ↔ List.ofFn x ∈ CNFSAT) → n + extra ≤ c.size := by
  let n := 9 * 2 ^ extra + 17
  have hSize : 16 ≤ n := by simp only [n]; omega
  exact ⟨n, hSize, cnfsat_size_ge_add n extra (Nat.le_refl _)⟩

end PvsNP.SATCircuitBounds
