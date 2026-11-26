module

public import PvsNP.SAT.PigeonholeEncoding
public import PvsNP.SAT.PigeonholeStrategy
public import PvsNP.SAT.PropagationRefutation

/-! # A lower bound on branching and unit propagation for binary CNF -/

public section

namespace PvsNP.Pigeonhole

open SATBranching

/-- Natural-number names and queries outside the formula preserve the leaf lower bound. -/
theorem encodedFormula_refutation_leaves (n : Nat) {tree : Tree Nat}
    (h : Refutes (encodedFormula n) (fun _ ↦ none) tree) : 2 ^ n ≤ tree.leaves := by
  obtain ⟨t, ht, hSize⟩ := refutation_pullback h
  exact (formula_refutation_leaves n ht).trans hSize

/-- A refutation using decisions and input-clause unit propagations has at least `2^n`
events on the binary pigeonhole instance. -/
theorem encodedFormula_propagation_nodes (n : Nat) {trace : PropagationTree Nat}
    (h : PropagationRefutes (encodedFormula n) (fun _ ↦ none) trace) : 2 ^ n ≤ trace.nodes :=
  (encodedFormula_refutation_leaves n h.toTree).trans trace.leaves_toTree_le_nodes

/-- The lengths of well-formed binary CNF words cannot polynomially bound the sizes of
their shortest decision and input-clause unit-propagation refutations. -/
theorem no_polynomial_bound_for_binary_CNF_propagation_refutations :
    ¬ ∃ bound : Nat → Nat, PolynomiallyBounded bound ∧
      ∀ F : CNF.Formula Nat, CNFCode.encode F ∉ CNFSAT →
        ∃ trace : PropagationTree Nat, PropagationRefutes F (fun _ ↦ none) trace ∧
          trace.nodes ≤ bound (CNFCode.encode F).length := by
  rintro ⟨bound, hBound, hTraces⟩
  apply pow_two_not_polynomiallyBounded
  apply (hBound.comp word_length_polynomiallyBounded).mono
  intro n
  obtain ⟨trace, hRefutes, hSize⟩ := hTraces (encodedFormula n) (word_not_mem_CNFSAT n)
  exact (encodedFormula_propagation_nodes n hRefutes).trans hSize

end PvsNP.Pigeonhole
