module

public import PvsNP.Circuits.ToCNF
public import PvsNP.MCSP.MergeViolation

/-! # A CNF check for disagreement in a proposed merge -/

public section

namespace PvsNP.MCSP

open Circuits

variable {n : Nat}

/-- A satisfying assignment encodes a row on which the merge fails. -/
@[expose] def mergeViolationCNF (old : BooleanCircuit n) (seen : Nat) (bit : Bool)
    (candidate : BooleanCircuit n) : CNF.Formula Nat :=
  (mergeViolationCircuit old seen bit candidate).toCNF

theorem satisfiable_mergeViolationCNF_iff (old : BooleanCircuit n) (seen : Nat) (bit : Bool)
    (candidate : BooleanCircuit n) :
    CNF.Satisfiable (mergeViolationCNF old seen bit candidate) ↔
      ∃ x : Fin n → Bool, (rank x < seen ∧ candidate.eval x ≠ old.eval x) ∨
        (rank x = seen ∧ candidate.eval x ≠ bit) := by
  simp only [mergeViolationCNF, BooleanCircuit.satisfiable_toCNF_iff,
    mergeViolationCircuit_eval_eq_true_iff]

theorem mergeAgrees_iff_not_satisfiable_mergeViolationCNF (old : BooleanCircuit n)
    (seen : Nat) (bit : Bool) (candidate : BooleanCircuit n) :
    MergeAgrees old seen bit candidate ↔
      ¬ CNF.Satisfiable (mergeViolationCNF old seen bit candidate) := by
  rw [mergeAgrees_iff_forall_mergeViolationCircuit_eq_false, mergeViolationCNF,
    BooleanCircuit.satisfiable_toCNF_iff]
  simp only [not_exists, Bool.eq_false_iff]

theorem mergeViolationCNF_size_le (old : BooleanCircuit n) (seen : Nat) (bit : Bool)
    (candidate : BooleanCircuit n) :
    CNF.size (mergeViolationCNF old seen bit candidate) ≤
      10 * (2 * old.size + 3 * candidate.size + 6 * n + 13) + 2 :=
  ((mergeViolationCircuit old seen bit candidate).size_toCNF_le).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 10
      (mergeViolationCircuit_size_le old seen bit candidate)) 2)

/-- The binary CNF word for a proposed merge violation. -/
@[expose] def mergeViolationWord (old : BooleanCircuit n) (seen : Nat) (bit : Bool)
    (candidate : BooleanCircuit n) : BinaryWord :=
  CNFCode.encode (mergeViolationCNF old seen bit candidate)

theorem mergeAgrees_iff_mergeViolationWord_not_mem_CNFSAT (old : BooleanCircuit n)
    (seen : Nat) (bit : Bool) (candidate : BooleanCircuit n) :
    MergeAgrees old seen bit candidate ↔ mergeViolationWord old seen bit candidate ∉ CNFSAT :=
  (mergeAgrees_iff_not_satisfiable_mergeViolationCNF old seen bit candidate).trans
    (not_congr (encode_mem_CNFSAT_iff _).symm)

theorem mergeViolationWord_length_le (old : BooleanCircuit n) (seen : Nat) (bit : Bool)
    (candidate : BooleanCircuit n) :
    let s := 2 * old.size + 3 * candidate.size + 6 * n + 13
    (mergeViolationWord old seen bit candidate).length ≤ 1 + (n + s + 3) * (10 * s + 2) := by
  let circuit := mergeViolationCircuit old seen bit candidate
  have hSize := mergeViolationCircuit_size_le old seen bit candidate
  apply circuit.encode_toCNF_length_le.trans
  exact Nat.add_le_add_left (Nat.mul_le_mul
    (Nat.add_le_add_right (Nat.add_le_add_left hSize n) 3)
    (Nat.add_le_add_right (Nat.mul_le_mul_left 10 hSize) 2)) 1

end PvsNP.MCSP
