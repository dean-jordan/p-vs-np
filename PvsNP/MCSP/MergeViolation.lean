module

public import PvsNP.MCSP.RankCircuit
public import PvsNP.MCSP.StreamMerge

/-! # A circuit for a failed one-bit merge -/

public section

namespace PvsNP.MCSP

open Circuits

variable {n : Nat}

/-- Accept exactly those rows where the proposed circuit violates the merge. -/
def mergeViolationCircuit (old : BooleanCircuit n) (seen : Nat) (bit : Bool)
    (candidate : BooleanCircuit n) : BooleanCircuit n :=
  let past := ltRankCircuit n seen
  let throughNext := ltRankCircuit n (seen + 1)
  let wrongPast := BooleanCircuit.binary .and
    (BooleanCircuit.binary .or candidate old)
    (BooleanCircuit.binary .and candidate old).not
  let wrongNext := if bit then candidate.not else candidate
  BooleanCircuit.binary .or
    (BooleanCircuit.binary .and past wrongPast)
    (BooleanCircuit.binary .and (BooleanCircuit.binary .and past.not throughNext) wrongNext)

theorem mergeViolationCircuit_size_le (old : BooleanCircuit n) (seen : Nat) (bit : Bool)
    (candidate : BooleanCircuit n) :
    (mergeViolationCircuit old seen bit candidate).size ≤ 2 * old.size + 3 * candidate.size +
      6 * n + 13 := by
  cases bit <;> simp [mergeViolationCircuit] <;> omega

theorem mergeViolationCircuit_eval_eq_true_iff (old : BooleanCircuit n) (seen : Nat) (bit : Bool)
    (candidate : BooleanCircuit n) (x : Fin n → Bool) :
    (mergeViolationCircuit old seen bit candidate).eval x = true ↔
      (rank x < seen ∧ candidate.eval x ≠ old.eval x) ∨
      (rank x = seen ∧ candidate.eval x ≠ bit) := by
  have hNext : (!(decide (rank x < seen)) && decide (rank x < seen + 1)) =
      decide (rank x = seen) := by
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
    omega
  simp only [mergeViolationCircuit, BooleanCircuit.eval_binary, BooleanCircuit.eval_not,
    BinaryOp.eval, ltRankCircuit_eval, hNext]
  cases bit <;> cases old.eval x <;> cases hc : candidate.eval x <;> simp [hc]

/-- The proposed merge succeeds exactly when the violation circuit rejects every row. -/
theorem mergeAgrees_iff_forall_mergeViolationCircuit_eq_false (old : BooleanCircuit n)
    (seen : Nat) (bit : Bool) (candidate : BooleanCircuit n) :
    MergeAgrees old seen bit candidate ↔
      ∀ x, (mergeViolationCircuit old seen bit candidate).eval x = false := by
  constructor
  · rintro ⟨hPast, hNext⟩ x
    apply Bool.eq_false_iff.mpr
    intro hTrue
    rcases (mergeViolationCircuit_eval_eq_true_iff old seen bit candidate x).mp hTrue with
      ⟨hRow, hWrong⟩ | ⟨hRow, hWrong⟩
    · exact hWrong (hPast x hRow)
    · exact hWrong (hNext x hRow)
  · intro h
    constructor <;> intro x hRow <;> by_contra hWrong
    · have hTrue := (mergeViolationCircuit_eval_eq_true_iff old seen bit candidate x).mpr
        (.inl ⟨hRow, hWrong⟩)
      exact Bool.noConfusion ((h x).symm.trans hTrue)
    · have hTrue := (mergeViolationCircuit_eval_eq_true_iff old seen bit candidate x).mpr
        (.inr ⟨hRow, hWrong⟩)
      exact Bool.noConfusion ((h x).symm.trans hTrue)

end PvsNP.MCSP
