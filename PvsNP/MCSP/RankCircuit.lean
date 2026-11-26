module

public import PvsNP.Circuits.BooleanCircuit
public import PvsNP.MCSP.PrefixOrder

/-! # A linear-size comparator for truth-table row ranks -/

public section

namespace PvsNP.MCSP

open Circuits

/-- Decide whether a row precedes `k`, including thresholds outside the table. -/
@[expose] def ltRankCircuit : (n k : Nat) → BooleanCircuit n
  | 0, k => .const 0 (decide (0 < k))
  | n + 1, k =>
    let notHead := (BooleanCircuit.input (0 : Fin (n + 1))).not
    if k ≤ 2 ^ n then
      .binary .and notHead ((ltRankCircuit n k).mapInputs Fin.succ)
    else
      .binary .or notHead ((ltRankCircuit n (k - 2 ^ n)).mapInputs Fin.succ)

@[simp] theorem ltRankCircuit_eval (n k : Nat) (bits : Fin n → Bool) :
    (ltRankCircuit n k).eval bits = decide (rank bits < k) := by
  induction n generalizing k with
  | zero => simp [ltRankCircuit]
  | succ n ih =>
    let tail : Fin n → Bool := bits ∘ Fin.succ
    have hBits : Fin.cases (bits 0) tail = bits := funext fun i ↦
      Fin.cases rfl (fun _ ↦ rfl) i
    have hRank : rank bits = (bits 0).toNat * 2 ^ n + rank tail :=
      hBits ▸ rank_cases (bits 0) tail
    have hTail := rank_lt tail
    by_cases hThreshold : k ≤ 2 ^ n
    · simp only [ltRankCircuit, ite_eq_left hThreshold, BooleanCircuit.eval_binary,
        BooleanCircuit.eval_not, BooleanCircuit.eval_input, BooleanCircuit.eval_mapInputs,
        ih, BinaryOp.eval]
      change (!bits 0 && decide (rank tail < k)) = decide (rank bits < k)
      cases hHead : bits 0
      · simp [hRank, hHead]
      · have hAbove : ¬ 2 ^ n + rank tail < k := by omega
        simp [hRank, hHead, hAbove]
    · simp only [ltRankCircuit, ite_eq_right hThreshold, BooleanCircuit.eval_binary,
        BooleanCircuit.eval_not, BooleanCircuit.eval_input, BooleanCircuit.eval_mapInputs,
        ih, BinaryOp.eval]
      change (!bits 0 || decide (rank tail < k - 2 ^ n)) = decide (rank bits < k)
      cases hHead : bits 0
      · have hBelow : rank tail < k := by omega
        simp [hRank, hHead, hBelow]
      · have hShift : rank tail < k - 2 ^ n ↔ 2 ^ n + rank tail < k := by omega
        simp [hRank, hHead, hShift]

@[simp] theorem ltRankCircuit_size (n k : Nat) : (ltRankCircuit n k).size = 2 * n + 1 := by
  induction n generalizing k with
  | zero => simp [ltRankCircuit]
  | succ n ih =>
    rw [ltRankCircuit]
    split <;> simp only [BooleanCircuit.size_binary, BooleanCircuit.size_not,
      BooleanCircuit.size_input, BooleanCircuit.size_mapInputs, ih] <;> omega

end PvsNP.MCSP
