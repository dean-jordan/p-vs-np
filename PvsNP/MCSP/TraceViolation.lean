module

public import PvsNP.Circuits.WireTrace
public import PvsNP.MCSP.MergeViolation

/-! # A merge violation from a row and two wire traces -/

public section

namespace PvsNP.MCSP

open Circuits

variable {n : Nat}

theorem fieldValue_append_bit (word : BinaryWord) (bit : Bool) :
    fieldValue (word ++ [bit]) = fieldValue word + 2 ^ word.length * bit.toNat := by
  induction word with
  | nil => simp [fieldValue]
  | cons b tail ih =>
    simp only [List.cons_append, fieldValue, List.length_cons, ih, Nat.mul_add, Nat.pow_succ,
      Nat.mul_assoc]
    rw [Nat.mul_left_comm 2 (2 ^ tail.length)]
    omega

theorem fieldValue_reverse_row (x : Fin n → Bool) : fieldValue (List.ofFn x).reverse = rank x := by
  induction n with
  | zero => simp [fieldValue]
  | succ n ih =>
    let tail : Fin n → Bool := fun i ↦ x i.succ
    have hBits : Fin.cases (x 0) tail = x := funext fun i ↦
      Fin.cases rfl (fun _ ↦ rfl) i
    have hRank : rank x = (x 0).toNat * 2 ^ n + rank tail :=
      hBits ▸ rank_cases (x 0) tail
    rw [List.ofFn_succ, List.reverse_cons, fieldValue_append_bit, List.length_reverse,
      List.length_ofFn, ih, hRank]
    rw [Nat.mul_comm (2 ^ n) ((x 0).toNat), Nat.add_comm]

/-- A row in the `n + 1` bit format used for the request counter. -/
@[expose] def mergeRowField (x : Fin n → Bool) : BinaryWord := (List.ofFn x).reverse ++ [false]

@[simp] theorem length_mergeRowField (x : Fin n → Bool) : (mergeRowField x).length = n + 1 := by
  simp [mergeRowField]

theorem compare_mergeRowField (x : Fin n → Bool) {seen : Nat} (hSeen : seen ≤ 2 ^ n) :
    compare (fieldValue (mergeRowField x)) (fieldValue (fieldBits (n + 1) seen)) =
      compare (rank x) seen := by
  have hFit : seen < 2 ^ (n + 1) := by
    rw [Nat.pow_succ]
    have hPos := Nat.two_pow_pos n
    omega
  simp [mergeRowField, fieldValue_append_bit, fieldValue_reverse_row, fieldValue_bits _ _ hFit]

/-- Check both evaluation traces and compare their output bits on a constrained row. -/
@[expose] def checkMergeTraceViolation (old : BooleanCircuit n) (seen : Nat) (bit : Bool)
    (candidate : BooleanCircuit n) (x : Fin n → Bool) (oldTrace newTrace : BinaryWord)
    (oldValue newValue : Bool) : Bool :=
  old.checkWireTrace x oldTrace oldValue && candidate.checkWireTrace x newTrace newValue &&
    ((decide (rank x < seen) && (newValue != oldValue)) ||
      (decide (rank x = seen) && (newValue != bit)))

/-- A genuine violation has a certificate with exactly one bit per wire in each circuit. -/
theorem exists_checkMergeTraceViolation_iff (old : BooleanCircuit n) (seen : Nat) (bit : Bool)
    (candidate : BooleanCircuit n) (x : Fin n → Bool) :
    (∃ (oldTrace newTrace : BinaryWord) (oldValue newValue : Bool),
      oldTrace.length + newTrace.length = 2 * n + old.size + candidate.size ∧
      checkMergeTraceViolation old seen bit candidate x oldTrace newTrace oldValue newValue =
        true) ↔
      (mergeViolationCircuit old seen bit candidate).eval x = true := by
  rw [mergeViolationCircuit_eval_eq_true_iff]
  simp only [checkMergeTraceViolation, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne,
    decide_eq_true_eq, BooleanCircuit.checkWireTrace_eq_true_iff]
  constructor
  · rintro ⟨u, v, a, b, _, ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩, h⟩
    exact h
  · intro h
    refine ⟨old.wireTrace x, candidate.wireTrace x, old.eval x, candidate.eval x,
      ?_, ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩, h⟩
    simp only [BooleanCircuit.length_wireTrace]
    omega

end PvsNP.MCSP
