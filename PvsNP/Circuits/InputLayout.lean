module

public import PvsNP.Circuits.BooleanCircuit

/-! # Circuits that read a prefix of a larger input -/

public section

namespace PvsNP.Circuits

variable {n N : Nat}

/-- Extend the input by false bits after its original prefix. -/
@[expose] def zeroExtend (_h : n ≤ N) (x : Fin n → Bool) (i : Fin N) : Bool :=
  if hi : i.val < n then x ⟨i.val, hi⟩ else false

@[simp] theorem zeroExtend_castLE (h : n ≤ N) (x : Fin n → Bool) (i : Fin n) :
    zeroExtend h x (i.castLE h) = x i := by
  simp [zeroExtend, i.isLt]

theorem zeroExtend_of_le (h : n ≤ N) (x : Fin n → Bool) {i : Fin N} (hi : n ≤ i.val) :
    zeroExtend h x i = false := by
  simp only [zeroExtend, dite_eq_right (Nat.not_lt_of_ge hi)]

private def zeroExtension (n N : Nat) : MultiCircuit n N where
  wires := n + 1
  network := .cons (.const false) (.empty (n + 1))
  output i := if hi : i.val < n then (⟨i.val, hi⟩ : Fin n).castSucc else Fin.last n

private theorem eval_zeroExtension (h : n ≤ N) (x : Fin n → Bool) :
    (zeroExtension n N).eval x = zeroExtend h x := by
  funext i
  change (Gate.const false : Gate n).extend x
    (if hi : i.val < n then (⟨i.val, hi⟩ : Fin n).castSucc else Fin.last n) =
      (if hi : i.val < n then x ⟨i.val, hi⟩ else false)
  by_cases hi : i.val < n
  · simp only [dite_eq_left hi, Gate.extend_castSucc]
  · simp only [dite_eq_right hi, Gate.extend_last, Gate.eval]

namespace BooleanCircuit

/-- Read the first `n` wires of an `N`-bit input. -/
def liftPrefix (circuit : BooleanCircuit n) (h : n ≤ N) : BooleanCircuit N :=
  circuit.mapInputs (Fin.castLE h)

@[simp] theorem eval_liftPrefix (circuit : BooleanCircuit n) (h : n ≤ N) (x : Fin N → Bool) :
    (circuit.liftPrefix h).eval x = circuit.eval (x ∘ Fin.castLE h) :=
  eval_mapInputs circuit _ x

@[simp] theorem size_liftPrefix (circuit : BooleanCircuit n) (h : n ≤ N) :
    (circuit.liftPrefix h).size = circuit.size := size_mapInputs circuit _

private def requireFalse : List (Fin N) → BooleanCircuit N
  | [] => .const N true
  | i :: indices => .binary .and (input i).not (requireFalse indices)

private theorem eval_requireFalse_eq_true (indices : List (Fin N)) (x : Fin N → Bool) :
    (requireFalse indices).eval x = true ↔ ∀ i ∈ indices, x i = false := by
  induction indices with
  | nil => simp [requireFalse]
  | cons i rest ih =>
    simp [requireFalse, BinaryOp.eval, ih, List.mem_cons, forall_eq_or_imp]

private theorem size_requireFalse (indices : List (Fin N)) :
    (requireFalse indices).size = 2 * indices.length + 1 := by
  induction indices with
  | nil => simp [requireFalse]
  | cons i rest ih =>
    simp only [requireFalse, size_binary, size_not, size_input, ih, List.length_cons]
    omega

private def suffixIndices (n N : Nat) : List (Fin N) :=
  (List.finRange N).filter fun i ↦ decide (n ≤ i.val)

private theorem mem_suffixIndices (i : Fin N) : i ∈ suffixIndices n N ↔ n ≤ i.val := by
  simp only [suffixIndices, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]

/-- Run the prefix circuit and require every wire after the prefix to be false. -/
def liftPrefixWithFalseSuffix (circuit : BooleanCircuit n) (h : n ≤ N) : BooleanCircuit N :=
  .binary .and (circuit.liftPrefix h) (requireFalse (suffixIndices n N))

theorem eval_liftPrefixWithFalseSuffix_eq_true (circuit : BooleanCircuit n) (h : n ≤ N)
    (x : Fin N → Bool) :
    (circuit.liftPrefixWithFalseSuffix h).eval x = true ↔
      circuit.eval (x ∘ Fin.castLE h) = true ∧ ∀ i : Fin N, n ≤ i.val → x i = false := by
  simp only [liftPrefixWithFalseSuffix, eval_binary, BinaryOp.eval, Bool.and_eq_true,
    eval_liftPrefix, eval_requireFalse_eq_true, mem_suffixIndices]

theorem size_liftPrefixWithFalseSuffix_le (circuit : BooleanCircuit n) (h : n ≤ N) :
    (circuit.liftPrefixWithFalseSuffix h).size ≤ circuit.size + (2 * N + 2) := by
  have hCount : (suffixIndices n N).length ≤ N := by
    simpa only [suffixIndices, List.length_finRange] using
      List.length_filter_le (fun i : Fin N ↦ decide (n ≤ i.val)) (List.finRange N)
  simp only [liftPrefixWithFalseSuffix, size_binary, size_liftPrefix, size_requireFalse]
  omega

/-- Set the circuit's suffix inputs to the output of one shared false gate. -/
def restrictFalseSuffix (circuit : BooleanCircuit N) (_h : n ≤ N) : BooleanCircuit n :=
  (zeroExtension n N).thenBoolean circuit

@[simp] theorem eval_restrictFalseSuffix (circuit : BooleanCircuit N) (h : n ≤ N)
    (x : Fin n → Bool) : (circuit.restrictFalseSuffix h).eval x = circuit.eval (zeroExtend h x) := by
  simp only [restrictFalseSuffix, MultiCircuit.eval_thenBoolean, eval_zeroExtension h]

@[simp] theorem size_restrictFalseSuffix (circuit : BooleanCircuit N) (h : n ≤ N) :
    (circuit.restrictFalseSuffix h).size = circuit.size + 1 := by
  rw [restrictFalseSuffix, MultiCircuit.size_thenBoolean]
  exact Nat.add_comm 1 circuit.size

end BooleanCircuit

end PvsNP.Circuits
