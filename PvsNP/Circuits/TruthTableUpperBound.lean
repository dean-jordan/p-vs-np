module

public import PvsNP.Circuits.BooleanCircuit

/-! # Circuit synthesis by splitting on the first input bit -/

public section

namespace PvsNP.Circuits

/-- Build a circuit for any Boolean function by preparing the two restrictions at the first
input bit and selecting the applicable output. -/
def truthTableCircuit : (n : Nat) → ((Fin n → Bool) → Bool) → BooleanCircuit n
  | 0, f => .const 0 (f Fin.elim0)
  | n + 1, f =>
    let bit := BooleanCircuit.input (0 : Fin (n + 1))
    let high := (truthTableCircuit n (fun x ↦ f (Fin.cases true x))).mapInputs Fin.succ
    let low := (truthTableCircuit n (fun x ↦ f (Fin.cases false x))).mapInputs Fin.succ
    .binary .or (.binary .and bit high) (.binary .and bit.not low)

theorem truthTableCircuit_eval (n : Nat) (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    (truthTableCircuit n f).eval x = f x := by
  induction n with
  | zero =>
    have hInput : (Fin.elim0 : Fin 0 → Bool) = x := funext fun i ↦ i.elim0
    simp only [truthTableCircuit, BooleanCircuit.eval_const, hInput]
  | succ n ih =>
    have hInput : Fin.cases (x 0) (x ∘ Fin.succ) = x :=
      funext fun i ↦ Fin.cases rfl (fun _ ↦ rfl) i
    cases h : x 0 <;> rw [h] at hInput <;>
      simp [truthTableCircuit, BinaryOp.eval, ih, h, hInput]

/-- Each input split adds one NOT and three binary gates to the two subcircuits. -/
theorem truthTableCircuit_size_add_four (n : Nat) (f : (Fin n → Bool) → Bool) :
    (truthTableCircuit n f).size + 4 = 5 * 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hHigh := ih (fun x ↦ f (Fin.cases true x))
    have hLow := ih (fun x ↦ f (Fin.cases false x))
    simp only [truthTableCircuit, BooleanCircuit.size_binary, BooleanCircuit.size_not,
      BooleanCircuit.size_input, BooleanCircuit.size_mapInputs, Nat.pow_succ]
    omega

/-- The synthesis gives a gate bound uniform over all functions at each arity. -/
theorem truthTableCircuit_size_le (n : Nat) (f : (Fin n → Bool) → Bool) :
    (truthTableCircuit n f).size ≤ 5 * 2 ^ n := by
  rw [← truthTableCircuit_size_add_four n f]
  exact Nat.le_add_right ..

end PvsNP.Circuits
