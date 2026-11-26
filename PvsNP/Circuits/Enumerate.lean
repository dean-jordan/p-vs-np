module

public import PvsNP.Circuits.BooleanCircuit

/-! # Enumerating circuits by their gate count -/

public section

namespace PvsNP.Circuits

private theorem length_flatMap_eq_of_length {α β : Type} {inputs : List α}
    (f : α → List β) (t : Nat) (h : ∀ a ∈ inputs, (f a).length = t) :
    (inputs.flatMap f).length = inputs.length * t := by
  induction inputs with
  | nil => simp
  | cons a rest ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul,
      h a (List.mem_cons_self ..), ih (fun b hb ↦ h b (List.mem_cons_of_mem _ hb))]
    exact Nat.add_comm ..

private def binaryGates (n : Nat) (op : BinaryOp) : List (Gate n) :=
  (List.finRange n).flatMap fun left ↦ (List.finRange n).map (Gate.binary op left)

private theorem mem_binaryGates {n : Nat} (op : BinaryOp) (left right : Fin n) :
    Gate.binary op left right ∈ binaryGates n op :=
  List.mem_flatMap.mpr ⟨left, List.mem_finRange left, List.mem_map_of_mem (List.mem_finRange right)⟩

private theorem length_binaryGates (n : Nat) (op : BinaryOp) : (binaryGates n op).length = n * n := by
  unfold binaryGates
  rw [length_flatMap_eq_of_length _ n (fun _ _ ↦ by simp only [List.length_map, List.length_finRange]),
    List.length_finRange]

/-- Enumerate the constant, unary, and binary gates on the available wires. -/
def allGates (n : Nat) : List (Gate n) :=
  [.const false, .const true] ++ (List.finRange n).map Gate.not ++
    binaryGates n .and ++ binaryGates n .or

theorem mem_allGates {n : Nat} (gate : Gate n) : gate ∈ allGates n := by
  cases gate with
  | const value => cases value <;> simp [allGates]
  | not i =>
    have hi : Gate.not i ∈ (List.finRange n).map Gate.not :=
      List.mem_map_of_mem (List.mem_finRange i)
    simp [allGates, hi]
  | binary op left right =>
    cases op <;> simp [allGates, mem_binaryGates]

theorem length_allGates (n : Nat) : (allGates n).length = 2 + n + n * n + n * n := by
  simp only [allGates, List.length_append, List.length_cons, List.length_nil, List.length_map,
    List.length_finRange, length_binaryGates, Nat.zero_add]

theorem length_allGates_le (n : Nat) : (allGates n).length ≤ 8 * (n + 1) ^ 2 := by
  simp only [length_allGates, Nat.pow_two, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  omega

theorem Network.wires_eq_input_add_size {n m : Nat} (network : Network n m) :
    m = n + network.size := by
  induction network with
  | empty => rfl
  | cons gate rest ih => simpa only [Network.size, ← Nat.add_assoc] using ih

private def castWires {n m k : Nat} (h : m = k) (network : Network n m) : Network n k :=
  h ▸ network

private theorem cons_castWires {n m k : Nat} (gate : Gate n) (h : m = k)
    (rest : Network (n + 1) m) :
    Network.cons gate (castWires h rest) = castWires h (Network.cons gate rest) := by
  cases h
  rfl

private theorem castWires_trans {n m k r : Nat} (h : m = k) (e : k = r)
    (network : Network n m) :
    castWires e (castWires h network) = castWires (h.trans e) network := by
  cases h
  cases e
  rfl

private theorem eval_castWires {n m k : Nat} (h : m = k) (network : Network n m)
    (x : Fin n → Bool) (i : Fin m) : (castWires h network).eval x (i.cast h) = network.eval x i := by
  cases h
  rfl

/-- Enumerate the networks with exactly `s` gates and `n` input wires. -/
def enumerateNetworks (n : Nat) : (s : Nat) → List (Network n (n + s))
  | 0 => [.empty n]
  | s + 1 => (allGates n).flatMap fun gate ↦
    (enumerateNetworks (n + 1) s).map fun rest ↦ castWires (Nat.succ_add n s) (.cons gate rest)

theorem length_enumerateNetworks_zero (n : Nat) : (enumerateNetworks n 0).length = 1 := by
  simp [enumerateNetworks]

theorem length_enumerateNetworks_succ (n s : Nat) :
    (enumerateNetworks n (s + 1)).length =
      (allGates n).length * (enumerateNetworks (n + 1) s).length := by
  rw [enumerateNetworks, length_flatMap_eq_of_length _ (enumerateNetworks (n + 1) s).length
    (fun _ _ ↦ List.length_map _)]

private theorem mem_enumerateNetworks_castWires {n m : Nat} (network : Network n m) :
    ∀ s, network.size = s → ∀ h : m = n + s,
      castWires h network ∈ enumerateNetworks n s := by
  induction network with
  | empty n =>
    intro s hSize h
    change 0 = s at hSize
    subst s
    exact List.mem_singleton.mpr rfl
  | @cons n m gate rest ih =>
    intro s hSize h
    cases s with
    | zero => simp [Network.size] at hSize
    | succ s =>
      have hRestSize : rest.size = s := by
        simp only [Network.size] at hSize
        omega
      let hRest : m = n + 1 + s := h.trans (Nat.succ_add n s).symm
      rw [enumerateNetworks, List.mem_flatMap]
      refine ⟨gate, mem_allGates gate, List.mem_map.mpr ⟨castWires hRest rest, ?_, ?_⟩⟩
      · exact ih s hRestSize hRest
      · rw [cons_castWires, castWires_trans]

theorem length_enumerateNetworks_le (n s : Nat) :
    (enumerateNetworks n s).length ≤ (8 * (n + s + 1) ^ 2) ^ s := by
  induction s generalizing n with
  | zero => simp [length_enumerateNetworks_zero]
  | succ s ih =>
    rw [length_enumerateNetworks_succ, Nat.pow_succ]
    have hGate := Nat.le_trans (length_allGates_le n)
      (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left (show n + 1 ≤ n + (s + 1) + 1 by omega) 2))
    have hRest := ih (n + 1)
    rw [show n + 1 + s + 1 = n + (s + 1) + 1 by omega] at hRest
    rw [Nat.mul_comm (allGates n).length]
    exact Nat.mul_le_mul hRest hGate

/-- Enumerate circuits with `n` inputs and exactly `s` gates, including every output wire. -/
def enumerateCircuits (n s : Nat) : List (BooleanCircuit n) :=
  (enumerateNetworks n s).flatMap fun network ↦
    (List.finRange (n + s)).map fun out ↦ ⟨n + s, network, out⟩

theorem length_enumerateCircuits_eq (n s : Nat) :
    (enumerateCircuits n s).length = (enumerateNetworks n s).length * (n + s) := by
  unfold enumerateCircuits
  exact length_flatMap_eq_of_length _ (n + s) (fun _ _ ↦ by
    simp only [List.length_map, List.length_finRange])

theorem length_enumerateCircuits_le (n s : Nat) :
    (enumerateCircuits n s).length ≤ (n + s) * (8 * (n + s + 1) ^ 2) ^ s := by
  rw [length_enumerateCircuits_eq, Nat.mul_comm]
  exact Nat.mul_le_mul_left (n + s) (length_enumerateNetworks_le n s)

theorem size_eq_of_mem_enumerateCircuits {n s : Nat} {c : BooleanCircuit n}
    (h : c ∈ enumerateCircuits n s) : c.size = s := by
  unfold enumerateCircuits at h
  obtain ⟨network, _, hOutput⟩ := List.mem_flatMap.mp h
  obtain ⟨out, _, rfl⟩ := List.mem_map.mp hOutput
  have hCount := network.wires_eq_input_add_size
  change network.size = s
  omega

private def constantPadding (n : Nat) : (t : Nat) → Network n (n + t)
  | 0 => .empty n
  | t + 1 => (constantPadding n t).push (.const false)

private theorem size_constantPadding (n t : Nat) : (constantPadding n t).size = t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [constantPadding, Network.size_push, ih]

/-- Padding with constants gives a listed circuit of exactly `s` gates with the same output. -/
theorem exists_mem_enumerateCircuits_of_size_le {n : Nat} (c : BooleanCircuit n) {s : Nat}
    (h : c.size ≤ s) : ∃ d ∈ enumerateCircuits n s, ∀ x, d.eval x = c.eval x := by
  let pad := constantPadding c.wires (s - c.size)
  let whole := c.network.append pad
  have hSize : whole.size = s := by
    simp only [whole, pad, Network.size_append, size_constantPadding]
    change c.size + (s - c.size) = s
    omega
  have hWires : c.wires + (s - c.size) = n + s := by
    have hCount := whole.wires_eq_input_add_size
    rwa [hSize] at hCount
  let dNet := castWires hWires whole
  let i := (c.output.castLE pad.wires_le).cast hWires
  refine ⟨⟨n + s, dNet, i⟩, ?_, ?_⟩
  · rw [enumerateCircuits, List.mem_flatMap]
    refine ⟨dNet, mem_enumerateNetworks_castWires whole s hSize hWires, ?_⟩
    exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
  · intro x
    change (castWires hWires (c.network.append pad)).eval x
      ((c.output.castLE pad.wires_le).cast hWires) = c.eval x
    rw [eval_castWires, Network.eval_append, Network.eval_castLE]
    rfl

end PvsNP.Circuits
