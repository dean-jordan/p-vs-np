module

public import PvsNP.Circuits.BooleanCircuit
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card

/-! # Input support of bounded-fan-in circuits

Following dependencies backwards charges each gate once. Only a binary gate can
replace one needed wire by two, so shared wires do not inflate the bound.
-/

public section

namespace PvsNP.Circuits

variable {n m : Nat}

/-- The number of input pins of a gate. -/
@[expose] def Gate.arity : Gate n → Nat
  | .const _ => 0
  | .not _ => 1
  | .binary _ _ _ => 2

/-- The distinct wires read by a gate. -/
@[expose] def gateInputs : Gate n → Finset (Fin n)
  | .const _ => ∅
  | .not i => {i}
  | .binary _ i j => {i, j}

theorem gateInputs_card_le (gate : Gate n) : (gateInputs gate).card ≤ gate.arity := by
  cases gate with
  | const => simp [gateInputs, Gate.arity]
  | not => simp [gateInputs, Gate.arity]
  | binary op i j =>
    simpa only [gateInputs, Gate.arity, Finset.card_singleton] using
      Finset.card_insert_le i ({j} : Finset (Fin n))

theorem gate_eval_eq_of_agree (gate : Gate n) (x y : Fin n → Bool)
    (agree : ∀ i ∈ gateInputs gate, x i = y i) : gate.eval x = gate.eval y := by
  cases gate with
  | const => rfl
  | not i =>
    exact congrArg Bool.not (agree i (by simp [gateInputs]))
  | binary op i j =>
    simp only [Gate.eval]
    rw [agree i (by simp [gateInputs]), agree j (by simp [gateInputs])]

/-- Keep the needed wires from before the latest gate. -/
@[expose] def oldWires (needed : Finset (Fin (n + 1))) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ i.castSucc ∈ needed

theorem mem_oldWires_iff (needed : Finset (Fin (n + 1))) (i : Fin n) :
    i ∈ oldWires needed ↔ i.castSucc ∈ needed := by
  simp [oldWires]

theorem oldWires_map (needed : Finset (Fin (n + 1))) :
    (oldWires needed).map Fin.castSuccEmb = needed.erase (Fin.last n) := by
  ext j
  refine Fin.lastCases ?_ (fun i ↦ ?_) j
  · constructor
    · intro h
      obtain ⟨i, _, hi⟩ := Finset.mem_map.mp h
      have hVal := congrArg Fin.val hi
      change i.val = n at hVal
      exact (Nat.ne_of_lt i.isLt hVal).elim
    · intro h
      exact ((Finset.mem_erase.mp h).1 rfl).elim
  · have hOld : i.castSucc ≠ Fin.last n := by
      intro e
      have hVal := congrArg Fin.val e
      change i.val = n at hVal
      exact Nat.ne_of_lt i.isLt hVal
    have hMem := Finset.mem_map' Fin.castSuccEmb (a := i) (s := oldWires needed)
    exact hMem.trans ((mem_oldWires_iff needed i).trans
      (Finset.mem_erase.trans (and_iff_right hOld)).symm)

theorem oldWires_card (needed : Finset (Fin (n + 1))) :
    (oldWires needed).card = (needed.erase (Fin.last n)).card := by
  rw [← oldWires_map needed, Finset.card_map]

/-- The wires required before a gate to evaluate the given wires after it. -/
@[expose] def previousSupport (gate : Gate n) (needed : Finset (Fin (n + 1))) :
    Finset (Fin n) :=
  oldWires needed ∪ (if Fin.last n ∈ needed then gateInputs gate else ∅)

theorem previousSupport_card_le (gate : Gate n) (needed : Finset (Fin (n + 1))) :
    (previousSupport gate needed).card ≤ needed.card + (gate.arity - 1) := by
  unfold previousSupport
  split
  · rename_i hNeeded
    have hUnion := Finset.card_union_le (oldWires needed) (gateInputs gate)
    have hInputs := gateInputs_card_le gate
    have hErased := Finset.card_erase_add_one hNeeded
    rw [oldWires_card] at hUnion
    omega
  · rw [Finset.union_empty, oldWires_card]
    exact Nat.le_trans Finset.card_erase_le (Nat.le_add_right ..)

theorem extend_eq_of_agree (gate : Gate n) (needed : Finset (Fin (n + 1)))
    (x y : Fin n → Bool) (agree : ∀ i ∈ previousSupport gate needed, x i = y i) :
    ∀ j ∈ needed, gate.extend x j = gate.extend y j := by
  intro j
  refine Fin.lastCases ?_ (fun i ↦ ?_) j
  · intro hLast
    rw [Gate.extend_last, Gate.extend_last]
    apply gate_eval_eq_of_agree
    intro i hi
    apply agree i
    exact Finset.mem_union_right _ (by simpa only [ite_eq_left hLast] using hi)
  · intro hi
    rw [Gate.extend_castSucc, Gate.extend_castSucc]
    apply agree i
    exact Finset.mem_union_left _ ((mem_oldWires_iff needed i).mpr hi)

namespace Network

/-- Count the binary gates in a network. -/
@[expose] def binarySize : {n m : Nat} → Network n m → Nat
  | _, _, .empty _ => 0
  | _, _, .cons gate rest => (gate.arity - 1) + rest.binarySize

theorem binarySize_le_size (network : Network n m) : network.binarySize ≤ network.size := by
  induction network with
  | empty => exact Nat.le_refl 0
  | cons gate rest ih =>
    have hGate : gate.arity - 1 ≤ 1 := by cases gate <;> simp [Gate.arity]
    exact Nat.add_le_add hGate ih

/-- Follow every dependency of the selected output wires back to the inputs. -/
@[expose] def inputSupport : {n m : Nat} → Network n m → Finset (Fin m) → Finset (Fin n)
  | _, _, .empty _, needed => needed
  | _, _, .cons gate rest, needed => previousSupport gate (rest.inputSupport needed)

theorem eval_eq_of_agree_inputSupport (network : Network n m) (needed : Finset (Fin m))
    (x y : Fin n → Bool) (agree : ∀ i ∈ network.inputSupport needed, x i = y i) :
    ∀ j ∈ needed, network.eval x j = network.eval y j := by
  induction network with
  | empty => exact agree
  | cons gate rest ih =>
    exact ih needed (gate.extend x) (gate.extend y)
      (extend_eq_of_agree gate (rest.inputSupport needed) x y agree)

theorem inputSupport_card_le (network : Network n m) (needed : Finset (Fin m)) :
    (network.inputSupport needed).card ≤ needed.card + network.binarySize := by
  induction network with
  | empty => simp [inputSupport, binarySize]
  | cons gate rest ih =>
    have hStep := previousSupport_card_le gate (rest.inputSupport needed)
    have hRest := ih needed
    simp only [inputSupport, binarySize]
    omega

/-- The specified outputs depend on at most one additional input wire per binary gate. -/
theorem exists_inputSupport_binary (network : Network n m) (needed : Finset (Fin m)) :
    ∃ support : Finset (Fin n), support.card ≤ needed.card + network.binarySize ∧
      ∀ x y : Fin n → Bool, (∀ i ∈ support, x i = y i) →
        ∀ j ∈ needed, network.eval x j = network.eval y j :=
  ⟨network.inputSupport needed, network.inputSupport_card_le needed,
    network.eval_eq_of_agree_inputSupport needed⟩

/-- The specified outputs depend on at most one additional input wire per gate. -/
theorem exists_inputSupport (network : Network n m) (needed : Finset (Fin m)) :
    ∃ support : Finset (Fin n), support.card ≤ needed.card + network.size ∧
      ∀ x y : Fin n → Bool, (∀ i ∈ support, x i = y i) →
        ∀ j ∈ needed, network.eval x j = network.eval y j := by
  obtain ⟨support, hCard, hSound⟩ := network.exists_inputSupport_binary needed
  exact ⟨support, hCard.trans (Nat.add_le_add_left network.binarySize_le_size _), hSound⟩

private theorem extend_binary_mono (op : BinaryOp) (left right : Fin n) (x y : Fin n → Bool)
    (h : ∀ i, x i = true → y i = true) (j : Fin (n + 1)) :
    (Gate.binary op left right).extend x j = true →
      (Gate.binary op left right).extend y j = true := by
  by_cases hj : j.val < n
  · simpa only [Gate.extend, dite_eq_left hj] using h ⟨j.val, hj⟩
  · simp only [Gate.extend, dite_eq_right hj, Gate.eval]
    cases op with
    | and =>
      simp only [BinaryOp.eval, Bool.and_eq_true]
      exact fun hx ↦ ⟨h left hx.1, h right hx.2⟩
    | or =>
      simp only [BinaryOp.eval, Bool.or_eq_true]
      exact Or.imp (h left) (h right)

private theorem extend_const_mono (value : Bool) (x y : Fin n → Bool)
    (h : ∀ i, x i = true → y i = true) (j : Fin (n + 1)) :
    (Gate.const value).extend x j = true → (Gate.const value).extend y j = true := by
  by_cases hj : j.val < n
  · simpa only [Gate.extend, dite_eq_left hj] using h ⟨j.val, hj⟩
  · simp only [Gate.extend, dite_eq_right hj, Gate.eval, imp_self]

/-- Count NOT gates separately from binary gates and constants. -/
@[expose] def negationSize : {n m : Nat} → Network n m → Nat
  | _, _, .empty _ => 0
  | _, _, .cons (.not _) rest => 1 + rest.negationSize
  | _, _, .cons _ rest => rest.negationSize

theorem binarySize_add_negationSize_le_size (network : Network n m) :
    network.binarySize + network.negationSize ≤ network.size := by
  induction network with
  | empty => exact Nat.le_refl 0
  | cons gate rest ih => cases gate <;> simp [binarySize, negationSize, Gate.arity, size] <;> omega

/-- A network of AND, OR, and constant gates is monotone. -/
theorem eval_mono_of_negationSize_zero (network : Network n m)
    (hSize : network.negationSize = 0) (x y : Fin n → Bool)
    (hInput : ∀ i, x i = true → y i = true) (j : Fin m) :
    network.eval x j = true → network.eval y j = true := by
  induction network with
  | empty => exact hInput j
  | cons gate rest ih =>
    cases gate with
    | const value =>
      exact ih hSize _ _ (extend_const_mono value x y hInput) j
    | not src =>
      simp only [negationSize] at hSize
      omega
    | binary op left right =>
      exact ih hSize _ _ (extend_binary_mono op left right x y hInput) j

end Network

namespace BooleanCircuit

/-- Count the binary gates in a circuit. -/
@[expose] def binarySize (circuit : BooleanCircuit n) : Nat := circuit.network.binarySize

theorem binarySize_le_size (circuit : BooleanCircuit n) : circuit.binarySize ≤ circuit.size :=
  circuit.network.binarySize_le_size

/-- A single selected output depends on at most `binarySize + 1` input wires. -/
theorem exists_inputSupport_binary (circuit : BooleanCircuit n) :
    ∃ support : Finset (Fin n), support.card ≤ circuit.binarySize + 1 ∧
      ∀ x y : Fin n → Bool, (∀ i ∈ support, x i = y i) → circuit.eval x = circuit.eval y := by
  obtain ⟨support, hCard, hSound⟩ := circuit.network.exists_inputSupport_binary {circuit.output}
  refine ⟨support, ?_, fun x y agree ↦ hSound x y agree _ (Finset.mem_singleton_self _)⟩
  simpa only [Finset.card_singleton, binarySize, Nat.add_comm] using hCard

/-- A single selected output depends on at most `size + 1` input wires. -/
theorem exists_inputSupport (circuit : BooleanCircuit n) :
    ∃ support : Finset (Fin n), support.card ≤ circuit.size + 1 ∧
      ∀ x y : Fin n → Bool, (∀ i ∈ support, x i = y i) → circuit.eval x = circuit.eval y := by
  obtain ⟨support, hCard, hSound⟩ := circuit.exists_inputSupport_binary
  exact ⟨support, hCard.trans (Nat.add_le_add_right circuit.binarySize_le_size _), hSound⟩

/-- Each independently relevant input must appear in a support for the output. -/
theorem card_le_binarySize_add_one_of_sensitive {k : Nat} (c : BooleanCircuit n)
    (coords : Fin k ↪ Fin n)
    (hSensitive : ∀ i : Fin k, ∃ x y : Fin n → Bool,
      c.eval x ≠ c.eval y ∧ ∀ j, j ≠ coords i → x j = y j) : k ≤ c.binarySize + 1 := by
  obtain ⟨support, hSize, hEval⟩ := c.exists_inputSupport_binary
  have hSubset : (Finset.univ : Finset (Fin k)).map coords ⊆ support := by
    intro j hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hj
    by_contra hMiss
    obtain ⟨x, y, hDiff, hAgree⟩ := hSensitive i
    apply hDiff
    exact hEval x y (fun j hj ↦ hAgree j (fun he ↦ hMiss (he ▸ hj)))
  simpa only [Finset.card_map, Finset.card_univ, Fintype.card_fin] using
    (Finset.card_le_card hSubset).trans hSize

end BooleanCircuit

end PvsNP.Circuits
