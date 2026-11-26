module

public import PvsNP.Circuits.InputSupport

/-! # Exact conversion to circuits over AND, OR, and NOT -/

public section

namespace PvsNP.Circuits

/-- A gate belongs to the AND, OR, NOT basis. -/
@[expose] def Gate.ConstantFree {n : Nat} : Gate n → Prop
  | .const _ => False
  | .not _ | .binary _ _ _ => True

/-- A network has no literal constant gates. -/
@[expose] def Network.ConstantFree : {n m : Nat} → Network n m → Prop
  | _, _, .empty _ => True
  | _, _, .cons gate rest => gate.ConstantFree ∧ rest.ConstantFree

/-- The strict basis uses only binary AND, binary OR, and unary NOT gates. -/
@[expose] def BooleanCircuit.ConstantFree {n : Nat} (c : BooleanCircuit n) : Prop :=
  c.network.ConstantFree

private def referenceValue {n : Nat} (bits : Fin n → Bool) : Bool ⊕ Fin n → Bool
  | .inl bit => bit
  | .inr wire => bits wire

private inductive GateFold (n : Nat) where
  | reuse (ref : Bool ⊕ Fin n)
  | keep (gate : Gate n) (free : gate.ConstantFree)

private def GateFold.eval {n : Nat} (bits : Fin n → Bool) : GateFold n → Bool
  | .reuse ref => referenceValue bits ref
  | .keep gate _ => gate.eval bits

private def foldBinaryConstant {n : Nat} (op : BinaryOp) (bit : Bool) (wire : Fin n) :
    GateFold n :=
  match op, bit with
  | .and, true | .or, false => .reuse (.inr wire)
  | .and, false | .or, true => .reuse (.inl bit)

private def foldBinary {n : Nat} (op : BinaryOp) : Bool ⊕ Fin n → Bool ⊕ Fin n → GateFold n
  | .inl a, .inl b => .reuse (.inl (op.eval a b))
  | .inl a, .inr i | .inr i, .inl a => foldBinaryConstant op a i
  | .inr i, .inr j => .keep (.binary op i j) trivial

private def foldGate {m n : Nat} (refs : Fin m → Bool ⊕ Fin n) : Gate m → GateFold n
  | .const bit => .reuse (.inl bit)
  | .not i => match refs i with
    | .inl bit => .reuse (.inl (!bit))
    | .inr wire => .keep (.not wire) trivial
  | .binary op l r => foldBinary op (refs l) (refs r)

private theorem foldBinary_eval {n : Nat} (op : BinaryOp) (l r : Bool ⊕ Fin n)
    (bits : Fin n → Bool) :
    (foldBinary op l r).eval bits = op.eval (referenceValue bits l) (referenceValue bits r) := by
  cases l with
  | inl a =>
    cases r with
    | inl b => rfl
    | inr j => cases op <;> cases a <;> simp [foldBinary, foldBinaryConstant, GateFold.eval,
        referenceValue, BinaryOp.eval]
  | inr i =>
    cases r with
    | inl b => cases op <;> cases b <;> simp [foldBinary, foldBinaryConstant, GateFold.eval,
        referenceValue, BinaryOp.eval]
    | inr j => rfl

private theorem foldGate_eval {m n : Nat} (refs : Fin m → Bool ⊕ Fin n) (gate : Gate m)
    (bits : Fin n → Bool) :
    (foldGate refs gate).eval bits = gate.eval (fun i ↦ referenceValue bits (refs i)) := by
  cases gate with
  | const _ => rfl
  | not src =>
    cases h : refs src <;> simp [foldGate, GateFold.eval, referenceValue, Gate.eval, h]
  | binary op l r => exact foldBinary_eval op (refs l) (refs r) bits

private theorem chargedRest_le {m k : Nat} (gate : Gate m) (rest : Network (m + 1) k) :
    rest.binarySize + rest.negationSize ≤
      (Network.cons gate rest).binarySize + (Network.cons gate rest).negationSize := by
  cases gate <;> simp only [Network.binarySize, Network.negationSize, Gate.arity] <;> omega

private theorem chargedKeep {m k n : Nat} (refs : Fin m → Bool ⊕ Fin n) (gate : Gate m)
    (rest : Network (m + 1) k) (kept : Gate n) (free : kept.ConstantFree)
    (h : foldGate refs gate = .keep kept free) :
    1 + (rest.binarySize + rest.negationSize) =
      (Network.cons gate rest).binarySize + (Network.cons gate rest).negationSize := by
  cases gate with
  | const bit => cases h
  | not src => simp only [Network.binarySize, Network.negationSize, Gate.arity]; omega
  | binary op l r => simp only [Network.binarySize, Network.negationSize, Gate.arity]; omega

private theorem referenceValue_castSucc {n : Nat} (gate : Gate n) (bits : Fin n → Bool)
    (ref : Bool ⊕ Fin n) :
    referenceValue (gate.extend bits) (ref.map id Fin.castSucc) = referenceValue bits ref := by
  cases ref <;> simp [referenceValue, Sum.map]

/-- The new network retains a constant or a real wire for every original output. -/
private structure FoldedNetwork {m k : Nat} (original : Network m k) (n : Nat)
    (inputs : Fin m → Bool ⊕ Fin n) where
  wires : Nat
  network : Network n wires
  output : Fin k → Bool ⊕ Fin wires
  eval_output : ∀ bits i, referenceValue (network.eval bits) (output i) =
    original.eval (fun j ↦ referenceValue bits (inputs j)) i
  constantFree : network.ConstantFree
  size_le : network.size ≤ original.binarySize + original.negationSize

private def foldNetwork : {m k : Nat} → (original : Network m k) → {n : Nat} →
    (inputs : Fin m → Bool ⊕ Fin n) → FoldedNetwork original n inputs
  | _, _, .empty _, n, refs =>
    ⟨n, .empty n, refs, fun _ _ ↦ rfl, trivial, Nat.zero_le _⟩
  | m, _, .cons gate rest, n, refs =>
    match h : foldGate refs gate with
    | .reuse ref =>
      let nextRefs : Fin (m + 1) → Bool ⊕ Fin n := Fin.lastCases ref refs
      let tail := foldNetwork rest nextRefs
      { wires := tail.wires
        network := tail.network
        output := tail.output
        eval_output := by
          intro bits i
          rw [tail.eval_output]
          have hExtend : (fun j ↦ referenceValue bits (nextRefs j)) =
              gate.extend (fun j ↦ referenceValue bits (refs j)) := by
            funext j
            refine Fin.lastCases ?_ (fun k ↦ ?_) j
            · simp only [nextRefs, Fin.lastCases_last, Gate.extend_last]
              have hValue := foldGate_eval refs gate bits
              rw [h] at hValue
              exact hValue
            · simp only [nextRefs, Fin.lastCases_castSucc, Gate.extend_castSucc]
          rw [hExtend]
          rfl
        constantFree := tail.constantFree
        size_le := tail.size_le.trans (chargedRest_le gate rest) }
    | .keep kept free =>
      let nextRefs : Fin (m + 1) → Bool ⊕ Fin (n + 1) :=
        Fin.lastCases (.inr (Fin.last n)) (fun i ↦ (refs i).map id Fin.castSucc)
      let tail := foldNetwork rest nextRefs
      { wires := tail.wires
        network := .cons kept tail.network
        output := tail.output
        eval_output := by
          intro bits i
          simp only [Network.eval, tail.eval_output]
          have hExtend : (fun j ↦ referenceValue (kept.extend bits) (nextRefs j)) =
              gate.extend (fun j ↦ referenceValue bits (refs j)) := by
            funext j
            refine Fin.lastCases ?_ (fun k ↦ ?_) j
            · simp only [nextRefs, Fin.lastCases_last, Gate.extend_last, referenceValue]
              have hValue := foldGate_eval refs gate bits
              rw [h] at hValue
              exact hValue
            · simp only [nextRefs, Fin.lastCases_castSucc, referenceValue_castSucc,
                Gate.extend_castSucc]
          rw [hExtend]
        constantFree := ⟨free, tail.constantFree⟩
        size_le := (Nat.add_le_add_left tail.size_le 1).trans_eq
          (chargedKeep refs gate rest kept free h) }

namespace BooleanCircuit

variable {m n : Nat}

/-- Substitute constants or input wires and fold the gates in topological order.
A folded literal output can be represented directly without allocating a gate. -/
def foldWithConstants (c : BooleanCircuit m) (refs : Fin m → Bool ⊕ Fin n) :
    Bool ⊕ BooleanCircuit n :=
  let folded := foldNetwork c.network refs
  match folded.output c.output with
  | .inl bit => .inl bit
  | .inr output => .inr ⟨folded.wires, folded.network, output⟩

/-- Fold all literal constants with the original input wiring. -/
def foldConstants (c : BooleanCircuit n) : Bool ⊕ BooleanCircuit n :=
  c.foldWithConstants Sum.inr

/-- The folded result agrees on every assignment to the remaining input wires. -/
theorem foldWithConstants_eval (c : BooleanCircuit m) (refs : Fin m → Bool ⊕ Fin n)
    (bits : Fin n → Bool) :
    (match c.foldWithConstants refs with
      | .inl bit => bit
      | .inr result => result.eval bits) =
    c.eval (fun i ↦ match refs i with | .inl bit => bit | .inr wire => bits wire) := by
  let folded := foldNetwork c.network refs
  have hEval := folded.eval_output bits c.output
  unfold foldWithConstants
  change (match (match folded.output c.output with
    | .inl bit => Sum.inl bit
    | .inr out => Sum.inr (⟨folded.wires, folded.network, out⟩ : BooleanCircuit n)) with
    | .inl bit => bit
    | .inr result => result.eval bits) = _
  cases h : folded.output c.output with
  | inl bit =>
    rw [h] at hEval
    exact hEval
  | inr wire =>
    rw [h] at hEval
    exact hEval

/-- A retained circuit uses only AND, OR, and NOT, with no more gates than
those three types of gates used in the original circuit. -/
theorem constantFree_size_le_of_foldWithConstants_eq_inr (c : BooleanCircuit m)
    (refs : Fin m → Bool ⊕ Fin n) {result : BooleanCircuit n}
    (h : c.foldWithConstants refs = .inr result) :
    result.ConstantFree ∧ result.size ≤ c.binarySize + c.network.negationSize := by
  let folded := foldNetwork c.network refs
  change (match folded.output c.output with
    | .inl bit => Sum.inl bit
    | .inr out => Sum.inr (⟨folded.wires, folded.network, out⟩ : BooleanCircuit n)) = _ at h
  split at h
  · contradiction
  · obtain rfl := Sum.inr.inj h
    exact ⟨folded.constantFree, folded.size_le⟩

/-- Folding the original circuit preserves its Boolean function. -/
theorem foldConstants_eval (c : BooleanCircuit n) (bits : Fin n → Bool) :
    (match c.foldConstants with | .inl bit => bit | .inr result => result.eval bits) =
      c.eval bits :=
  c.foldWithConstants_eval Sum.inr bits

/-- A circuit with a nonconstant output can always be converted at its original
size budget. The stronger bound counts only binary and negation gates in the source. -/
theorem exists_constantFree_of_nonconstant (c : BooleanCircuit n)
    (h : ∃ x y, c.eval x ≠ c.eval y) :
    ∃ result : BooleanCircuit n, result.ConstantFree ∧
      result.size ≤ c.binarySize + c.network.negationSize ∧ result.eval = c.eval := by
  cases hFold : c.foldConstants with
  | inl bit =>
    obtain ⟨x, y, hNe⟩ := h
    have hx := c.foldConstants_eval x
    have hy := c.foldConstants_eval y
    rw [hFold] at hx hy
    exact (hNe (hx.symm.trans hy)).elim
  | inr result =>
    obtain ⟨hFree, hSize⟩ := c.constantFree_size_le_of_foldWithConstants_eq_inr Sum.inr hFold
    refine ⟨result, hFree, hSize, funext fun bits ↦ ?_⟩
    simpa only [hFold] using c.foldConstants_eval bits

/-- With an input wire, either fixed Boolean can be produced in two gates:
negate the wire, and combine it with its negation. -/
@[expose] def constantFreeConst (wire : Fin n) (bit : Bool) : BooleanCircuit n :=
  ⟨n + 2, .cons (.not wire) (.cons
    (.binary (if bit then .or else .and) wire.castSucc (Fin.last n)) (.empty (n + 2))),
    Fin.last (n + 1)⟩

@[simp] theorem constantFree_constantFreeConst (wire : Fin n) (bit : Bool) :
    (constantFreeConst wire bit).ConstantFree :=
  ⟨trivial, trivial, trivial⟩

@[simp] theorem size_constantFreeConst (wire : Fin n) (bit : Bool) :
    (constantFreeConst wire bit).size = 2 := rfl

@[simp] theorem eval_constantFreeConst (wire : Fin n) (bit : Bool) (bits : Fin n → Bool) :
    (constantFreeConst wire bit).eval bits = bit := by
  simp only [constantFreeConst, eval, Network.eval, Gate.extend_last, Gate.eval,
    Gate.extend_castSucc]
  cases bit <;> cases bits wire <;> simp [BinaryOp.eval]

private theorem endpoints_ne_of_small_constantFree {n m : Nat} (network : Network n m)
    (hFree : network.ConstantFree) (hSize : network.size ≤ 1) (output : Fin m) :
    network.eval (fun _ ↦ false) output ≠ network.eval (fun _ ↦ true) output := by
  cases network with
  | empty _ => simp [Network.eval]
  | cons gate rest =>
    cases rest with
    | empty _ =>
      refine Fin.lastCases ?_ (fun i ↦ ?_) output
      · cases gate with
        | const _ => exact False.elim hFree.1
        | not _ => simp [Network.eval, Gate.eval]
        | binary op _ _ => cases op <;> simp [Network.eval, Gate.eval, BinaryOp.eval]
      · simp [Network.eval]
    | cons _ tail =>
      simp only [Network.size] at hSize
      omega

/-- A fixed-output circuit over AND, OR, and NOT needs at least two gates. -/
theorem two_le_size_of_constantFree_constant (c : BooleanCircuit n) (hFree : c.ConstantFree)
    (bit : Bool) (hEval : ∀ input, c.eval input = bit) : 2 ≤ c.size := by
  by_contra! hSize
  have hSmall : c.network.size ≤ 1 := by
    change c.size ≤ 1
    omega
  have hEndpoints := endpoints_ne_of_small_constantFree c.network hFree hSmall c.output
  exact hEndpoints ((hEval (fun _ ↦ false)).trans (hEval (fun _ ↦ true)).symm)

/-- Every circuit has an equivalent constant-free representative at cost at
most its original size or two, whichever is greater. -/
theorem exists_constantFree_le_max_two (c : BooleanCircuit n) (hn : 0 < n) :
    ∃ result : BooleanCircuit n, result.ConstantFree ∧ result.size ≤ max 2 c.size ∧
      result.eval = c.eval := by
  cases hFold : c.foldConstants with
  | inl bit =>
    let wire : Fin n := ⟨0, hn⟩
    refine ⟨constantFreeConst wire bit, constantFree_constantFreeConst .., ?_, ?_⟩
    · rw [size_constantFreeConst]
      exact Nat.le_max_left ..
    · funext bits
      have hEval := c.foldConstants_eval bits
      rw [hFold] at hEval
      exact (eval_constantFreeConst _ _ _).trans hEval
  | inr result =>
    obtain ⟨hFree, hSize⟩ := c.constantFree_size_le_of_foldWithConstants_eq_inr Sum.inr hFold
    refine ⟨result, hFree, hSize.trans (c.network.binarySize_add_negationSize_le_size.trans
      (Nat.le_max_right ..)), funext fun bits ↦ ?_⟩
    simpa only [hFold] using c.foldConstants_eval bits

end BooleanCircuit

/-- For positive arity and cap at least two, imposing the strict basis
preserves the exact budget for any property of the circuit's output function. -/
theorem exists_constantFree_size_le_iff {n cap : Nat} (hn : 0 < n) (hCap : 2 ≤ cap)
    (p : ((Fin n → Bool) → Bool) → Prop) :
    (∃ c : BooleanCircuit n, c.ConstantFree ∧ c.size ≤ cap ∧ p c.eval) ↔
      ∃ c : BooleanCircuit n, c.size ≤ cap ∧ p c.eval := by
  constructor
  · rintro ⟨c, _, hSize, hProperty⟩
    exact ⟨c, hSize, hProperty⟩
  · rintro ⟨c, hSize, hProperty⟩
    obtain ⟨result, hFree, hBound, hEval⟩ := c.exists_constantFree_le_max_two hn
    exact ⟨result, hFree, hBound.trans (Nat.max_le.mpr ⟨hCap, hSize⟩), hEval.symm ▸ hProperty⟩

end PvsNP.Circuits
