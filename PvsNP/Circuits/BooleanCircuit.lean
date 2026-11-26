module

public import PvsNP.Circuits.Layered

import Init.Data.Fin.Lemmas

/-! # Boolean circuits in topological order

Every gate references only inputs and outputs of earlier gates. Earlier wires remain
available for arbitrary fan-out. The size is the number of gates.
-/

public section

namespace PvsNP.Circuits

/-- The two binary operations for circuit gates. -/
inductive BinaryOp where
  | and
  | or

/-- Evaluate one of the binary operations. -/
@[expose] def BinaryOp.eval : BinaryOp → Bool → Bool → Bool
  | .and => (· && ·)
  | .or => (· || ·)

/-- A fan-in-at-most-two gate with access to the first `n` wires. -/
inductive Gate (n : Nat) where
  | const (value : Bool)
  | not (src : Fin n)
  | binary (op : BinaryOp) (left right : Fin n)

namespace Gate

variable {n : Nat}

@[expose] def eval (bits : Fin n → Bool) : Gate n → Bool
  | .const b => b
  | .not i => !(bits i)
  | .binary op l r => op.eval (bits l) (bits r)

/-- Add the gate value at the last wire and retain all earlier wires. -/
@[expose] def extend (gate : Gate n) (bits : Fin n → Bool) (i : Fin (n + 1)) : Bool :=
  if h : i.val < n then bits ⟨i.val, h⟩ else gate.eval bits

@[simp] theorem extend_castSucc (gate : Gate n) (bits : Fin n → Bool) (i : Fin n) :
    gate.extend bits i.castSucc = bits i := by
  simp [extend, i.isLt]

@[simp] theorem extend_last (gate : Gate n) (bits : Fin n → Bool) :
    gate.extend bits (Fin.last n) = gate.eval bits := by
  simp [extend]

end Gate

/-- A sequence of gates extending `n` input wires to a total of `m` wires. -/
inductive Network : Nat → Nat → Type where
  | empty (n : Nat) : Network n n
  | cons {n m : Nat} (gate : Gate n) (rest : Network (n + 1) m) : Network n m

namespace Network

variable {n m k : Nat}

@[expose] def eval : {n m : Nat} → Network n m → (Fin n → Bool) → Fin m → Bool
  | _, _, .empty _, bits => bits
  | _, _, .cons gate rest, bits => rest.eval (gate.extend bits)

@[expose] def size : {n m : Nat} → Network n m → Nat
  | _, _, .empty _ => 0
  | _, _, .cons _ rest => 1 + rest.size

/-- All earlier wires are still available when the network finishes. -/
theorem wires_le (network : Network n m) : n ≤ m := by
  induction network with
  | empty => exact Nat.le_refl _
  | cons _ _ ih => exact Nat.le_trans (Nat.le_succ _) ih

@[simp] theorem eval_castLE (network : Network n m) (bits : Fin n → Bool) (i : Fin n) :
    network.eval bits (i.castLE network.wires_le) = bits i := by
  induction network with
  | empty _ => rfl
  | cons gate rest ih =>
    change rest.eval (gate.extend bits) (i.castSucc.castLE rest.wires_le) = bits i
    rw [ih, Gate.extend_castSucc]

/-- Join two gate sequences at their shared wire count. -/
@[expose] def append : {n m k : Nat} → Network n m → Network m k → Network n k
  | _, _, _, .empty _, after => after
  | _, _, _, .cons gate rest, after => .cons gate (rest.append after)

@[simp] theorem eval_append (before : Network n m) (after : Network m k)
    (bits : Fin n → Bool) : (before.append after).eval bits = after.eval (before.eval bits) := by
  induction before with
  | empty => rfl
  | cons gate rest ih => exact ih after (gate.extend bits)

@[simp] theorem size_append (before : Network n m) (after : Network m k) :
    (before.append after).size = before.size + after.size := by
  induction before with
  | empty => exact (Nat.zero_add _).symm
  | cons gate rest ih =>
    change 1 + (rest.append after).size = 1 + rest.size + after.size
    rw [ih, Nat.add_assoc]

/-- Put one gate after an existing sequence. -/
@[expose] def push (network : Network n m) (gate : Gate m) : Network n (m + 1) :=
  network.append (.cons gate (.empty (m + 1)))

@[simp] theorem eval_push_last (network : Network n m) (gate : Gate m) (bits : Fin n → Bool) :
    (network.push gate).eval bits (Fin.last m) = gate.eval (network.eval bits) := by
  rw [push, eval_append]
  exact gate.extend_last (network.eval bits)

@[simp] theorem size_push (network : Network n m) (gate : Gate m) :
    (network.push gate).size = network.size + 1 := by
  rw [push, size_append]
  rfl

end Network

private def mapGate {m n : Nat} (refs : Fin m → Fin n) : Gate m → Gate n
  | .const value => .const value
  | .not i => .not (refs i)
  | .binary op i j => .binary op (refs i) (refs j)

private theorem eval_mapGate {m n : Nat} (refs : Fin m → Fin n) (gate : Gate m)
    (bits : Fin n → Bool) : (mapGate refs gate).eval bits = gate.eval (bits ∘ refs) := by
  cases gate <;> rfl

private def extendReferences {m n : Nat} (refs : Fin m → Fin n) : Fin (m + 1) → Fin (n + 1) :=
  Fin.lastCases (Fin.last n) (fun i ↦ (refs i).castSucc)

private theorem eval_extendReferences {m n : Nat} (refs : Fin m → Fin n) (gate : Gate m)
    (bits : Fin n → Bool) :
    (mapGate refs gate).extend bits ∘ extendReferences refs = gate.extend (bits ∘ refs) := by
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp [Function.comp_def, extendReferences, eval_mapGate]
  · simp [Function.comp_def, extendReferences]

/-- Rewiring the inputs preserves gate count, even when different inputs share a wire. -/
private structure Rewired {m k : Nat} (original : Network m k) (n : Nat)
    (refs : Fin m → Fin n) where
  wires : Nat
  network : Network n wires
  outputMap : Fin k → Fin wires
  eval_output : ∀ bits i, network.eval bits (outputMap i) = original.eval (bits ∘ refs) i
  size_eq : network.size = original.size

private def rewireNetwork : {m k : Nat} → (network : Network m k) → {n : Nat} →
    (refs : Fin m → Fin n) → Rewired network n refs
  | _, _, .empty _, n, refs =>
    ⟨n, .empty n, refs, fun _ _ ↦ rfl, rfl⟩
  | _, _, .cons gate rest, _, refs =>
    let a := rewireNetwork rest (extendReferences refs)
    { wires := a.wires
      network := .cons (mapGate refs gate) a.network
      outputMap := a.outputMap
      eval_output := by
        intro bits i
        simp only [Network.eval]
        rw [a.eval_output, eval_extendReferences]
      size_eq := by
        simp only [Network.size, a.size_eq] }

/-- A topologically ordered Boolean circuit with `n` inputs and one output. -/
structure BooleanCircuit (n : Nat) where
  wires : Nat
  network : Network n wires
  output : Fin wires

namespace BooleanCircuit

variable {n : Nat}

@[expose] def eval (circuit : BooleanCircuit n) (bits : Fin n → Bool) : Bool :=
  circuit.network.eval bits circuit.output

@[expose] def size (circuit : BooleanCircuit n) : Nat := circuit.network.size

/-- A circuit with one constant gate. -/
@[expose] def const (n : Nat) (value : Bool) : BooleanCircuit n :=
  ⟨n + 1, (.empty n : Network n n).push (.const value), Fin.last n⟩

@[simp] theorem eval_const (n : Nat) (value : Bool) (bits : Fin n → Bool) :
    (const n value).eval bits = value :=
  Network.eval_push_last (.empty n) (.const value) bits

@[simp] theorem size_const (n : Nat) (value : Bool) : (const n value).size = 1 := rfl

/-- A circuit reading only an existing input wire. -/
@[expose] def input (i : Fin n) : BooleanCircuit n := ⟨n, .empty n, i⟩

@[simp] theorem eval_input (i : Fin n) (bits : Fin n → Bool) : (input i).eval bits = bits i := rfl

@[simp] theorem size_input (i : Fin n) : (input i).size = 0 := rfl

/-- Add a NOT gate at the output. -/
def not (circuit : BooleanCircuit n) : BooleanCircuit n :=
  ⟨circuit.wires + 1, circuit.network.push (.not circuit.output), Fin.last circuit.wires⟩

@[simp] theorem eval_not (circuit : BooleanCircuit n) (bits : Fin n → Bool) :
    circuit.not.eval bits = !(circuit.eval bits) :=
  Network.eval_push_last circuit.network (.not circuit.output) bits

@[simp] theorem size_not (circuit : BooleanCircuit n) : circuit.not.size = circuit.size + 1 :=
  Network.size_push circuit.network (.not circuit.output)

/-- Substitute references for the input wires, retaining the gate sequence's size. -/
def mapInputs {m : Nat} (circuit : BooleanCircuit m) (refs : Fin m → Fin n) : BooleanCircuit n :=
  let a := rewireNetwork circuit.network refs
  ⟨a.wires, a.network, a.outputMap circuit.output⟩

@[simp] theorem eval_mapInputs {m : Nat} (circuit : BooleanCircuit m) (refs : Fin m → Fin n)
    (bits : Fin n → Bool) : (circuit.mapInputs refs).eval bits = circuit.eval (bits ∘ refs) :=
  (rewireNetwork circuit.network refs).eval_output bits circuit.output

@[simp] theorem size_mapInputs {m : Nat} (circuit : BooleanCircuit m) (refs : Fin m → Fin n) :
    (circuit.mapInputs refs).size = circuit.size :=
  (rewireNetwork circuit.network refs).size_eq

/-- Combine two circuits with common inputs and one new binary gate. -/
def binary (op : BinaryOp) (left right : BooleanCircuit n) : BooleanCircuit n :=
  let next := right.mapInputs (fun i ↦ i.castLE left.network.wires_le)
  let gate := Gate.binary op (left.output.castLE next.network.wires_le) next.output
  ⟨next.wires + 1, (left.network.append next.network).push gate, Fin.last next.wires⟩

@[simp] theorem eval_binary (op : BinaryOp) (left right : BooleanCircuit n) (bits : Fin n → Bool) :
    (binary op left right).eval bits = op.eval (left.eval bits) (right.eval bits) := by
  let refs := fun i ↦ Fin.castLE left.network.wires_le i
  let next := right.mapInputs refs
  change ((left.network.append next.network).push
    (.binary op (left.output.castLE next.network.wires_le) next.output)).eval bits
      (Fin.last next.wires) = _
  rw [Network.eval_push_last, Network.eval_append]
  simp only [Gate.eval, Network.eval_castLE]
  change op.eval (left.eval bits) (next.eval (left.network.eval bits)) = _
  rw [eval_mapInputs]
  have hWires : left.network.eval bits ∘ refs = bits := funext (left.network.eval_castLE bits)
  rw [hWires]

@[simp] theorem size_binary (op : BinaryOp) (left right : BooleanCircuit n) :
    (binary op left right).size = left.size + right.size + 1 := by
  let next := right.mapInputs (fun i ↦ i.castLE left.network.wires_le)
  change ((left.network.append next.network).push _).size = _
  rw [Network.size_push, Network.size_append]
  exact congrArg (fun added ↦ left.size + added + 1) (size_mapInputs right _)

/-- Disjoin the outputs of circuits on the same inputs. The empty list rejects. -/
def orList : List (BooleanCircuit n) → BooleanCircuit n
  | [] => .const n false
  | c :: cs => .binary .or c (orList cs)

theorem eval_orList_eq_true (cs : List (BooleanCircuit n)) (bits : Fin n → Bool) :
    (orList cs).eval bits = true ↔ ∃ c ∈ cs, c.eval bits = true := by
  induction cs with
  | nil => simp [orList]
  | cons c cs ih => simp [orList, BinaryOp.eval, ih]

theorem size_orList_le (cs : List (BooleanCircuit n)) (K : Nat)
    (h : ∀ c ∈ cs, c.size ≤ K) : (orList cs).size ≤ cs.length * (K + 1) + 1 := by
  induction cs with
  | nil => simp [orList]
  | cons c cs ih =>
    have hc := h c (List.mem_cons_self ..)
    have ht := ih (fun d hd ↦ h d (List.mem_cons_of_mem _ hd))
    simp only [orList, size_binary, List.length_cons, Nat.succ_mul]
    omega

end BooleanCircuit

/-- A topologically ordered Boolean circuit selecting several wires as outputs. -/
structure MultiCircuit (n m : Nat) where
  wires : Nat
  network : Network n wires
  output : Fin m → Fin wires

namespace MultiCircuit

variable {n m : Nat}

@[expose] def eval (circuit : MultiCircuit n m) (bits : Fin n → Bool) : Fin m → Bool :=
  circuit.network.eval bits ∘ circuit.output

@[expose] def size (circuit : MultiCircuit n m) : Nat := circuit.network.size

/-- Feed a multi-output circuit's result wires to a single-output circuit. -/
def thenBoolean (before : MultiCircuit n m) (after : BooleanCircuit m) : BooleanCircuit n :=
  let next := after.mapInputs before.output
  ⟨next.wires, before.network.append next.network, next.output⟩

@[simp] theorem eval_thenBoolean (before : MultiCircuit n m) (after : BooleanCircuit m)
    (bits : Fin n → Bool) : (before.thenBoolean after).eval bits = after.eval (before.eval bits) := by
  let next := after.mapInputs before.output
  change (before.network.append next.network).eval bits next.output = _
  rw [Network.eval_append]
  exact BooleanCircuit.eval_mapInputs after before.output (before.network.eval bits)

@[simp] theorem size_thenBoolean (before : MultiCircuit n m) (after : BooleanCircuit m) :
    (before.thenBoolean after).size = before.size + after.size := by
  let next := after.mapInputs before.output
  change (before.network.append next.network).size = _
  rw [Network.size_append]
  exact congrArg (before.size + ·) (BooleanCircuit.size_mapInputs after before.output)

/-- Evaluate one more circuit on the current output wires, keeping those wires
and adding its result as the last output. -/
def pushOutput (before : MultiCircuit n m) (after : BooleanCircuit m) : MultiCircuit n (m + 1) :=
  let next := after.mapInputs before.output
  ⟨next.wires, before.network.append next.network,
    Fin.lastCases next.output (fun i ↦ (before.output i).castLE next.network.wires_le)⟩

@[simp] theorem eval_pushOutput_castSucc (before : MultiCircuit n m) (after : BooleanCircuit m)
    (bits : Fin n → Bool) (i : Fin m) :
    (before.pushOutput after).eval bits i.castSucc = before.eval bits i := by
  let next := after.mapInputs before.output
  change (before.network.append next.network).eval bits
    (Fin.lastCases next.output (fun j ↦ (before.output j).castLE next.network.wires_le) i.castSucc)
      = before.eval bits i
  simp only [Fin.lastCases_castSucc, Network.eval_append, Network.eval_castLE, eval,
    Function.comp_apply]

@[simp] theorem eval_pushOutput_last (before : MultiCircuit n m) (after : BooleanCircuit m)
    (bits : Fin n → Bool) :
    (before.pushOutput after).eval bits (Fin.last m) = after.eval (before.eval bits) := by
  let next := after.mapInputs before.output
  change (before.network.append next.network).eval bits (Fin.lastCases next.output
      (fun i ↦ (before.output i).castLE next.network.wires_le) (Fin.last m)) = _
  rw [Fin.lastCases_last]
  exact eval_thenBoolean before after bits

@[simp] theorem size_pushOutput (before : MultiCircuit n m) (after : BooleanCircuit m) :
    (before.pushOutput after).size = before.size + after.size :=
  size_thenBoolean before after

end MultiCircuit

/-- A gate sequence and its selected result wires, with a specification and gate budget. -/
private structure Lowering (n : Nat) (α : Type) (compute : (Fin n → Bool) → α → Bool)
    (budget : Nat) where
  wires : Nat
  network : Network n wires
  output : α → Fin wires
  eval_output : ∀ bits i, network.eval bits (output i) = compute bits i
  size_le : network.size ≤ budget

private def lowerBinary {α : Type} {n : Nat} (op : BinaryOp) (l r : Expr α)
    (refs : α → Fin n)
    (a : Lowering n Unit (fun x _ ↦ l.eval (x ∘ refs)) l.size)
    (b : Lowering a.wires Unit
      (fun x _ ↦ r.eval (fun i ↦ x ((refs i).castLE a.network.wires_le))) r.size) :
    Lowering n Unit (fun x _ ↦ op.eval (l.eval (x ∘ refs)) (r.eval (x ∘ refs)))
      (l.size + r.size + 1) where
  wires := b.wires + 1
  network := (a.network.append b.network).push
    (.binary op ((a.output ()).castLE b.network.wires_le) (b.output ()))
  output := fun _ ↦ Fin.last b.wires
  eval_output := by
    intro bits _
    rw [Network.eval_push_last, Network.eval_append]
    change op.eval (b.network.eval (a.network.eval bits)
      ((a.output ()).castLE b.network.wires_le)) (b.network.eval (a.network.eval bits) (b.output ())) = _
    rw [Network.eval_castLE, a.eval_output, b.eval_output]
    simp only [Network.eval_castLE, Function.comp_def]
  size_le := by
    rw [Network.size_push, Network.size_append]
    exact Nat.add_le_add_right (Nat.add_le_add a.size_le b.size_le) 1

private def lowerExpr {α : Type} : {n : Nat} → (e : Expr α) → (refs : α → Fin n) →
    Lowering n Unit (fun x _ ↦ e.eval (x ∘ refs)) e.size
  | n, .const value, _ =>
    { wires := n + 1
      network := (.empty n : Network n n).push (.const value)
      output := fun _ ↦ Fin.last n
      eval_output := fun bits _ ↦ Network.eval_push_last (.empty n) (.const value) bits
      size_le := by rw [Network.size_push]; exact Nat.le_refl 1 }
  | n, .input i, refs =>
    { wires := n
      network := .empty n
      output := fun _ ↦ refs i
      eval_output := fun _ _ ↦ rfl
      size_le := Nat.zero_le 1 }
  | _, .not e, refs =>
    let a := lowerExpr e refs
    { wires := a.wires + 1
      network := a.network.push (.not (a.output ()))
      output := fun _ ↦ Fin.last a.wires
      eval_output := by
        intro bits _
        rw [Network.eval_push_last]
        exact congrArg Bool.not (a.eval_output bits ())
      size_le := by
        rw [Network.size_push]
        exact Nat.add_le_add_right a.size_le 1 }
  | _, .and l r, refs =>
    let a := lowerExpr l refs
    lowerBinary .and l r refs a (lowerExpr r (fun i ↦ (refs i).castLE a.network.wires_le))
  | _, .or l r, refs =>
    let a := lowerExpr l refs
    lowerBinary .or l r refs a (lowerExpr r (fun i ↦ (refs i).castLE a.network.wires_le))

private def lowerList {α : Type} : {n : Nat} → (es : List (Expr α)) → (refs : α → Fin n) →
    Lowering n (Fin es.length) (fun x i ↦ es[i.val].eval (x ∘ refs)) (es.map Expr.size).sum
  | n, [], _ =>
    { wires := n
      network := .empty n
      output := Fin.elim0
      eval_output := fun _ i ↦ i.elim0
      size_le := Nat.le_refl 0 }
  | _, e :: es, refs =>
    let a := lowerExpr e refs
    let b := lowerList es (fun j ↦ (refs j).castLE a.network.wires_le)
    { wires := b.wires
      network := a.network.append b.network
      output := Fin.cases ((a.output ()).castLE b.network.wires_le) b.output
      eval_output := by
        intro bits i
        rw [Network.eval_append]
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · simp only [Fin.cases_zero, Network.eval_castLE]
          exact a.eval_output bits ()
        · simp only [Fin.cases_succ]
          rw [b.eval_output]
          simp only [Network.eval_castLE, Function.comp_def]
          rfl
      size_le := by
        rw [Network.size_append]
        exact Nat.add_le_add a.size_le b.size_le }

private def lowerLayer {m k n : Nat} (layer : Layer m k) (refs : Fin m → Fin n) :
    Lowering n (Fin k) (fun x i ↦ layer.eval (x ∘ refs) i) layer.size :=
  let es := (List.finRange k).map layer
  let a := lowerList es refs
  have hLength : k = es.length := by simp [es]
  { wires := a.wires
    network := a.network
    output := fun i ↦ a.output (i.cast hLength)
    eval_output := by
      intro bits i
      rw [a.eval_output]
      simp [es, Layer.eval]
    size_le := by simpa [es, Layer.size, Function.comp_def] using a.size_le }

private def lowerLayered : {m k n : Nat} → (layered : Layered m k) → (refs : Fin m → Fin n) →
    Lowering n (Fin k) (fun x i ↦ layered.eval (x ∘ refs) i) layered.size
  | _, _, n, .id _, refs =>
    { wires := n
      network := .empty n
      output := refs
      eval_output := fun _ _ ↦ rfl
      size_le := Nat.le_refl 0 }
  | _, _, _, .cons layer rest, refs =>
    let a := lowerLayer layer refs
    let b := lowerLayered rest a.output
    { wires := b.wires
      network := a.network.append b.network
      output := b.output
      eval_output := by
        intro bits i
        rw [Network.eval_append, b.eval_output]
        have hInput : a.network.eval bits ∘ a.output = layer.eval (bits ∘ refs) :=
          funext (a.eval_output bits)
        rw [hInput]
        rfl
      size_le := by
        rw [Network.size_append]
        exact Nat.add_le_add a.size_le b.size_le }

namespace Layered

variable {n m : Nat}

/-- Flatten the layers once and retain all selected output wires. -/
def toMultiCircuit (layered : Layered n m) : MultiCircuit n m :=
  let a := lowerLayered layered (fun i ↦ i)
  ⟨a.wires, a.network, a.output⟩

theorem eval_toMultiCircuit (layered : Layered n m) (x : Fin n → Bool) :
    layered.toMultiCircuit.eval x = layered.eval x :=
  funext ((lowerLayered layered (fun i ↦ i)).eval_output x)

theorem size_toMultiCircuit_le (layered : Layered n m) :
    layered.toMultiCircuit.size ≤ layered.size :=
  (lowerLayered layered (fun i ↦ i)).size_le

/-- Flatten the layered circuit and select a single output wire. -/
def toBooleanCircuit (layered : Layered n m) (out : Fin m) : BooleanCircuit n :=
  let a := layered.toMultiCircuit
  ⟨a.wires, a.network, a.output out⟩

/-- Flattening retains the value of the selected wire. -/
theorem eval_toBooleanCircuit (layered : Layered n m) (out : Fin m) (x : Fin n → Bool) :
    (layered.toBooleanCircuit out).eval x = layered.eval x out :=
  (lowerLayered layered (fun i ↦ i)).eval_output x out

/-- Flattening introduces at most one gate per expression node. -/
theorem size_toBooleanCircuit_le (layered : Layered n m) (out : Fin m) :
    (layered.toBooleanCircuit out).size ≤ layered.size :=
  (lowerLayered layered (fun i ↦ i)).size_le

end Layered

end PvsNP.Circuits
