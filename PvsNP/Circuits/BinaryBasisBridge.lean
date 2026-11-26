module

public import PvsNP.Circuits.BinaryBasis

/-! # Simulate arbitrary Boolean gates with AND, OR, and NOT -/

public section

namespace PvsNP.Circuits

variable {n m k : Nat}

private def lowerBinaryFunction (op : BinaryFunction) (i j : Fin n) : BooleanCircuit n :=
  let x := BooleanCircuit.input i
  let y := BooleanCircuit.input j
  let both := BooleanCircuit.binary .and x y
  let either := BooleanCircuit.binary .or x y
  match op false false, op false true, op true false, op true true with
  | false, false, false, false => .const n false
  | false, false, false, true => both
  | false, false, true, false => .binary .and x y.not
  | false, false, true, true => x
  | false, true, false, false => .binary .and x.not y
  | false, true, false, true => y
  | false, true, true, false => .binary .and either both.not
  | false, true, true, true => either
  | true, false, false, false => either.not
  | true, false, false, true => .binary .or both either.not
  | true, false, true, false => y.not
  | true, false, true, true => .binary .or x y.not
  | true, true, false, false => x.not
  | true, true, false, true => .binary .or x.not y
  | true, true, true, false => both.not
  | true, true, true, true => .const n true

private theorem eval_lowerBinaryFunction (op : BinaryFunction) (i j : Fin n)
    (bits : Fin n → Bool) : (lowerBinaryFunction op i j).eval bits = op (bits i) (bits j) := by
  cases h00 : op false false <;> cases h01 : op false true <;>
    cases h10 : op true false <;> cases h11 : op true true <;>
    cases hi : bits i <;> cases hj : bits j <;>
    simp [lowerBinaryFunction, h00, h01, h10, h11, hi, hj, BinaryOp.eval]

private theorem size_lowerBinaryFunction_le (op : BinaryFunction) (i j : Fin n) :
    (lowerBinaryFunction op i j).size ≤ 4 := by
  cases h00 : op false false <;> cases h01 : op false true <;>
    cases h10 : op true false <;> cases h11 : op true true <;>
    simp [lowerBinaryFunction, h00, h01, h10, h11]

private def lowerGate (gate : Gate n) (op : BinaryFunction) : BooleanCircuit n :=
  match gate with
  | .const value => BooleanCircuit.const n value
  | .not src => (BooleanCircuit.input src).not
  | .binary _ i j => lowerBinaryFunction op i j

private theorem eval_lowerGate (gate : Gate n) (op : BinaryFunction) (bits : Fin n → Bool) :
    (lowerGate gate op).eval bits = gate.evalWith op bits := by
  cases gate <;> simp [lowerGate, Gate.evalWith, eval_lowerBinaryFunction]

private theorem size_lowerGate_le (gate : Gate n) (op : BinaryFunction) :
    (lowerGate gate op).size ≤ 4 := by
  cases gate with
  | const => simp [lowerGate]
  | not => simp [lowerGate]
  | binary _ i j => exact size_lowerBinaryFunction_le op i j

private def lowerFrom {k : Nat} : {n m : Nat} → (network : Network n m) →
    network.BinaryFunctions → MultiCircuit k n → MultiCircuit k m
  | _, _, .empty _, _, before => before
  | _, _, .cons gate rest, ops, before =>
    lowerFrom rest ops.2 (before.pushOutput (lowerGate gate ops.1))

private theorem eval_lowerFrom (network : Network n m) (ops : network.BinaryFunctions)
    (before : MultiCircuit k n) (bits : Fin k → Bool) :
    (lowerFrom network ops before).eval bits = network.evalWith ops (before.eval bits) := by
  induction network with
  | empty => rfl
  | cons gate rest ih =>
    change (lowerFrom rest ops.2 (before.pushOutput (lowerGate gate ops.1))).eval bits =
      rest.evalWith ops.2 (gate.extendWith ops.1 (before.eval bits))
    refine (ih ops.2 _).trans (congrArg (rest.evalWith ops.2) ?_)
    funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp only [MultiCircuit.eval_pushOutput_last, Gate.extendWith_last, eval_lowerGate]
    · simp only [MultiCircuit.eval_pushOutput_castSucc, Gate.extendWith_castSucc]

private theorem size_lowerFrom_le (network : Network n m) (ops : network.BinaryFunctions)
    (before : MultiCircuit k n) :
    (lowerFrom network ops before).size ≤ before.size + 4 * network.size := by
  induction network with
  | empty => simp [lowerFrom, Network.size]
  | cons gate rest ih =>
    have hRest := ih ops.2 (before.pushOutput (lowerGate gate ops.1))
    have hGate := size_lowerGate_le gate ops.1
    rw [MultiCircuit.size_pushOutput] at hRest
    change (lowerFrom rest ops.2 (before.pushOutput (lowerGate gate ops.1))).size ≤ _
    simp only [Network.size]
    omega

private def initial (n : Nat) : MultiCircuit n n := ⟨n, .empty n, id⟩

namespace BinaryBasisCircuit

/-- Replace each binary gate using its truth table, retaining every output for reuse. -/
def toBooleanCircuit (circuit : BinaryBasisCircuit n) : BooleanCircuit n :=
  let a := lowerFrom circuit.topology.network circuit.operations (initial n)
  ⟨a.wires, a.network, a.output circuit.topology.output⟩

@[simp] theorem eval_toBooleanCircuit (circuit : BinaryBasisCircuit n) (bits : Fin n → Bool) :
    circuit.toBooleanCircuit.eval bits = circuit.eval bits := by
  change (lowerFrom circuit.topology.network circuit.operations (initial n)).eval bits
    circuit.topology.output = _
  rw [eval_lowerFrom]
  rfl

theorem size_toBooleanCircuit_le (circuit : BinaryBasisCircuit n) :
    circuit.toBooleanCircuit.size ≤ 4 * circuit.size := by
  have h := size_lowerFrom_le circuit.topology.network circuit.operations (initial n)
  change (lowerFrom circuit.topology.network circuit.operations (initial n)).size ≤ _
  simpa only [initial, MultiCircuit.size, Network.size, Nat.zero_add,
    BinaryBasisCircuit.size, BooleanCircuit.size] using h

end BinaryBasisCircuit

end PvsNP.Circuits
