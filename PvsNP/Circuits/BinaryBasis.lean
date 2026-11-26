module

public import PvsNP.Circuits.ParitySupport

/-! # Arbitrary binary gates on the same circuit topology -/

public section

namespace PvsNP.Circuits

abbrev BinaryFunction := Bool → Bool → Bool

variable {n m : Nat}

namespace Gate

@[expose] def evalWith (gate : Gate n) (op : BinaryFunction) (bits : Fin n → Bool) : Bool :=
  match gate with
  | .const value => value
  | .not src => !(bits src)
  | .binary _ left right => op (bits left) (bits right)

@[expose] def extendWith (gate : Gate n) (op : BinaryFunction) (bits : Fin n → Bool) :
    Fin (n + 1) → Bool :=
  Fin.lastCases (gate.evalWith op bits) bits

@[simp] theorem extendWith_last (gate : Gate n) (op : BinaryFunction) (bits : Fin n → Bool) :
    gate.extendWith op bits (Fin.last n) = gate.evalWith op bits := by
  simp [extendWith]

@[simp] theorem extendWith_castSucc (gate : Gate n) (op : BinaryFunction)
    (bits : Fin n → Bool) (i : Fin n) : gate.extendWith op bits i.castSucc = bits i := by
  simp [extendWith]

/-- Recover the operation on a binary gate. The other gates ignore this parameter. -/
@[expose] def standardBinaryFunction : Gate n → BinaryFunction
  | .binary op _ _ => op.eval
  | .const _ | .not _ => fun _ _ ↦ false

theorem evalWith_standardBinaryFunction (gate : Gate n) (bits : Fin n → Bool) :
    gate.evalWith gate.standardBinaryFunction bits = gate.eval bits := by
  cases gate <;> rfl

theorem extendWith_standardBinaryFunction (gate : Gate n) (bits : Fin n → Bool) :
    gate.extendWith gate.standardBinaryFunction bits = gate.extend bits := by
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · rw [extendWith_last, extend_last, evalWith_standardBinaryFunction]
  · rw [extendWith_castSucc, extend_castSucc]

end Gate

theorem gate_evalWith_eq_of_agree (gate : Gate n) (op : BinaryFunction) (x y : Fin n → Bool)
    (agree : ∀ i ∈ gateInputs gate, x i = y i) : gate.evalWith op x = gate.evalWith op y := by
  cases gate with
  | const => rfl
  | not i =>
    exact congrArg Bool.not (agree i (by simp [gateInputs]))
  | binary _ i j =>
    simp only [Gate.evalWith]
    rw [agree i (by simp [gateInputs]), agree j (by simp [gateInputs])]

theorem extendWith_eq_of_agree (gate : Gate n) (op : BinaryFunction)
    (needed : Finset (Fin (n + 1))) (x y : Fin n → Bool)
    (agree : ∀ i ∈ previousSupport gate needed, x i = y i) :
    ∀ j ∈ needed, gate.extendWith op x j = gate.extendWith op y j := by
  intro j
  refine Fin.lastCases ?_ (fun i ↦ ?_) j
  · intro hLast
    rw [Gate.extendWith_last, Gate.extendWith_last]
    apply gate_evalWith_eq_of_agree
    intro i hi
    apply agree i
    exact Finset.mem_union_right _ (by simpa only [ite_eq_left hLast] using hi)
  · intro hi
    rw [Gate.extendWith_castSucc, Gate.extendWith_castSucc]
    apply agree i
    exact Finset.mem_union_left _ ((mem_oldWires_iff needed i).mpr hi)

namespace Network

/-- Supply a Boolean operation at each gate. A constant or inverter ignores it. -/
@[expose] def BinaryFunctions : {n m : Nat} → Network n m → Type
  | _, _, .empty _ => Unit
  | _, _, .cons _ rest => BinaryFunction × rest.BinaryFunctions

@[expose] def evalWith : {n m : Nat} → (network : Network n m) → network.BinaryFunctions →
    (Fin n → Bool) → Fin m → Bool
  | _, _, .empty _, _, bits => bits
  | _, _, .cons gate rest, ops, bits => rest.evalWith ops.2 (gate.extendWith ops.1 bits)

theorem evalWith_eq_of_agree_inputSupport (network : Network n m) (ops : network.BinaryFunctions)
    (needed : Finset (Fin m)) (x y : Fin n → Bool)
    (agree : ∀ i ∈ network.inputSupport needed, x i = y i) :
    ∀ j ∈ needed, network.evalWith ops x j = network.evalWith ops y j := by
  induction network with
  | empty => exact agree
  | cons gate rest ih =>
    exact ih ops.2 needed (gate.extendWith ops.1 x) (gate.extendWith ops.1 y)
      (extendWith_eq_of_agree gate ops.1 (rest.inputSupport needed) x y agree)

@[expose] def standardBinaryFunctions : {n m : Nat} → (network : Network n m) →
    network.BinaryFunctions
  | _, _, .empty _ => ()
  | _, _, .cons gate rest => (gate.standardBinaryFunction, rest.standardBinaryFunctions)

theorem evalWith_standardBinaryFunctions (network : Network n m) (bits : Fin n → Bool) :
    network.evalWith network.standardBinaryFunctions bits = network.eval bits := by
  induction network with
  | empty => rfl
  | cons gate rest ih =>
    change rest.evalWith rest.standardBinaryFunctions
        (gate.extendWith gate.standardBinaryFunction bits) =
      rest.eval (gate.extend bits)
    rw [Gate.extendWith_standardBinaryFunction]
    exact ih _

end Network

/-- A Boolean circuit whose binary gates may use any two-input Boolean function. -/
structure BinaryBasisCircuit (n : Nat) where
  topology : BooleanCircuit n
  operations : topology.network.BinaryFunctions

namespace BinaryBasisCircuit

@[expose] def eval (circuit : BinaryBasisCircuit n) (bits : Fin n → Bool) : Bool :=
  circuit.topology.network.evalWith circuit.operations bits circuit.topology.output

@[expose] def size (circuit : BinaryBasisCircuit n) : Nat := circuit.topology.size

@[expose] def binarySize (circuit : BinaryBasisCircuit n) : Nat := circuit.topology.binarySize

@[expose] def ofBooleanCircuit (circuit : BooleanCircuit n) : BinaryBasisCircuit n :=
  ⟨circuit, circuit.network.standardBinaryFunctions⟩

@[simp] theorem eval_ofBooleanCircuit (circuit : BooleanCircuit n) (bits : Fin n → Bool) :
    (ofBooleanCircuit circuit).eval bits = circuit.eval bits :=
  congrFun (circuit.network.evalWith_standardBinaryFunctions bits) circuit.output

@[simp] theorem size_ofBooleanCircuit (circuit : BooleanCircuit n) :
    (ofBooleanCircuit circuit).size = circuit.size := rfl

@[simp] theorem binarySize_ofBooleanCircuit (circuit : BooleanCircuit n) :
    (ofBooleanCircuit circuit).binarySize = circuit.binarySize := rfl

end BinaryBasisCircuit

end PvsNP.Circuits
