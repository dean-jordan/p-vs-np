module

public import PvsNP.Circuits.Description
public import PvsNP.Circuits.ToCNF
public import PvsNP.SAT.Assignment

import Init.Data.List.Nat.TakeDrop

/-! # Local checking of a circuit's wire values -/

public section

namespace PvsNP.Circuits

open SATAssignment (lookup)

/-- Each instruction writes the next wire and may read only earlier wires. -/
inductive WireTraceInstruction where
  | const (value : Bool)
  | not (source : Nat)
  | binary (op : BinaryOp) (left right : Nat)

namespace WireTraceInstruction

/-- Missing bits and references at or beyond the destination both fail. -/
@[expose] def readEarlier (trace : BinaryWord) (destination source : Nat) : Option Bool :=
  if source < destination then (trace)[source]? else none

@[expose] def expected (instruction : WireTraceInstruction) (destination : Nat)
    (trace : BinaryWord) : Option Bool :=
  match instruction with
  | .const b => some b
  | .not i => (readEarlier trace destination i).map (!·)
  | .binary op l r => do
    let a ← readEarlier trace destination l
    let b ← readEarlier trace destination r
    return op.eval a b

@[expose] def checkAt (instruction : WireTraceInstruction) (destination : Nat)
    (trace : BinaryWord) : Bool :=
  match (trace)[destination]?, instruction.expected destination trace with
  | some actual, some value => actual == value
  | _, _ => false

theorem checkAt_eq_true_iff (instruction : WireTraceInstruction) (destination : Nat)
    (trace : BinaryWord) : instruction.checkAt destination trace = true ↔
      ∃ b, instruction.expected destination trace = some b ∧ (trace)[destination]? = some b := by
  cases ha : (trace)[destination]? <;> cases hv : instruction.expected destination trace <;>
    simp [checkAt, ha, hv]

end WireTraceInstruction

/-- Check the flat instructions in order, then reject any extra trace bits. -/
@[expose] def checkWireTraceFrom : Nat → List WireTraceInstruction → BinaryWord → Bool
  | destination, [], trace => decide (trace.length = destination)
  | destination, op :: rest, trace =>
    op.checkAt destination trace && checkWireTraceFrom (destination + 1) rest trace

theorem length_of_checkWireTraceFrom_eq_true (destination : Nat)
    (ops : List WireTraceInstruction) (trace : BinaryWord)
    (h : checkWireTraceFrom destination ops trace = true) :
    trace.length = destination + ops.length := by
  induction ops generalizing destination with
  | nil => simpa [checkWireTraceFrom] using h
  | cons op rest ih =>
    have hBoth : op.checkAt destination trace = true ∧
        checkWireTraceFrom (destination + 1) rest trace = true := by
      simpa only [checkWireTraceFrom, Bool.and_eq_true] using h
    have hTail := hBoth.2
    have hLength := ih (destination + 1) hTail
    simp only [List.length_cons]
    omega

variable {n m : Nat}

namespace Gate

@[expose] def traceInstruction (gate : Gate n) : WireTraceInstruction :=
  match gate with
  | .const value => .const value
  | .not src => .not src.val
  | .binary op l r => .binary op l.val r.val

private theorem some_lookup (trace : BinaryWord) (i : Nat) (hi : i < trace.length) :
    (trace)[i]? = some (lookup trace i) := by
  simp [lookup, List.getElem?_eq_getElem hi]

private theorem readEarlier_fin (trace : BinaryWord) (i : Fin n) (h : n < trace.length) :
    WireTraceInstruction.readEarlier trace n i.val = some (lookup trace i.val) := by
  rw [WireTraceInstruction.readEarlier, ite_eq_left i.isLt]
  exact some_lookup trace i.val (i.isLt.trans h)

theorem expected_traceInstruction (gate : Gate n) (trace : BinaryWord)
    (h : n < trace.length) : gate.traceInstruction.expected n trace =
      some (gate.eval (fun i ↦ lookup trace i.val)) := by
  cases gate with
  | const b => rfl
  | not i => simp [traceInstruction, WireTraceInstruction.expected, readEarlier_fin _ i h, eval]
  | binary op l r =>
    simp [traceInstruction, WireTraceInstruction.expected,
      readEarlier_fin _ l h, readEarlier_fin _ r h, eval]

theorem checkTraceInstruction_eq_true_iff (gate : Gate n) (trace : BinaryWord)
    (h : n < trace.length) : gate.traceInstruction.checkAt n trace = true ↔
      CNF.Sat (lookup trace) (CNF.mapAtoms Fin.val gate.constraints) := by
  rw [WireTraceInstruction.checkAt, some_lookup trace n h, expected_traceInstruction gate trace h,
    CNF.sat_mapAtoms, gate.sat_constraints_iff]
  exact beq_iff_eq

end Gate

namespace Network

@[expose] def traceInstructions : {n m : Nat} → Network n m → List WireTraceInstruction
  | _, _, .empty _ => []
  | _, _, .cons gate rest => gate.traceInstruction :: rest.traceInstructions

@[simp] theorem length_traceInstructions (network : Network n m) :
    network.traceInstructions.length = network.size := by
  induction network with
  | empty => rfl
  | cons gate rest ih => simp [traceInstructions, size, ih, Nat.add_comm]

/-- On a well-formed network, the flat checker verifies the same local constraints as CNF. -/
theorem checkWireTraceFrom_network_iff (network : Network n m) (trace : BinaryWord) :
    checkWireTraceFrom n network.traceInstructions trace = true ↔
      trace.length = m ∧ CNF.Sat (lookup trace) network.constraints := by
  induction network with
  | empty => simp [traceInstructions, checkWireTraceFrom, constraints]
  | @cons n m gate rest ih =>
    simp only [traceInstructions, checkWireTraceFrom, Bool.and_eq_true, ih,
      constraints, CNF.sat_append]
    constructor
    · rintro ⟨hGate, hLength, hRest⟩
      have hDst : n < trace.length := hLength ▸ Nat.lt_of_succ_le rest.wires_le
      exact ⟨hLength, (gate.checkTraceInstruction_eq_true_iff trace hDst).mp hGate, hRest⟩
    · rintro ⟨hLength, hGate, hRest⟩
      have hDst : n < trace.length := hLength ▸ Nat.lt_of_succ_le rest.wires_le
      exact ⟨(gate.checkTraceInstruction_eq_true_iff trace hDst).mpr hGate, hLength, hRest⟩

end Network

namespace BooleanCircuit

/-- The unique trace lists the inputs followed by the gate outputs. -/
@[expose] def wireTrace (circuit : BooleanCircuit n) (bits : Fin n → Bool) : BinaryWord :=
  List.ofFn (circuit.network.eval bits)

@[simp] theorem length_wireTrace (circuit : BooleanCircuit n) (bits : Fin n → Bool) :
    (circuit.wireTrace bits).length = n + circuit.size :=
  List.length_ofFn.trans circuit.network.wires_eq_input_add_size

@[expose] def checkWireTrace (circuit : BooleanCircuit n) (bits : Fin n → Bool)
    (trace : BinaryWord) (answer : Bool) : Bool :=
  (trace.take n == List.ofFn bits) &&
    (checkWireTraceFrom n circuit.network.traceInstructions trace &&
      ((trace)[circuit.output.val]? == some answer))

private theorem lookup_of_trace_prefix {trace : BinaryWord} {bits : Fin n → Bool}
    (h : trace.take n = List.ofFn bits) : (fun i : Fin n ↦ lookup trace i.val) = bits := by
  funext i
  have hTake := List.getElem?_take_of_lt (l := trace) i.isLt
  rw [h] at hTake
  simp only [List.getElem?_ofFn, dite_eq_left i.isLt] at hTake
  simp [lookup, ← hTake]

private theorem take_wireTrace (circuit : BooleanCircuit n) (bits : Fin n → Bool) :
    (circuit.wireTrace bits).take n = List.ofFn bits := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < n
  · have hw := hi.trans_le circuit.network.wires_le
    simp only [wireTrace, List.getElem?_take_of_lt hi, List.getElem?_ofFn,
      dite_eq_left hi, dite_eq_left hw, Option.some.injEq]
    exact circuit.network.eval_castLE bits ⟨i, hi⟩
  · simp [hi]

/-- A trace passes exactly when all its wire values and its claimed answer are correct. -/
theorem checkWireTrace_eq_true_iff (circuit : BooleanCircuit n) (bits : Fin n → Bool)
    (trace : BinaryWord) (answer : Bool) : circuit.checkWireTrace bits trace answer = true ↔
      trace = circuit.wireTrace bits ∧ circuit.eval bits = answer := by
  simp only [checkWireTrace, Bool.and_eq_true, beq_iff_eq,
    circuit.network.checkWireTraceFrom_network_iff]
  constructor
  · rintro ⟨hPrefix, ⟨hLength, hConstraints⟩, hOutput⟩
    have hValues := (circuit.network.sat_constraints_iff_eval (lookup trace)).mp hConstraints
    rw [lookup_of_trace_prefix hPrefix] at hValues
    have hTrace : trace = circuit.wireTrace bits := by
      apply List.ext_getElem
      · simpa only [wireTrace, List.length_ofFn] using hLength
      · intro i hi hi'
        have hw : i < circuit.wires := by simpa only [wireTrace, List.length_ofFn] using hi'
        simpa only [wireTrace, List.getElem_ofFn, lookup,
          List.getElem?_eq_getElem hi, Option.getD_some] using hValues ⟨i, hw⟩
    refine ⟨hTrace, ?_⟩
    simpa only [hTrace, wireTrace, List.getElem?_ofFn, dite_eq_left circuit.output.isLt,
      Option.some.injEq, eval] using hOutput
  · rintro ⟨rfl, hOutput⟩
    have hPrefix := take_wireTrace circuit bits
    have hValues (i : Fin circuit.wires) :
        lookup (circuit.wireTrace bits) i.val = circuit.network.eval bits i := by
      simp [wireTrace, lookup, i.isLt]
    have hConstraints : CNF.Sat (lookup (circuit.wireTrace bits)) circuit.network.constraints := by
      apply (circuit.network.sat_constraints_iff_eval _).mpr
      rw [lookup_of_trace_prefix hPrefix]
      exact hValues
    refine ⟨hPrefix, ⟨List.length_ofFn, hConstraints⟩, ?_⟩
    simpa only [wireTrace, List.getElem?_ofFn, dite_eq_left circuit.output.isLt,
      Option.some.injEq, eval] using hOutput

end BooleanCircuit

/-- Check a fixed-width circuit description, the input row, and the proposed wire values. -/
@[expose] def checkCodedWireTrace (n cap : Nat) (code row trace : BinaryWord)
    (answer : Bool) : Bool :=
  if row.length = n then
    match decodeCircuit n cap code with
    | none => false
    | some circuit => circuit.checkWireTrace (fun i ↦ lookup row i.val) trace answer
  else false

theorem checkCodedWireTrace_eq_true_iff (n cap : Nat) (code row trace : BinaryWord)
    (answer : Bool) : checkCodedWireTrace n cap code row trace answer = true ↔
      row.length = n ∧ ∃ circuit : BooleanCircuit n, decodeCircuit n cap code = some circuit ∧
        trace = circuit.wireTrace (fun i ↦ lookup row i.val) ∧
        circuit.eval (fun i ↦ lookup row i.val) = answer := by
  by_cases hRow : row.length = n
  · cases hCode : decodeCircuit n cap code with
    | none => simp [checkCodedWireTrace, hRow, hCode]
    | some circuit => simp [checkCodedWireTrace, hRow, hCode, circuit.checkWireTrace_eq_true_iff]
  · simp [checkCodedWireTrace, hRow]

theorem exists_codedWireTrace_iff (n cap : Nat) (code row : BinaryWord) (answer : Bool) :
    (∃ trace : BinaryWord, trace.length ≤ n + cap ∧
      checkCodedWireTrace n cap code row trace answer = true) ↔
      row.length = n ∧ ∃ circuit : BooleanCircuit n, decodeCircuit n cap code = some circuit ∧
        circuit.eval (fun i ↦ lookup row i.val) = answer := by
  constructor
  · rintro ⟨trace, _, hTrace⟩
    obtain ⟨hRow, circuit, hCode, _, hAnswer⟩ :=
      (checkCodedWireTrace_eq_true_iff n cap code row trace answer).mp hTrace
    exact ⟨hRow, circuit, hCode, hAnswer⟩
  · rintro ⟨hRow, circuit, hCode, hAnswer⟩
    let trace := circuit.wireTrace (fun i ↦ lookup row i.val)
    refine ⟨trace, ?_, (checkCodedWireTrace_eq_true_iff n cap code row trace answer).mpr
      ⟨hRow, circuit, hCode, rfl, hAnswer⟩⟩
    rw [BooleanCircuit.length_wireTrace]
    exact Nat.add_le_add_left (size_le_of_decodeCircuit_eq_some hCode) n

end PvsNP.Circuits
