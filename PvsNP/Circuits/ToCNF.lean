module

public import PvsNP.Circuits.BooleanCircuit
public import PvsNP.SAT.BinaryLanguage

import PvsNP.Circuits.Enumerate

/-! # Tseitin encoding for Boolean circuit satisfiability -/

public section

namespace PvsNP.Circuits

variable {n m : Nat}

namespace Gate

/-- Constrain the last wire to carry the new gate's value. -/
@[expose] def constraints : Gate n → CNF.Formula (Fin (n + 1))
  | .const false => [[.neg (Fin.last n)]]
  | .const true => [[.pos (Fin.last n)]]
  | .not i => [[.pos (Fin.last n), .pos i.castSucc], [.neg (Fin.last n), .neg i.castSucc]]
  | .binary .and i j =>
    [[.neg (Fin.last n), .pos i.castSucc], [.neg (Fin.last n), .pos j.castSucc],
      [.pos (Fin.last n), .neg i.castSucc, .neg j.castSucc]]
  | .binary .or i j =>
    [[.pos (Fin.last n), .neg i.castSucc], [.pos (Fin.last n), .neg j.castSucc],
      [.neg (Fin.last n), .pos i.castSucc, .pos j.castSucc]]

theorem sat_constraints_iff (gate : Gate n) (σ : Fin (n + 1) → Bool) :
    CNF.Sat σ gate.constraints ↔ σ (Fin.last n) = gate.eval (σ ∘ Fin.castSucc) := by
  cases gate with
  | const value => cases value <;> simp [constraints, Gate.eval]
  | not i =>
    cases hz : σ (Fin.last n) <;> cases hi : σ i.castSucc <;>
      simp [constraints, Gate.eval, hz, hi]
  | binary op i j =>
    cases op <;> cases hz : σ (Fin.last n) <;> cases hi : σ i.castSucc <;>
      cases hj : σ j.castSucc <;>
      simp [constraints, Gate.eval, BinaryOp.eval, hz, hi, hj]

theorem size_constraints_le (gate : Gate n) : CNF.size gate.constraints ≤ 10 := by
  cases gate with
  | const value => cases value <;> simp [constraints]
  | not _ => simp [constraints]
  | binary op _ _ => cases op <;> simp [constraints]

end Gate

namespace Network

/-- Consecutive gate blocks refer to the same absolute wire indices. -/
@[expose] def constraints : {n m : Nat} → Network n m → CNF.Formula Nat
  | _, _, .empty _ => []
  | _, _, .cons gate rest => CNF.mapAtoms Fin.val gate.constraints ++ rest.constraints

private theorem assignment_extend (gate : Gate n) (σ : Nat → Bool)
    (h : CNF.Sat σ (CNF.mapAtoms Fin.val gate.constraints)) :
    (fun i : Fin (n + 1) ↦ σ i.val) = gate.extend (fun i : Fin n ↦ σ i.val) := by
  have hEval := (gate.sat_constraints_iff (σ ∘ Fin.val)).mp ((CNF.sat_mapAtoms ..).mp h)
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · rw [Gate.extend_last]
    exact hEval
  · rw [Gate.extend_castSucc]
    rfl

/-- Satisfying assignments of the gate clauses are exactly evaluations on their input wires. -/
theorem sat_constraints_iff_eval (network : Network n m) (σ : Nat → Bool) :
    CNF.Sat σ network.constraints ↔
      ∀ i : Fin m, σ i.val = network.eval (fun j : Fin n ↦ σ j.val) i := by
  induction network with
  | empty => simp [constraints, eval]
  | @cons n m gate rest ih =>
    simp only [constraints, CNF.sat_append, eval]
    constructor
    · rintro ⟨hGate, hRest⟩ i
      rw [← assignment_extend gate σ hGate]
      exact ih.mp hRest i
    · intro hValues
      have hLast := hValues ((Fin.last n).castLE rest.wires_le)
      rw [eval_castLE, Gate.extend_last] at hLast
      have hGate : CNF.Sat σ (CNF.mapAtoms Fin.val gate.constraints) :=
        (CNF.sat_mapAtoms σ Fin.val gate.constraints).mpr
          ((gate.sat_constraints_iff (σ ∘ Fin.val)).mpr hLast)
      refine ⟨hGate, ih.mpr ?_⟩
      rw [assignment_extend gate σ hGate]
      exact hValues

theorem size_constraints_le (network : Network n m) :
    CNF.size network.constraints ≤ 10 * network.size := by
  induction network with
  | empty => simp [constraints, size]
  | cons gate rest ih =>
    have hGate := gate.size_constraints_le
    simp only [constraints, CNF.size_append, CNF.size_mapAtoms, size]
    omega

theorem literalIndex_lt_of_mem_constraints (network : Network n m)
    {c : CNF.Clause Nat} {l : CNF.Literal Nat} (hc : c ∈ network.constraints) (hl : l ∈ c) :
    CNFCode.literalIndex l < m := by
  induction network with
  | empty => simp [constraints] at hc
  | cons gate rest ih =>
    simp only [constraints, List.mem_append] at hc
    rcases hc with hc | hc
    · simp only [CNF.mapAtoms, List.mem_map] at hc
      obtain ⟨localClause, _, rfl⟩ := hc
      obtain ⟨localLiteral, _, rfl⟩ := List.mem_map.mp hl
      cases localLiteral with
      | pos i => exact i.isLt.trans_le rest.wires_le
      | neg i => exact i.isLt.trans_le rest.wires_le
    · exact ih hc

end Network

namespace BooleanCircuit

/-- Assert that the circuit evaluates to true. -/
@[expose] def toCNF (circuit : BooleanCircuit n) : CNF.Formula Nat :=
  circuit.network.constraints ++ [[.pos circuit.output.val]]

theorem satisfiable_toCNF_iff (circuit : BooleanCircuit n) :
    CNF.Satisfiable circuit.toCNF ↔ ∃ bits : Fin n → Bool, circuit.eval bits = true := by
  simp only [toCNF, CNF.Satisfiable, CNF.sat_append, CNF.sat_unit, CNF.Literal.sat_pos]
  constructor
  · rintro ⟨σ, hRun, hOutput⟩
    refine ⟨fun i ↦ σ i.val, ?_⟩
    exact ((circuit.network.sat_constraints_iff_eval σ).mp hRun circuit.output).symm.trans hOutput
  · rintro ⟨bits, hEval⟩
    let σ (i : Nat) : Bool := if h : i < circuit.wires then circuit.network.eval bits ⟨i, h⟩
      else false
    have hWire (i : Fin circuit.wires) : σ i.val = circuit.network.eval bits i := by
      simp [σ, i.isLt]
    have hInput : (fun i : Fin n ↦ σ i.val) = bits := by
      funext i
      exact (hWire (i.castLE circuit.network.wires_le)).trans (circuit.network.eval_castLE bits i)
    refine ⟨σ, (circuit.network.sat_constraints_iff_eval σ).mpr ?_,
      (hWire circuit.output).trans hEval⟩
    rw [hInput]
    exact hWire

theorem size_toCNF_le (circuit : BooleanCircuit n) :
    CNF.size circuit.toCNF ≤ 10 * circuit.size + 2 :=
  calc
    _ = CNF.size circuit.network.constraints + 2 := by simp [toCNF, CNF.size_append]
    _ ≤ 10 * circuit.size + 2 := Nat.add_le_add_right circuit.network.size_constraints_le 2

private theorem literalIndex_lt_of_mem_toCNF (circuit : BooleanCircuit n)
    {c : CNF.Clause Nat} {l : CNF.Literal Nat} (hc : c ∈ circuit.toCNF) (hl : l ∈ c) :
    CNFCode.literalIndex l < circuit.wires := by
  simp only [toCNF, List.mem_append, List.mem_singleton] at hc
  rcases hc with hc | rfl
  · exact circuit.network.literalIndex_lt_of_mem_constraints hc hl
  · obtain rfl := List.mem_singleton.mp hl
    exact circuit.output.isLt

private theorem length_encodeClause_le (c : CNF.Clause Nat) (m : Nat)
    (h : ∀ l ∈ c, CNFCode.literalIndex l < m) :
    (CNFCode.encodeClause c).length ≤ 1 + (m + 3) * c.length := by
  induction c with
  | nil => simp
  | cons l c ih =>
    have hl := h l List.mem_cons_self
    have hc := ih (fun i hi ↦ h i (List.mem_cons_of_mem _ hi))
    simp only [CNFCode.encodeClause_cons, List.length_cons, List.length_append,
      CNFCode.length_encodeLiteral, Nat.mul_succ]
    omega

private theorem length_encode_le (F : CNF.Formula Nat) (m : Nat)
    (h : ∀ c ∈ F, ∀ l ∈ c, CNFCode.literalIndex l < m) :
    (CNFCode.encode F).length ≤ 1 + (m + 3) * CNF.size F := by
  induction F with
  | nil => simp
  | cons c F ih =>
    have hClause := length_encodeClause_le c m (h c List.mem_cons_self)
    have hRest := ih (fun e he ↦ h e (List.mem_cons_of_mem _ he))
    simp only [CNFCode.encode_cons, List.length_cons, List.length_append, CNF.size_cons,
      Nat.mul_add, Nat.mul_one]
    omega

/-- Unary wire indices make the code at most quadratic in the input and gate counts. -/
theorem encode_toCNF_length_le (circuit : BooleanCircuit n) :
    (CNFCode.encode circuit.toCNF).length ≤
      1 + (n + circuit.size + 3) * (10 * circuit.size + 2) := by
  have hLength := length_encode_le circuit.toCNF circuit.wires
    (fun c hc l hl ↦ literalIndex_lt_of_mem_toCNF circuit hc hl)
  rw [circuit.network.wires_eq_input_add_size] at hLength
  exact hLength.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ circuit.size_toCNF_le) 1)

theorem encode_toCNF_mem_CNFSAT_iff (circuit : BooleanCircuit n) :
    CNFCode.encode circuit.toCNF ∈ CNFSAT ↔
      ∃ bits : Fin n → Bool, circuit.eval bits = true :=
  (encode_mem_CNFSAT_iff _).trans circuit.satisfiable_toCNF_iff

end BooleanCircuit

end PvsNP.Circuits
