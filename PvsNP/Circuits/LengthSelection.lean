module

public import PvsNP.Circuits.BooleanCircuit
public import PvsNP.Circuits.WordBuffer

/-! # Selecting a circuit by the length of a padded word -/

public section

namespace PvsNP.Circuits

private def lengthGuard (B : Nat) (len : Fin (B + 1)) : BooleanCircuit (B + B) :=
  let predecessor := if h : 0 < len.val then
      BooleanCircuit.input (Fin.natAdd B ⟨len.val - 1, by omega⟩)
    else BooleanCircuit.const (B + B) true
  let successor := if h : len.val < B then
      (BooleanCircuit.input (Fin.natAdd B ⟨len.val, h⟩)).not
    else BooleanCircuit.const (B + B) true
  BooleanCircuit.binary .and predecessor successor

private theorem lengthGuard_eval (B : Nat) (y : BinaryWord) (h : y.length ≤ B)
    (len : Fin (B + 1)) :
    (lengthGuard B len).eval (wordBuffer B y) = true ↔ len.val = y.length := by
  have hLen : len.val ≤ B := Nat.le_of_lt_succ len.isLt
  simp only [lengthGuard, BooleanCircuit.eval_binary, BinaryOp.eval]
  split <;> split <;>
    simp only [BooleanCircuit.eval_input, BooleanCircuit.eval_const, BooleanCircuit.eval_not,
      wordBuffer_present, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      decide_eq_false_iff_not, true_and, and_true, true_iff] <;>
    omega

private theorem lengthGuard_size_le (B : Nat) (len : Fin (B + 1)) :
    (lengthGuard B len).size ≤ 3 := by
  simp only [lengthGuard, BooleanCircuit.size_binary]
  split <;> split <;> simp

private def dataWires {B : Nat} (len : Fin (B + 1)) (j : Fin len.val) : Fin (B + B) :=
  Fin.castAdd B (Fin.castLE (Nat.le_of_lt_succ len.isLt) j)

private theorem dataWires_eval (B : Nat) (y : BinaryWord) (h : y.length ≤ B) :
    wordBuffer B y ∘ dataWires ⟨y.length, Nat.lt_succ_of_le h⟩ =
      (fun j : Fin y.length ↦ y[j.val]) := by
  funext j
  simp [dataWires, j.isLt]

private def lengthBranch (family : (len : Nat) → BooleanCircuit len) (B : Nat)
    (len : Fin (B + 1)) : BooleanCircuit (B + B) :=
  BooleanCircuit.binary .and (lengthGuard B len) ((family len.val).mapInputs (dataWires len))

private theorem lengthBranch_eval (family : (len : Nat) → BooleanCircuit len) (B : Nat)
    (y : BinaryWord) (h : y.length ≤ B) (len : Fin (B + 1)) :
    (lengthBranch family B len).eval (wordBuffer B y) = true ↔
      len.val = y.length ∧ (family y.length).eval (fun j : Fin y.length ↦ y[j.val]) = true := by
  simp only [lengthBranch, BooleanCircuit.eval_binary, BinaryOp.eval, Bool.and_eq_true,
    lengthGuard_eval B y h, BooleanCircuit.eval_mapInputs]
  by_cases hLen : len.val = y.length
  · have hIndex : len = ⟨y.length, Nat.lt_succ_of_le h⟩ := Fin.ext hLen
    subst len
    simp [dataWires_eval B y h]
  · simp [hLen]

/-- Select a circuit for one of the lengths represented by a buffer of capacity `B`. -/
def selectLength (family : (len : Nat) → BooleanCircuit len) (B : Nat) :
    BooleanCircuit (B + B) :=
  BooleanCircuit.orList ((List.finRange (B + 1)).map (lengthBranch family B))

/-- A valid buffer selects exactly the circuit for the original word length. -/
theorem selectLength_eval (family : (len : Nat) → BooleanCircuit len) (B : Nat)
    (y : BinaryWord) (h : y.length ≤ B) :
    (selectLength family B).eval (wordBuffer B y) =
      (family y.length).eval (fun j : Fin y.length ↦ y[j.val]) := by
  apply Bool.eq_iff_iff.mpr
  rw [selectLength, BooleanCircuit.eval_orList_eq_true]
  constructor
  · rintro ⟨c, hc, hEval⟩
    obtain ⟨len, _, rfl⟩ := List.mem_map.mp hc
    exact ((lengthBranch_eval family B y h len).mp hEval).2
  · intro hEval
    let len : Fin (B + 1) := ⟨y.length, Nat.lt_succ_of_le h⟩
    exact ⟨lengthBranch family B len, List.mem_map_of_mem (List.mem_finRange len),
      (lengthBranch_eval family B y h len).mpr ⟨rfl, hEval⟩⟩

/-- The selector uses at most five additional gates per candidate length and one constant. -/
theorem selectLength_size_le (family : (len : Nat) → BooleanCircuit len) (B K : Nat)
    (h : ∀ len ≤ B, (family len).size ≤ K) :
    (selectLength family B).size ≤ (B + 1) * (K + 5) + 1 := by
  unfold selectLength
  have bound := BooleanCircuit.size_orList_le ((List.finRange (B + 1)).map (lengthBranch family B))
    (K + 4) (by
      intro c hc
      obtain ⟨len, _, rfl⟩ := List.mem_map.mp hc
      have hLen := h len.val (Nat.le_of_lt_succ len.isLt)
      have hGuard := lengthGuard_size_le B len
      simp only [lengthBranch, BooleanCircuit.size_binary, BooleanCircuit.size_mapInputs]
      omega)
  simpa only [List.length_map, List.length_finRange] using bound

end PvsNP.Circuits
