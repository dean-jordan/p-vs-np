module

public import PvsNP.SAT.AssignmentQueryTree
public import PvsNP.SAT.BinaryLanguage

import Init.Data.List.Nat.TakeDrop

/-! # Two separated truth tables in one CNF word

The clauses on either side independently prescribe the selector bit at
each address. The formula is satisfiable exactly when the two prescribed
values agree at some address, which detects differing table bits.
-/

public section

namespace PvsNP.SATCrossing

open AssignmentQueryTree (allAssignments mem_allAssignments length_allAssignments)
open CNFCode (encode encodeClause encode_cons encodeClause_cons length_encodeLiteral literalIndex)

abbrev Address (r : Nat) := Fin r → Bool
abbrev Table (r : Nat) := Address r → Bool

private def signedLiteral (i : Nat) (value : Bool) : CNF.Literal Nat :=
  if value then .pos i else .neg i

private theorem signedLiteral_sat (σ : Nat → Bool) (i : Nat) (value : Bool) :
    (signedLiteral i value).Sat σ ↔ σ i = value := by
  cases value <;> simp [signedLiteral]

private theorem literalIndex_signedLiteral (i : Nat) (value : Bool) :
    literalIndex (signedLiteral i value) = i := by
  cases value <;> rfl

/-- Require the selector value at this address, with every other address allowed. -/
private def addressClause (r : Nat) (address : Address r) (value : Bool) : CNF.Clause Nat :=
  signedLiteral r value :: List.ofFn fun i : Fin r ↦ signedLiteral i.val (!(address i))

private theorem addressClause_sat (r : Nat) (σ : Nat → Bool) (address : Address r)
    (value : Bool) :
    CNF.Clause.Sat σ (addressClause r address value) ↔
      (fun i : Fin r ↦ σ i.val) = address → σ r = value := by
  rw [addressClause, CNF.Clause.sat_cons, signedLiteral_sat]
  constructor
  · rintro (hSelector | hAddress) hEqual
    · exact hSelector
    · obtain ⟨literal, hMem, hSat⟩ := hAddress
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hMem
      have hDifferent := (signedLiteral_sat σ i.val (!(address i))).mp hSat
      have hSame := congrFun hEqual i
      change σ i.val = address i at hSame
      rw [hSame] at hDifferent
      cases address i <;> simp at hDifferent
  · intro h
    by_cases hEqual : (fun i : Fin r ↦ σ i.val) = address
    · exact Or.inl (h hEqual)
    · have hDifference : ∃ i : Fin r, σ i.val ≠ address i := by
        by_contra! hAll
        exact hEqual (funext hAll)
      obtain ⟨i, hi⟩ := hDifference
      refine Or.inr ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, (signedLiteral_sat _ _ _).mpr ?_⟩
      cases hBit : address i <;> simpa [hBit] using hi

/-- The left table prescribes its bit, and the right table prescribes its complement. -/
def tableFormula (r : Nat) (values : Table r) : CNF.Formula Nat :=
  (allAssignments r).map fun address ↦ addressClause r address (values address)

private theorem tableFormula_sat (r : Nat) (σ : Nat → Bool) (values : Table r) :
    CNF.Sat σ (tableFormula r values) ↔ σ r = values (fun i : Fin r ↦ σ i.val) := by
  rw [tableFormula, CNF.sat_map]
  constructor
  · intro h
    exact (addressClause_sat r σ _ _).mp (h _ (mem_allAssignments _)) rfl
  · intro h address _
    exact (addressClause_sat r σ address _).mpr (fun hEqual ↦ hEqual ▸ h)

private def tautology : CNF.Clause Nat := [.pos 0, .neg 0]

def paddingFormula (p : Nat) : CNF.Formula Nat := List.replicate p tautology

theorem paddingFormula_sat (p : Nat) (σ : Nat → Bool) :
    CNF.Sat σ (paddingFormula p) := by
  intro c hc
  have he : c = tautology := List.eq_of_mem_replicate hc
  subst c
  cases h : σ 0 <;> simp [tautology, h]

/-- The left fragment leaves the next clause position open. -/
def leftBlock (r : Nat) (a : Table r) : BinaryWord := (encode (tableFormula r a)).dropLast

/-- The right fragment includes the final formula terminator. -/
def rightBlock (r : Nat) (b : Table r) : BinaryWord :=
  encode (tableFormula r fun address ↦ !(b address))

/-- Insert any number of fixed tautological clauses between the two tables. -/
@[expose] def paddingBlock (p : Nat) : BinaryWord := (encode (paddingFormula p)).dropLast

@[expose] def crossingWord (r p : Nat) (a b : Table r) : BinaryWord :=
  leftBlock r a ++ paddingBlock p ++ rightBlock r b

/-- The input portion to the left of a cut after `k` padding bits. -/
@[expose] def leftPart (r p k : Nat) (a : Table r) : BinaryWord :=
  leftBlock r a ++ (paddingBlock p).take k

/-- The input portion to the right of the same cut. -/
@[expose] def rightPart (r p k : Nat) (b : Table r) : BinaryWord :=
  (paddingBlock p).drop k ++ rightBlock r b

theorem crossingWord_eq_parts (r p k : Nat) (a b : Table r) :
    crossingWord r p a b = leftPart r p k a ++ rightPart r p k b := by
  simp only [crossingWord, leftPart, rightPart, List.append_assoc]
  rw [← List.append_assoc ((paddingBlock p).take k), List.take_append_drop]

theorem encode_ne_nil (F : CNF.Formula Nat) : encode F ≠ [] := by
  cases F <;> simp [encode_cons]

theorem dropLast_encode_append (F G : CNF.Formula Nat) :
    (encode F).dropLast ++ encode G = encode (F ++ G) := by
  induction F with
  | nil => simp
  | cons c F ih =>
    rw [encode_cons, List.cons_append, encode_cons]
    change (((true :: encodeClause c) ++ encode F).dropLast ++ encode G) =
      (true :: encodeClause c) ++ encode (F ++ G)
    rw [List.dropLast_append_of_ne_nil (encode_ne_nil F), List.append_assoc, ih]

theorem crossingWord_eq_encode (r p : Nat) (a b : Table r) :
    crossingWord r p a b =
      encode (tableFormula r a ++ paddingFormula p ++ tableFormula r (fun j ↦ !(b j))) := by
  simp only [crossingWord, leftBlock, rightBlock, paddingBlock, List.append_assoc,
    dropLast_encode_append]

/-- The combined formula detects a differing table entry. -/
theorem crossingWord_mem_CNFSAT_iff (r p : Nat) (a b : Table r) :
    crossingWord r p a b ∈ CNFSAT ↔ ∃ j : Address r, a j ≠ b j := by
  rw [crossingWord_eq_encode, encode_mem_CNFSAT_iff]
  simp only [CNF.Satisfiable, CNF.sat_append, tableFormula_sat, paddingFormula_sat, and_true]
  constructor
  · rintro ⟨σ, hLeft, hRight⟩
    let j : Address r := fun i ↦ σ i.val
    refine ⟨j, ?_⟩
    change σ r = a j at hLeft
    change σ r = !(b j) at hRight
    rw [hLeft] at hRight
    cases hb : b j <;> simp_all
  · rintro ⟨j, hDifferent⟩
    let σ (i : Nat) : Bool := if h : i < r then j ⟨i, h⟩ else a j
    have hAddress : (fun i : Fin r ↦ σ i.val) = j := by
      funext i
      simp only [σ, dite_eq_left i.isLt]
    have hSelector : σ r = a j := by simp [σ]
    refine ⟨σ, ?_, ?_⟩
    · rw [hAddress, hSelector]
    · rw [hAddress, hSelector]
      cases hb : b j <;> simp_all

theorem crossingWord_mem_CNFSAT_iff_ne (r p : Nat) (a b : Table r) :
    crossingWord r p a b ∈ CNFSAT ↔ a ≠ b := by
  rw [crossingWord_mem_CNFSAT_iff]
  constructor
  · rintro ⟨j, hDifferent⟩ hEqual
    exact hDifferent (congrFun hEqual j)
  · intro hDifferent
    by_contra! hEqual
    exact hDifferent (funext hEqual)

theorem crossingWord_diagonal_not_mem_CNFSAT (r p : Nat) (a : Table r) :
    crossingWord r p a a ∉ CNFSAT := by
  rw [crossingWord_mem_CNFSAT_iff_ne]
  exact fun hDifferent ↦ hDifferent rfl

private def clauseWidth (r : Nat) : Nat :=
  2 + (r + 3) + (List.ofFn fun i : Fin r ↦ i.val + 3).sum

/-- The fixed bit length of a table's clauses, before the final terminator. -/
def blockWidth (r : Nat) : Nat := 2 ^ r * clauseWidth r

private theorem length_encodeClause_eq (clause : CNF.Clause Nat) :
    (encodeClause clause).length = 1 + (clause.map fun l ↦ literalIndex l + 3).sum := by
  induction clause with
  | nil => simp
  | cons l rest ih =>
    simp only [encodeClause_cons, List.length_cons, List.length_append, length_encodeLiteral,
      List.map_cons, List.sum_cons, ih]
    omega

private theorem length_addressClause (r : Nat) (address : Address r) (value : Bool) :
    (encodeClause (addressClause r address value)).length + 1 = clauseWidth r := by
  rw [length_encodeClause_eq]
  simp only [addressClause, clauseWidth, List.map_cons, List.sum_cons, literalIndex_signedLiteral,
    List.map_ofFn, Function.comp_def]
  omega

private theorem length_addressBlocks (r : Nat) (values : Table r) (addresses : List (Address r)) :
    (encode (addresses.map fun address ↦ addressClause r address (values address))).length =
      addresses.length * clauseWidth r + 1 := by
  induction addresses with
  | nil => simp
  | cons address addresses ih =>
    simp only [List.map_cons, encode_cons, List.length_cons, List.length_append, Nat.succ_mul, ih]
    have hWidth := length_addressClause r address (values address)
    omega

private theorem length_encode_tableFormula (r : Nat) (values : Table r) :
    (encode (tableFormula r values)).length = blockWidth r + 1 := by
  rw [tableFormula, length_addressBlocks, length_allAssignments, blockWidth]

@[simp] theorem length_leftBlock (r : Nat) (a : Table r) :
    (leftBlock r a).length = blockWidth r := by
  simp only [leftBlock, List.length_dropLast, length_encode_tableFormula, Nat.add_sub_cancel]

@[simp] theorem length_rightBlock (r : Nat) (b : Table r) :
    (rightBlock r b).length = blockWidth r + 1 :=
  length_encode_tableFormula r _

private theorem length_paddingFormula (p : Nat) :
    (encode (paddingFormula p)).length = 8 * p + 1 := by
  induction p with
  | zero => simp [paddingFormula]
  | succ p ih =>
    change (encode (tautology :: paddingFormula p)).length = 8 * (p + 1) + 1
    have hWidth : (encodeClause tautology).length = 7 := by
      simp [length_encodeClause_eq, tautology, literalIndex]
    simp only [encode_cons, List.length_cons, List.length_append, hWidth, ih]
    omega

@[simp] theorem length_paddingBlock (p : Nat) : (paddingBlock p).length = 8 * p := by
  simp only [paddingBlock, List.length_dropLast, length_paddingFormula, Nat.add_sub_cancel]

theorem length_leftPart (r p k : Nat) (a : Table r) (hk : k ≤ (paddingBlock p).length) :
    (leftPart r p k a).length = blockWidth r + k := by
  simp only [leftPart, List.length_append, length_leftBlock, List.length_take, Nat.min_eq_left hk]

theorem length_rightPart (r p k : Nat) (b : Table r) :
    (rightPart r p k b).length = (8 * p - k) + (blockWidth r + 1) := by
  simp only [rightPart, List.length_append, List.length_drop, length_paddingBlock,
    length_rightBlock]

theorem take_crossingWord (r p k : Nat) (a b : Table r) (hk : k ≤ (paddingBlock p).length) :
    (crossingWord r p a b).take (blockWidth r + k) = leftPart r p k a := by
  rw [crossingWord_eq_parts r p k a b]
  exact List.take_left' (length_leftPart r p k a hk)

theorem drop_crossingWord (r p k : Nat) (a b : Table r) (hk : k ≤ (paddingBlock p).length) :
    (crossingWord r p a b).drop (blockWidth r + k) = rightPart r p k b := by
  rw [crossingWord_eq_parts r p k a b]
  exact List.drop_left' (length_leftPart r p k a hk)

/-- Splicing at a cut in the common padding combines the selected table fragments. -/
theorem splice_crossingWord (r p k : Nat) (a b c d : Table r)
    (hk : k ≤ (paddingBlock p).length) :
    (crossingWord r p a b).take (blockWidth r + k) ++
      (crossingWord r p c d).drop (blockWidth r + k) = crossingWord r p a d := by
  rw [take_crossingWord r p k a b hk, drop_crossingWord r p k c d hk,
    crossingWord_eq_parts r p k a d]

@[simp] theorem length_crossingWord (r p : Nat) (a b : Table r) :
    (crossingWord r p a b).length = 2 * blockWidth r + 8 * p + 1 := by
  simp only [crossingWord, List.length_append, length_leftBlock, length_paddingBlock,
    length_rightBlock]
  omega

theorem sum_le_length_mul (xs : List Nat) (cap : Nat) (hCap : ∀ x ∈ xs, x ≤ cap) :
    xs.sum ≤ xs.length * cap := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hHead := hCap x (List.mem_cons_self ..)
    have hTail := ih (fun y hy ↦ hCap y (List.mem_cons_of_mem _ hy))
    simp only [List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

theorem blockWidth_pos (r : Nat) : 0 < blockWidth r := by
  unfold blockWidth
  apply Nat.mul_pos (Nat.pow_pos (by decide))
  unfold clauseWidth
  omega

theorem pow_le_blockWidth (r : Nat) : 2 ^ r ≤ blockWidth r := by
  unfold blockWidth
  have hWidth : 1 ≤ clauseWidth r := by unfold clauseWidth; omega
  simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2 ^ r) hWidth

theorem blockWidth_le (r : Nat) : blockWidth r ≤ 2 ^ r * (2 + (r + 1) * (r + 3)) := by
  have hSum := sum_le_length_mul (List.ofFn fun i : Fin r ↦ i.val + 3) (r + 3) (by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    have hi := i.isLt
    omega)
  rw [List.length_ofFn] at hSum
  unfold blockWidth
  apply Nat.mul_le_mul_left
  unfold clauseWidth
  rw [Nat.succ_mul]
  omega

theorem length_crossingWord_le (r p : Nat) (a b : Table r) :
    (crossingWord r p a b).length ≤ 2 * (2 ^ r * (2 + (r + 1) * (r + 3))) + 8 * p + 1 := by
  rw [length_crossingWord]
  have hWidth := blockWidth_le r
  omega

end PvsNP.SATCrossing
