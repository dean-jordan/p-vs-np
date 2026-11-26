module

public import PvsNP.SAT.CrossingBlockPadding
public import PvsNP.SAT.CrossingPalette

/-! # Uniform bit lengths for the palette crossing family -/

public section

namespace PvsNP.SATCrossing.Palette

open CNFCode (encode literalIndex)

/-- Reserve bits for the address clauses, the payload constraint, and a
fresh positive unit that fixes the final length. -/
@[expose] def width (r : Nat) : Nat := 48 * (r + 1) ^ 2 * 2 ^ r

theorem pow_le_width (r : Nat) : 2 ^ r ≤ width r := by
  have hPos : 0 < 48 * (r + 1) ^ 2 :=
    Nat.mul_pos (by decide) (Nat.pow_pos (Nat.succ_pos r))
  exact Nat.le_mul_of_pos_left _ hPos

theorem width_pos (r : Nat) : 0 < width r := (Nat.two_pow_pos r).trans_le (pow_le_width r)

private theorem rawBlockLength_le (F : CNF.Formula Nat) (k m : Nat)
    (hClauses : ∀ c ∈ F, c.length ≤ k ∧ ∀ l ∈ c, literalIndex l < m) :
    rawBlockLength F ≤ F.length * (2 + k * (m + 3)) := by
  induction F with
  | nil => simp [rawBlockLength]
  | cons c F ih =>
    obtain ⟨hLength, hIndices⟩ := hClauses c List.mem_cons_self
    have hSum := sum_le_length_mul (c.map fun l ↦ literalIndex l + 3) (m + 3) (by
      intro v hv
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hv
      exact Nat.add_le_add_right (hIndices l hl).le 3)
    rw [List.length_map] at hSum
    have hWidth : rawBlockLength [c] = 2 + (c.map fun l ↦ literalIndex l + 3).sum := by
      simp only [rawBlockLength_eq, List.length_singleton, List.flatten_cons, List.flatten_nil,
        List.append_nil, Nat.mul_one]
    have hTail := ih (fun d hd ↦ hClauses d (List.mem_cons_of_mem _ hd))
    have hCap := Nat.mul_le_mul_right (m + 3) hLength
    rw [show c :: F = [c] ++ F from rfl, rawBlockLength_append, hWidth]
    simp only [List.length_append, List.length_singleton, Nat.add_mul, Nat.one_mul]
    omega

private theorem raw_side_le (r : Nat) (a : Table r) :
    rawBlockLength (side r a) ≤ 8 * ((r + 1) ^ 2 * 2 ^ r) := by
  have h := rawBlockLength_le (side r a) (2 * r) (3 * r) (side_clause_bounds r a)
  rw [length_side] at h
  have hMul : (2 * r) * (3 * r + 3) ≤ 6 * (r + 1) ^ 2 := by
    have hCompare := Nat.mul_le_mul (show 2 * r ≤ 2 * (r + 1) by omega)
      (show 3 * r + 3 ≤ 3 * (r + 1) by omega)
    calc
      _ ≤ (2 * (r + 1)) * (3 * (r + 1)) := hCompare
      _ = (2 * 3) * (r + 1) ^ 2 := by rw [Nat.pow_two]; ac_rfl
  have hPos : 0 < (r + 1) ^ 2 := Nat.pow_pos (Nat.succ_pos r)
  calc
    _ ≤ 2 ^ r * (2 + 2 * r * (3 * r + 3)) := h
    _ ≤ 2 ^ r * (8 * (r + 1) ^ 2) := Nat.mul_le_mul_left _ (by omega)
    _ = _ := by ac_rfl

private theorem raw_header_le (r : Nat) :
    rawBlockLength (header r) ≤ 32 * ((r + 1) ^ 2 * 2 ^ r) := by
  have h := rawBlockLength_le (header r) 2 (3 * r) (header_clause_bounds r)
  have hRow : r ≤ 2 ^ r := Nat.le_of_lt Nat.lt_two_pow_self
  have hSquare : r * r ≤ (r + 1) * 2 ^ r :=
    Nat.mul_le_mul (Nat.le_succ _) hRow
  calc
    _ ≤ (header r).length * (2 + 2 * (3 * r + 3)) := h
    _ ≤ (2 * r) ^ 2 * (8 * (r + 1)) :=
      Nat.mul_le_mul (length_header_le r) (by omega)
    _ = 32 * ((r + 1) * (r * r)) := by
      rw [Nat.pow_two]
      calc
        _ = (2 * 2 * 8) * ((r + 1) * (r * r)) := by ac_rfl
        _ = _ := rfl
    _ ≤ 32 * ((r + 1) * ((r + 1) * 2 ^ r)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hSquare)
    _ = _ := by rw [Nat.pow_two, Nat.mul_assoc (r + 1)]

private theorem padding_room (r : Nat) : 5 + 3 * r ≤ 8 * ((r + 1) ^ 2 * 2 ^ r) := by
  have hSquare : r + 1 ≤ (r + 1) ^ 2 := by
    rw [Nat.pow_two]
    exact Nat.le_mul_of_pos_left _ (Nat.succ_pos r)
  have hRoom : (r + 1) ^ 2 ≤ (r + 1) ^ 2 * 2 ^ r :=
    Nat.le_mul_of_pos_right _ (Nat.two_pow_pos r)
  omega

private theorem left_fits (r : Nat) (a : Table r) :
    rawBlockLength (header r ++ side r a) + 5 + 3 * r ≤ width r := by
  have hHeader := raw_header_le r
  have hSide := raw_side_le r a
  have hRoom := padding_room r
  rw [rawBlockLength_append, width, Nat.mul_assoc]
  omega

private theorem right_fits (r : Nat) (b : Table r) :
    rawBlockLength (side r (fun j s ↦ !(b j s))) + 5 + 3 * r ≤ width r := by
  have hSide := raw_side_le r (fun j s ↦ !(b j s))
  have hRoom := padding_room r
  rw [width, Nat.mul_assoc]
  omega

@[expose] def leftBlock (r : Nat) (a : Table r) : BinaryWord :=
  (encode (padFormula (width r) (header r ++ side r a))).dropLast

@[expose] def rightBlock (r : Nat) (b : Table r) : BinaryWord :=
  encode (padFormula (width r) (side r (fun j s ↦ !(b j s))))

@[expose] def word (r p : Nat) (a b : Table r) : BinaryWord :=
  leftBlock r a ++ paddingBlock p ++ rightBlock r b

theorem length_leftBlock (r : Nat) (a : Table r) : (leftBlock r a).length = width r :=
  rawBlockLength_padFormula _ _ (by have h := left_fits r a; omega)

theorem length_rightBlock (r : Nat) (b : Table r) : (rightBlock r b).length = width r + 1 := by
  have h := rawBlockLength_padFormula (width r) (side r (fun j s ↦ !(b j s)))
    (by have hRoom := right_fits r b; omega)
  change (rightBlock r b).dropLast.length = width r at h
  have hNonempty := List.length_pos_iff.mpr
    (encode_ne_nil (padFormula (width r) (side r (fun j s ↦ !(b j s)))))
  rw [List.length_dropLast] at h
  change 0 < (rightBlock r b).length at hNonempty
  omega

theorem length_word (r p : Nat) (a b : Table r) :
    (word r p a b).length = 2 * width r + 8 * p + 1 := by
  simp only [word, List.length_append, length_leftBlock, length_rightBlock, length_paddingBlock]
  omega

private theorem combined_blocks_mem_CNFSAT_iff (r : Nat) (H : CNF.Formula Nat)
    (hMiddle : ∀ σ : Nat → Bool, (∀ i, 3 * r ≤ i → σ i = true) → CNF.Sat σ H)
    (a b : Table r) :
    leftBlock r a ++ (encode H).dropLast ++ rightBlock r b ∈ CNFSAT ↔ a ≠ b := by
  let F := header r ++ side r a
  let G := side r (fun j s ↦ !(b j s))
  have hF : ∀ c ∈ F, ∀ l ∈ c, literalIndex l < 3 * r := by
    intro c hc
    rcases List.mem_append.mp hc with hHeader | hSide
    · exact (header_clause_bounds r c hHeader).2
    · exact (side_clause_bounds r a c hSide).2
  have hG : ∀ c ∈ G, ∀ l ∈ c, literalIndex l < 3 * r := by
    intro c hc
    exact (side_clause_bounds r (fun j s ↦ !(b j s)) c hc).2
  have hEncode : leftBlock r a ++ (encode H).dropLast ++ rightBlock r b =
      encode (padFormula (width r) F ++ H ++ padFormula (width r) G) := by
    simp only [leftBlock, rightBlock, F, G, List.append_assoc,
      dropLast_encode_append]
  rw [hEncode, encode_mem_CNFSAT_iff,
    satisfiable_padFormula_with_middle_iff (width r) (3 * r) F G H hMiddle hF hG
      (left_fits r a) (right_fits r b)]
  exact satisfiable_iff_ne r a b

theorem word_mem_CNFSAT_iff (r p : Nat) (a b : Table r) : word r p a b ∈ CNFSAT ↔ a ≠ b :=
  combined_blocks_mem_CNFSAT_iff r (paddingFormula p) (fun σ _ ↦ paddingFormula_sat p σ) a b

/-- The middle block is a positive unit with enough unary bits to make the
assembled word exactly `n` bits long. -/
@[expose] def middleBlock (r n : Nat) : BinaryWord :=
  (encode (padFormula (n - (2 * width r + 1)) [])).dropLast

@[expose] def wordAtLength (r n : Nat) (a b : Table r) : BinaryWord :=
  leftBlock r a ++ middleBlock r n ++ rightBlock r b

private theorem middle_room (r n : Nat) (hLength : 10 * width r + 1 ≤ n) :
    5 + 3 * r ≤ n - (2 * width r + 1) := by
  have h := padding_room r
  simp only [width, Nat.mul_assoc] at hLength ⊢
  omega

private theorem length_middleBlock (r n : Nat) (hLength : 10 * width r + 1 ≤ n) :
    (middleBlock r n).length = n - (2 * width r + 1) := by
  have hRoom := middle_room r n hLength
  exact rawBlockLength_padFormula _ [] (by simp only [rawBlockLength_eq, List.length_nil,
    Nat.mul_zero, List.flatten_nil, List.map_nil, List.sum_nil, Nat.zero_add]; omega)

theorem enough_middleBlock (r n : Nat) (hLength : 10 * width r + 1 ≤ n) :
    8 * width r ≤ (middleBlock r n).length := by
  rw [length_middleBlock r n hLength]
  omega

theorem length_wordAtLength (r n : Nat) (hLength : 10 * width r + 1 ≤ n) (a b : Table r) :
    (wordAtLength r n a b).length = n := by
  simp only [wordAtLength, List.length_append, length_leftBlock, length_rightBlock,
    length_middleBlock r n hLength]
  omega

theorem wordAtLength_mem_CNFSAT_iff (r n : Nat) (hLength : 10 * width r + 1 ≤ n)
    (a b : Table r) : wordAtLength r n a b ∈ CNFSAT ↔ a ≠ b := by
  refine combined_blocks_mem_CNFSAT_iff r (padFormula (n - (2 * width r + 1)) []) ?_ a b
  intro σ hHigh
  have hRoom := middle_room r n hLength
  simp only [padFormula, rawBlockLength_eq, List.nil_append, List.length_nil, Nat.mul_zero,
    List.flatten_nil, List.map_nil, List.sum_nil, Nat.zero_add, CNF.sat_unit, CNF.Literal.sat_pos]
  exact hHigh _ (by omega)

end PvsNP.SATCrossing.Palette
