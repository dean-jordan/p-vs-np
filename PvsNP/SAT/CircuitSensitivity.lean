module

public import PvsNP.SAT.BinaryLanguage

/-! # Input sensitivity of binary CNF satisfiability -/

public section

namespace PvsNP.SATCircuitBounds

open CNFCode (encode encodeClause)

private theorem positiveUnit_length (a : Nat) :
    (encodeClause [.pos a]).length = a + 4 := by
  simp only [CNFCode.encodeClause_cons, CNFCode.encodeClause_nil, List.length_cons,
    List.length_append, CNFCode.length_encodeLiteral, CNFCode.literalIndex, List.length_nil]

private theorem rejects_trailing {f : CNF.Formula Nat} {rest : BinaryWord} (hRest : rest ≠ []) :
    encode f ++ rest ∉ CNFSAT := by
  rintro ⟨g, hDecode, _⟩
  rw [CNFCode.decode_encode_append] at hDecode
  cases rest with
  | nil => exact hRest rfl
  | cons b bs => simp at hDecode

private theorem split_witness {n : Nat} (i : Fin n) (front rest : BinaryWord) (yes no : Bool)
    (hFront : front.length = i.val) (hLength : front.length + 1 + rest.length = n)
    (hYes : front ++ yes :: rest ∈ CNFSAT) (hNo : front ++ no :: rest ∉ CNFSAT) :
    ∃ x y : Fin n → Bool, List.ofFn x ∈ CNFSAT ∧ List.ofFn y ∉ CNFSAT ∧
      ∀ j : Fin n, j ≠ i → x j = y j := by
  let bits (b : Bool) (j : Fin n) := (front ++ b :: rest)[j.val]?.getD false
  have hWord (b : Bool) : List.ofFn (bits b) = front ++ b :: rest := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_append, List.length_cons]
      omega
    · intro j _ hj
      simp [bits, List.getElem?_eq_getElem hj]
  refine ⟨bits yes, bits no, ?_, ?_, ?_⟩
  · rwa [hWord]
  · rwa [hWord]
  · intro j hDiff
    have hNe : j.val ≠ i.val := fun hEq ↦ hDiff (Fin.ext hEq)
    dsimp only [bits]
    by_cases hj : j.val < front.length
    · rw [List.getElem?_append_left hj, List.getElem?_append_left hj]
    · have hGe : front.length ≤ j.val := Nat.le_of_not_gt hj
      rw [List.getElem?_append_right hGe, List.getElem?_append_right hGe]
      cases hIndex : j.val - front.length with
      | zero => omega
      | succ d => rfl

/-- Every interior coordinate is relevant for binary CNF-SAT at its given input length. -/
theorem interior_sensitive {n : Nat} (i : Fin n) (hLeft : 5 ≤ i.val) (hRight : i.val + 6 ≤ n) :
    ∃ x y : Fin n → Bool, List.ofFn x ∈ CNFSAT ∧ List.ofFn y ∉ CNFSAT ∧
      ∀ j : Fin n, j ≠ i → x j = y j := by
  let first : CNF.Clause Nat := [.pos (i.val - 5)]
  let second : CNF.Clause Nat := [.pos (n - i.val - 6)]
  let front := true :: encodeClause first
  let rest := encodeClause second ++ [false]
  have hFront : front.length = i.val := by
    simp only [front, first, List.length_cons, positiveUnit_length]
    omega
  have hLength : front.length + 1 + rest.length = n := by
    simp only [hFront, rest, second, List.length_append, positiveUnit_length,
      List.length_cons, List.length_nil]
    omega
  apply split_witness i front rest true false hFront hLength
  · have hEncode : front ++ true :: rest = encode [first, second] := by
      simp only [front, rest, CNFCode.encode_cons, CNFCode.encode_nil, List.cons_append]
    rw [hEncode, encode_mem_CNFSAT_iff]
    exact ⟨fun _ ↦ true, by simp [first, second]⟩
  · have hEncode : front ++ false :: rest = encode [first] ++ rest := by
      simp only [front, CNFCode.encode_cons, CNFCode.encode_nil, List.cons_append,
        List.append_assoc, List.nil_append]
    rw [hEncode]
    exact rejects_trailing (by simp [rest])

/-- The first coordinate is relevant once a positive unit clause fits in the word. -/
theorem first_sensitive {n : Nat} (i : Fin n) (hSize : 6 ≤ n) (hFirst : i.val = 0) :
    ∃ x y : Fin n → Bool, List.ofFn x ∈ CNFSAT ∧ List.ofFn y ∉ CNFSAT ∧
      ∀ j : Fin n, j ≠ i → x j = y j := by
  let clause : CNF.Clause Nat := [.pos (n - 6)]
  let rest := encodeClause clause ++ [false]
  have hLength : ([] : BinaryWord).length + 1 + rest.length = n := by
    simp only [rest, clause, List.length_append, List.length_cons, positiveUnit_length,
      List.length_nil]
    omega
  apply split_witness i [] rest true false hFirst.symm hLength
  · rw [List.nil_append]
    have hEncode : true :: rest = encode [clause] := by
      simp only [rest, CNFCode.encode_cons, CNFCode.encode_nil]
    rw [hEncode, encode_mem_CNFSAT_iff]
    exact ⟨fun _ ↦ true, by simp [clause]⟩
  · simpa only [CNFCode.encode_nil, List.nil_append, List.singleton_append] using
      rejects_trailing (f := []) (rest := rest) (by simp [rest])

private theorem encodeIndex_eq_replicate (a : Nat) :
    CNFCode.encodeIndex a = List.replicate a true ++ [false] := by
  induction a with
  | zero => rfl
  | succ a ih => simp only [CNFCode.encodeIndex, ih, List.replicate_succ, List.cons_append]

private theorem encode_cons_positiveUnit (a : Nat) (f : CNF.Formula Nat) :
    encode ([.pos a] :: f) = List.replicate (a + 3) true ++ [false, false] ++ encode f := by
  simp only [CNFCode.encode_cons, CNFCode.encodeClause_cons, CNFCode.encodeClause_nil,
    CNFCode.encodeLiteral, encodeIndex_eq_replicate, List.replicate_succ, List.cons_append,
    List.append_assoc, List.nil_append]

private theorem encode_positiveUnit_length (a : Nat) : (encode [[.pos a]]).length = a + 6 := by
  simp only [CNFCode.encode_cons, CNFCode.encode_nil, List.length_cons, List.length_append,
    positiveUnit_length, List.length_nil]

private theorem positiveUnits_mem (a b : Nat) : encode [[.pos a], [.pos b]] ∈ CNFSAT :=
  (encode_mem_CNFSAT_iff _).mpr ⟨fun _ ↦ true, by simp⟩

private theorem left_unary_marker_sensitive {n : Nat} (i : Fin n) (hLeft : 3 ≤ i.val)
    (hRight : i.val + 9 ≤ n) :
    ∃ x y : Fin n → Bool, List.ofFn x ∈ CNFSAT ∧ List.ofFn y ∉ CNFSAT ∧
      ∀ j : Fin n, j ≠ i → x j = y j := by
  let b := n - i.val - 9
  let tail := encode [[.pos b]]
  let front := List.replicate i.val true
  let rest := false :: false :: tail
  have hFront : front.length = i.val := List.length_replicate
  have hTail : tail.length = b + 6 := encode_positiveUnit_length b
  have hLength : front.length + 1 + rest.length = n := by
    simp only [hFront, rest, List.length_cons, hTail, b]
    omega
  apply split_witness i front rest true false hFront hLength
  · have hAdd : i.val - 2 + 3 = i.val + 1 := by omega
    have hEncode : encode [[.pos (i.val - 2)], [.pos b]] = front ++ true :: rest := by
      rw [encode_cons_positiveUnit, hAdd, List.replicate_add]
      simp only [front, rest, tail, List.replicate_succ, List.replicate_zero, List.append_assoc,
        List.cons_append, List.nil_append]
    rw [← hEncode]
    exact positiveUnits_mem _ _
  · have hAdd : i.val - 3 + 3 = i.val := by omega
    have hEncode : encode [[.pos (i.val - 3)]] ++ tail = front ++ false :: rest := by
      rw [encode_cons_positiveUnit, hAdd]
      simp only [front, rest, CNFCode.encode_nil, List.append_assoc, List.cons_append,
        List.nil_append]
    rw [← hEncode]
    apply rejects_trailing
    intro hEmpty
    rw [hEmpty, List.length_nil] at hTail
    omega

/-- The first literal marker and the next two unary marker positions are relevant. -/
theorem early_markers_sensitive {n : Nat} (i : Fin n) (hSize : 16 ≤ n)
    (hEarly : i.val = 1 ∨ i.val = 3 ∨ i.val = 4) :
    ∃ x y : Fin n → Bool, List.ofFn x ∈ CNFSAT ∧ List.ofFn y ∉ CNFSAT ∧
      ∀ j : Fin n, j ≠ i → x j = y j := by
  rcases hEarly with hMarker | hUnary
  · let b := n - 11
    let tail := encode [[.pos b]]
    let rest := true :: false :: false :: tail
    have hTail : tail.length = b + 6 := encode_positiveUnit_length b
    have hLength : ([true] : BinaryWord).length + 1 + rest.length = n := by
      simp only [rest, List.length_cons, List.length_nil, hTail, b]
      omega
    apply split_witness i [true] rest true false hMarker.symm hLength
    · have hEncode : encode [[.pos 0], [.pos b]] = [true] ++ true :: rest := by
        rw [encode_cons_positiveUnit]
        rfl
      rw [← hEncode]
      exact positiveUnits_mem _ _
    · have hEncode : encode [[], []] ++ tail = [true] ++ false :: rest := by
        simp only [rest, CNFCode.encode_cons, CNFCode.encode_nil, CNFCode.encodeClause_nil,
          List.cons_append, List.nil_append]
      rw [← hEncode]
      apply rejects_trailing
      intro hEmpty
      rw [hEmpty, List.length_nil] at hTail
      omega
  · apply left_unary_marker_sensitive i <;> omega

/-- The last literal marker is relevant when the word ends in a unit clause. -/
theorem last_literal_marker_sensitive {n : Nat} (i : Fin n) (hSize : 16 ≤ n)
    (hLast : i.val + 5 = n) :
    ∃ x y : Fin n → Bool, List.ofFn x ∈ CNFSAT ∧ List.ofFn y ∉ CNFSAT ∧
      ∀ j : Fin n, j ≠ i → x j = y j := by
  let a := n - 11
  let front := (true :: encodeClause [.pos a]) ++ [true]
  let rest : BinaryWord := [true, false, false, false]
  have hFront : front.length = i.val := by
    simp only [front, List.length_append, List.length_cons, List.length_nil, positiveUnit_length, a]
    omega
  have hLength : front.length + 1 + rest.length = n := by
    simpa only [hFront, rest, List.length_cons, List.length_nil] using hLast
  apply split_witness i front rest true false hFront hLength
  · have hEncode : encode [[.pos a], [.pos 0]] = front ++ true :: rest := by
      rw [CNFCode.encode_cons, encode_cons_positiveUnit 0, CNFCode.encode_nil]
      simp only [front, rest, List.cons_append, List.append_assoc, List.nil_append]
      rfl
    rw [← hEncode]
    exact positiveUnits_mem _ _
  · have hEncode : encode [[.pos a], [], []] ++ [false] = front ++ false :: rest := by
      simp only [front, rest, CNFCode.encode_cons, CNFCode.encode_nil, CNFCode.encodeClause_nil,
        List.cons_append, List.append_assoc, List.nil_append]
    rw [← hEncode]
    exact rejects_trailing (by simp)

end PvsNP.SATCircuitBounds
