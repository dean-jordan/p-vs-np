module

public import PvsNP.SAT.BinaryLanguage

/-! # Sensitivity of the three final coordinates of a binary CNF word -/

public section

namespace PvsNP.SATCircuitBounds

open CNFCode

private theorem encodeIndex_false_suffix (index : Nat) :
    ∃ front, encodeIndex index = front ++ [false] := by
  induction index with
  | zero => exact ⟨[], rfl⟩
  | succ index ih =>
    obtain ⟨front, hFront⟩ := ih
    exact ⟨true :: front, by simp only [encodeIndex, hFront, List.cons_append]⟩

private theorem encodeLiteral_false_suffix (l : CNF.Literal Nat) :
    ∃ front, encodeLiteral l = front ++ [false] := by
  cases l with
  | pos index =>
    obtain ⟨front, hFront⟩ := encodeIndex_false_suffix index
    exact ⟨true :: front, by simp only [encodeLiteral, hFront, List.cons_append]⟩
  | neg index =>
    obtain ⟨front, hFront⟩ := encodeIndex_false_suffix index
    exact ⟨false :: front, by simp only [encodeLiteral, hFront, List.cons_append]⟩

private theorem encodeClause_false_suffix {clause : CNF.Clause Nat} (hClause : clause ≠ []) :
    ∃ front, encodeClause clause = front ++ [false, false] := by
  induction clause with
  | nil => exact (hClause rfl).elim
  | cons literal tail ih =>
    cases tail with
    | nil =>
      obtain ⟨front, hFront⟩ := encodeLiteral_false_suffix literal
      exact ⟨true :: front, by
        simp only [encodeClause_cons, encodeClause_nil, hFront, List.cons_append, List.append_assoc]
        rfl⟩
    | cons next rest =>
      obtain ⟨front, hFront⟩ := ih (by simp)
      exact ⟨true :: (encodeLiteral literal ++ front), by
        simp only [encodeClause_cons, hFront, List.cons_append, List.append_assoc]⟩

private theorem encode_false_suffix {formula : CNF.Formula Nat} {assignment : Nat → Bool}
    (hNonempty : formula ≠ []) (hSat : CNF.Sat assignment formula) :
    ∃ front, encode formula = front ++ [false, false, false] := by
  induction formula with
  | nil => exact (hNonempty rfl).elim
  | cons clause tail ih =>
    obtain ⟨hClause, hTail⟩ := (CNF.sat_cons assignment clause tail).mp hSat
    cases tail with
    | nil =>
      have hClauseNonempty : clause ≠ [] := by
        rintro rfl
        exact CNF.Clause.sat_nil assignment hClause
      obtain ⟨front, hFront⟩ := encodeClause_false_suffix hClauseNonempty
      exact ⟨true :: front, by
        simp only [encode_cons, encode_nil, hFront, List.cons_append, List.append_assoc]
        rfl⟩
    | cons next rest =>
      obtain ⟨front, hFront⟩ := ih (by simp) hTail
      exact ⟨true :: (encodeClause clause ++ front), by
        simp only [encode_cons, hFront, List.cons_append, List.append_assoc]⟩

/-- A satisfiable code of length greater than one has three final zero bits. -/
theorem exists_false_suffix_of_mem_CNFSAT {word : BinaryWord} (hSat : word ∈ CNFSAT)
    (hLength : 1 < word.length) : ∃ front, word = front ++ [false, false, false] := by
  obtain ⟨formula, hDecode, assignment, hAssignment⟩ := hSat
  have hWord := decode_eq_some_iff.mp hDecode
  have hNonempty : formula ≠ [] := by
    rintro rfl
    rw [hWord, encode_nil] at hLength
    exact (Nat.lt_irrefl 1) hLength
  rw [hWord]
  exact encode_false_suffix hNonempty hAssignment

/-- Setting any of the final three bits of a suitable positive-unit encoding to one rejects it. -/
theorem last_three_sensitive_monotone {n : Nat} (i : Fin n) (hSize : 6 ≤ n)
    (hLast : n ≤ i.val + 3) :
    ∃ x y : Fin n → Bool, List.ofFn x ∈ CNFSAT ∧ List.ofFn y ∉ CNFSAT ∧
      (∀ j : Fin n, j ≠ i → x j = y j) ∧
      ∀ j : Fin n, x j = true → y j = true := by
  let formula : CNF.Formula Nat := [[.pos (n - 6)]]
  let word := encode formula
  have hLength : word.length = n := by
    simp only [word, formula, encode_cons, encode_nil, encodeClause_cons, encodeClause_nil,
      List.length_cons, List.length_append, List.length_nil, length_encodeLiteral, literalIndex]
    omega
  let x (j : Fin n) : Bool := word[j.val]?.getD false
  let y (j : Fin n) : Bool := if j = i then true else x j
  have hx : List.ofFn x = word := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, hLength]
    · intro j _ hj
      simp [x, List.getElem?_eq_getElem hj]
  refine ⟨x, y, ?_, ?_, ?_, ?_⟩
  · rw [hx, encode_mem_CNFSAT_iff]
    exact ⟨fun _ ↦ true, by simp [formula]⟩
  · intro hYes
    have hLong : 1 < (List.ofFn y).length := by
      simp only [List.length_ofFn]
      omega
    obtain ⟨front, hFront⟩ := exists_false_suffix_of_mem_CNFSAT hYes hLong
    have hFrontLength : front.length + 3 = n := by
      have hEq := congrArg List.length hFront
      simpa only [List.length_ofFn, List.length_append, List.length_cons, List.length_nil]
        using hEq.symm
    have hBefore : front.length ≤ i.val := by omega
    have hInside : i.val - front.length < 3 := by have := i.isLt; omega
    have hiTrue : (List.ofFn y)[i.val]? = some true := by simp [y, i.isLt]
    have hiFalse : (List.ofFn y)[i.val]? = some false := by
      rw [hFront, List.getElem?_append_right hBefore]
      exact List.getElem?_replicate_of_lt hInside
    rw [hiTrue] at hiFalse
    contradiction
  · intro j hNe
    exact (ite_eq_right hNe).symm
  · intro j hOn
    by_cases hEq : j = i
    · exact ite_eq_left hEq
    · exact (ite_eq_right hEq).trans hOn

/-- Each of the final three coordinates is relevant once a positive unit fits in the word. -/
theorem last_three_sensitive {n : Nat} (i : Fin n) (hSize : 6 ≤ n)
    (hLast : n ≤ i.val + 3) :
    ∃ x y : Fin n → Bool, List.ofFn x ∈ CNFSAT ∧ List.ofFn y ∉ CNFSAT ∧
      ∀ j : Fin n, j ≠ i → x j = y j := by
  obtain ⟨x, y, hYes, hNo, hAgree, _⟩ := last_three_sensitive_monotone i hSize hLast
  exact ⟨x, y, hYes, hNo, hAgree⟩

end PvsNP.SATCircuitBounds
