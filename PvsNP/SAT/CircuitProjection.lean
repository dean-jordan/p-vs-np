module

public import PvsNP.SAT.BinaryLanguage

/-! # Input sensitivity on valid CNF words -/

public section

namespace PvsNP.SATCircuitBounds

private def unitClause (a : Nat) (b : Bool) : CNF.Clause Nat :=
  [if b then .pos a else .neg a]

private def unitBlock (a : Nat) (b : Bool) : BinaryWord :=
  true :: true :: b :: (CNFCode.encodeIndex a ++ [false])

private theorem encode_unit_cons (a : Nat) (b : Bool) (F : CNF.Formula Nat) :
    CNFCode.encode (unitClause a b :: F) = unitBlock a b ++ CNFCode.encode F := by
  cases b <;> simp [unitClause, unitBlock, CNFCode.encode_cons, CNFCode.encodeClause_cons,
    CNFCode.encodeLiteral]

private theorem unitBlock_length (a : Nat) (b : Bool) : (unitBlock a b).length = a + 5 := by
  have h := CNFCode.length_encodeLiteral (.pos a)
  simp only [CNFCode.encodeLiteral, CNFCode.literalIndex, List.length_cons] at h
  simp only [unitBlock, List.length_cons, List.length_append, List.length_nil]
  omega

/-- A positive unit clause for variable zero, followed by one unit clause per sign. -/
def signFormula (signs : BinaryWord) : CNF.Formula Nat := (true :: signs).map (unitClause 0)

private theorem encode_signClauses (signs : BinaryWord) :
    CNFCode.encode (signs.map (unitClause 0)) = signs.flatMap (unitBlock 0) ++ [false] := by
  induction signs with
  | nil => simp
  | cons b signs ih =>
    simp only [List.map_cons, encode_unit_cons, List.flatMap_cons, ih, List.append_assoc]

private theorem length_signBlocks (signs : BinaryWord) :
    (signs.flatMap (unitBlock 0)).length = 5 * signs.length := by
  induction signs with
  | nil => simp
  | cons b signs ih =>
    simp only [List.flatMap_cons, List.length_append, unitBlock_length, Nat.zero_add, ih,
      List.length_cons, Nat.mul_succ, Nat.add_comm]

/-- Each sign adds five bits to the six-bit formula containing only the positive unit. -/
theorem encode_signFormula_length (signs : BinaryWord) :
    (CNFCode.encode (signFormula signs)).length = 5 * signs.length + 6 := by
  simp only [signFormula, encode_signClauses, List.length_append, length_signBlocks,
    List.length_cons, List.length_nil]
  omega

/-- On this valid family, binary CNF satisfiability computes the conjunction of the signs. -/
theorem encode_signFormula_mem_CNFSAT (signs : BinaryWord) :
    CNFCode.encode (signFormula signs) ∈ CNFSAT ↔ ∀ b ∈ signs, b = true := by
  rw [encode_mem_CNFSAT_iff]
  constructor
  · rintro ⟨σ, hSat⟩ b hb
    have h := (CNF.sat_map σ (true :: signs) (unitClause 0)).mp hSat
    have anchor := h true (List.mem_cons_self ..)
    have clause := h b (List.mem_cons_of_mem _ hb)
    cases b <;> simp_all [unitClause]
  · intro h
    refine ⟨fun _ ↦ true, (CNF.sat_map _ (true :: signs) (unitClause 0)).mpr ?_⟩
    intro b hb
    have eq := (List.mem_cons.mp hb).elim id (h b)
    simp [unitClause, eq]

private theorem encode_signFormula_context (before after : BinaryWord) (b : Bool) :
    CNFCode.encode (signFormula (before ++ b :: after)) =
      (unitBlock 0 true ++ before.flatMap (unitBlock 0) ++ [true, true]) ++
        b :: false :: false :: (after.flatMap (unitBlock 0) ++ [false]) := by
  unfold signFormula
  rw [encode_signClauses]
  simp [unitBlock, CNFCode.encodeIndex, List.flatMap_append, List.append_assoc]

private theorem encode_signFormula_flip (before after : BinaryWord) :
    CNFCode.encode (signFormula (before ++ false :: after)) =
      (CNFCode.encode (signFormula (before ++ true :: after))).set
        (5 * before.length + 7) false := by
  let front := unitBlock 0 true ++ before.flatMap (unitBlock 0) ++ [true, true]
  have hFront : front.length = 5 * before.length + 7 := by
    simp only [front, List.length_append, unitBlock_length, length_signBlocks, List.length_cons,
      List.length_nil]
    omega
  rw [encode_signFormula_context before after false, encode_signFormula_context before after true]
  change front ++ false :: false :: false :: (after.flatMap (unitBlock 0) ++ [false]) =
    (front ++ true :: false :: false :: (after.flatMap (unitBlock 0) ++ [false])).set
      (5 * before.length + 7) false
  rw [← hFront, List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self, List.set_cons_zero]

private def wordVector {n : Nat} (word : BinaryWord) (h : word.length = n) : Fin n → Bool :=
  fun j ↦ word[j.val]'(by simpa only [h] using j.isLt)

private theorem ofFn_wordVector {n : Nat} (word : BinaryWord) (h : word.length = n) :
    List.ofFn (wordVector word h) = word := by
  subst n
  exact List.ofFn_getElem

private theorem wordVector_set_other {n k : Nat} {good bad : BinaryWord}
    (hGoodLen : good.length = n) (hBadLen : bad.length = n)
    (hFlip : bad = good.set k false) (j : Fin n) (hj : j.val ≠ k) :
    wordVector good hGoodLen j = wordVector bad hBadLen j := by
  have hGet : bad[j.val]? = good[j.val]? := by rw [hFlip, List.getElem?_set_ne (Ne.symm hj)]
  have hGood : j.val < good.length := by simpa only [hGoodLen] using j.isLt
  have hBad : j.val < bad.length := by simpa only [hBadLen] using j.isLt
  simpa only [wordVector, List.getElem?_eq_getElem hGood, List.getElem?_eq_getElem hBad,
    Option.some.injEq] using hGet.symm

/-- Every sign position is sensitive even on valid formula encodings. -/
theorem valid_sign_sensitive (n : Nat) (i : Fin n) :
    ∃ x y : Fin (5 * n + 6) → Bool,
      (∃ F, CNFCode.decode (List.ofFn x) = some F) ∧
      (∃ F, CNFCode.decode (List.ofFn y) = some F) ∧
      List.ofFn x ∈ CNFSAT ∧ List.ofFn y ∉ CNFSAT ∧
      ∀ j : Fin (5 * n + 6), j.val ≠ 5 * i.val + 7 → x j = y j := by
  let before := List.replicate i.val true
  let after := List.replicate (n - (i.val + 1)) true
  let good := CNFCode.encode (signFormula (before ++ true :: after))
  let bad := CNFCode.encode (signFormula (before ++ false :: after))
  have hSignCount (b : Bool) : (before ++ b :: after).length = n := by
    have hi := i.isLt
    simp only [before, after, List.length_append, List.length_cons, List.length_replicate]
    omega
  have hGoodLen : good.length = 5 * n + 6 := by
    simp only [good, encode_signFormula_length, hSignCount]
  have hBadLen : bad.length = 5 * n + 6 := by
    simp only [bad, encode_signFormula_length, hSignCount]
  refine ⟨wordVector good hGoodLen, wordVector bad hBadLen, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ofFn_wordVector]
    exact ⟨_, CNFCode.decode_encode _⟩
  · rw [ofFn_wordVector]
    exact ⟨_, CNFCode.decode_encode _⟩
  · simp only [ofFn_wordVector, good, encode_signFormula_mem_CNFSAT]
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact (List.mem_replicate.mp hb).2
    · rcases List.mem_cons.mp hb with eq | hb
      · exact eq
      · exact (List.mem_replicate.mp hb).2
  · simp only [ofFn_wordVector, bad, encode_signFormula_mem_CNFSAT]
    intro h
    exact Bool.false_ne_true (h false (List.mem_append_right _ (List.mem_cons_self ..)))
  · intro j hj
    have hFlip : bad = good.set (5 * i.val + 7) false := by
      simpa only [before, List.length_replicate] using encode_signFormula_flip before after
    exact wordVector_set_other hGoodLen hBadLen hFlip j hj

private theorem encode_three_units_length (a b c : Nat) (s t u : Bool) :
    (CNFCode.encode [unitClause a s, unitClause b t, unitClause c u]).length = a + b + c + 16 := by
  simp only [encode_unit_cons, CNFCode.encode_nil, List.length_append, unitBlock_length,
    List.length_cons, List.length_nil]
  omega

private theorem unsatisfiable_conflicting_units {F : CNF.Formula Nat}
    (hp : [.pos 0] ∈ F) (hn : [.neg 0] ∈ F) : ¬ CNF.Satisfiable F := by
  rintro ⟨σ, h⟩
  have hPos : σ 0 = true := by simpa using h _ hp
  have hNeg : σ 0 = false := by simpa using h _ hn
  exact Bool.false_ne_true (hNeg.symm.trans hPos)

private theorem sensitive_of_encoding_flip {n : Nat} (i : Fin n) {F G : CNF.Formula Nat}
    (hLen : (CNFCode.encode F).length = n) (hSat : CNF.Satisfiable F) (hUnsat : ¬ CNF.Satisfiable G)
    (hFlip : CNFCode.encode G = (CNFCode.encode F).set i.val false) :
    ∃ x y : Fin n → Bool, List.ofFn x ∈ CNFSAT ∧ List.ofFn y ∉ CNFSAT ∧
      ∀ j : Fin n, j ≠ i → x j = y j := by
  have hLenG : (CNFCode.encode G).length = n := by simp only [hFlip, List.length_set, hLen]
  refine ⟨wordVector _ hLen, wordVector _ hLenG, ?_, ?_, ?_⟩
  · rw [ofFn_wordVector]
    exact (encode_mem_CNFSAT_iff F).mpr hSat
  · rw [ofFn_wordVector]
    exact fun h ↦ hUnsat ((encode_mem_CNFSAT_iff G).mp h)
  · intro j hNe
    exact wordVector_set_other hLen hLenG hFlip j (fun h ↦ hNe (Fin.ext h))

/-- The first and final unit signs can each flip satisfiability at every length at least sixteen. -/
theorem end_sign_sensitive {n : Nat} (i : Fin n) (hSize : 16 ≤ n)
    (hSign : i.val = 2 ∨ i.val + 4 = n) :
    ∃ x y : Fin n → Bool, List.ofFn x ∈ CNFSAT ∧ List.ofFn y ∉ CNFSAT ∧
      ∀ j : Fin n, j ≠ i → x j = y j := by
  let a := n - 16
  rcases hSign with hFirst | hLast
  · let F := [unitClause 0 true, unitClause 0 true, unitClause a true]
    let G := [unitClause 0 false, unitClause 0 true, unitClause a true]
    apply sensitive_of_encoding_flip i (F := F) (G := G)
    · simp only [F, encode_three_units_length, a]
      omega
    · exact ⟨fun _ ↦ true, by simp [F, unitClause]⟩
    · exact unsatisfiable_conflicting_units (by simp [G, unitClause]) (by simp [G, unitClause])
    · rw [hFirst]
      simp only [F, G, encode_unit_cons]
      rfl
  · let F := [unitClause a true, unitClause 0 true, unitClause 0 true]
    let G := [unitClause a true, unitClause 0 true, unitClause 0 false]
    apply sensitive_of_encoding_flip i (F := F) (G := G)
    · simp only [F, encode_three_units_length, a]
      omega
    · exact ⟨fun _ ↦ true, by simp [F, unitClause]⟩
    · exact unsatisfiable_conflicting_units (by simp [G, unitClause]) (by simp [G, unitClause])
    · let front := unitBlock a true ++ unitBlock 0 true
      have hFront : front.length + 2 = i.val := by
        simp only [front, List.length_append, unitBlock_length, a]
        omega
      simp only [F, G, encode_unit_cons, ← List.append_assoc (unitBlock a true) (unitBlock 0 true)]
      change front ++ (unitBlock 0 false ++ CNFCode.encode []) =
        (front ++ (unitBlock 0 true ++ CNFCode.encode [])).set i.val false
      rw [← hFront, List.set_append_right _ _ (Nat.le_add_right ..), Nat.add_sub_cancel_left]
      rfl

end PvsNP.SATCircuitBounds
