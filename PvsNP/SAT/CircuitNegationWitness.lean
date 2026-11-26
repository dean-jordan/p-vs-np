module

public import PvsNP.SAT.BinaryLanguage

/-! # A monotone chain of CNF inputs with alternating satisfiability -/

public section

namespace PvsNP.SATCircuitBounds

private def signedLiteral (a : Nat) (b : Bool) : CNF.Literal Nat :=
  if b then .pos a else .neg a

private def signedUnit (a : Nat) (b : Bool) : CNF.Clause Nat := [signedLiteral a b]

private def unitBlock (a : Nat) (b : Bool) : BinaryWord :=
  true :: true :: b :: (CNFCode.encodeIndex a ++ [false])

private theorem encode_unit_cons (a : Nat) (b : Bool) (F : CNF.Formula Nat) :
    CNFCode.encode (signedUnit a b :: F) = unitBlock a b ++ CNFCode.encode F := by
  cases b <;> simp [signedUnit, signedLiteral, unitBlock, CNFCode.encode_cons,
    CNFCode.encodeClause_cons, CNFCode.encodeLiteral]

private theorem unitBlock_length (a : Nat) (b : Bool) : (unitBlock a b).length = a + 5 := by
  have h := CNFCode.length_encodeLiteral (.pos a)
  simp only [CNFCode.encodeLiteral, CNFCode.literalIndex, List.length_cons] at h
  simp only [unitBlock, List.length_cons, List.length_append, List.length_nil]
  omega

private theorem signedUnit_sat (σ : Nat → Bool) (a : Nat) (b : Bool) :
    (signedUnit a b).Sat σ ↔ σ a = b := by
  cases b <;> simp [signedUnit, signedLiteral]

private def mixedClause (b c : Bool) : CNF.Clause Nat := [signedLiteral 0 b, signedLiteral 1 c]

private def mixedBlock (b c : Bool) : BinaryWord :=
  [true, true, b, false, true, c, true, false, false]

private theorem encode_mixed_cons (b c : Bool) (F : CNF.Formula Nat) :
    CNFCode.encode (mixedClause b c :: F) = mixedBlock b c ++ CNFCode.encode F := by
  cases b <;> cases c <;>
    simp [mixedClause, mixedBlock, signedLiteral, CNFCode.encode_cons, CNFCode.encodeClause_cons,
      CNFCode.encodeLiteral, CNFCode.encodeIndex]

private def mixedClauses : Nat → Nat → CNF.Formula Nat
  | 0, _ => []
  | k + 1, t => mixedClause (decide (2 * k < t)) (decide (2 * k + 1 < t)) :: mixedClauses k t

private def paddedFormula (k t p : Nat) : CNF.Formula Nat :=
  signedUnit 0 false :: signedUnit 1 true :: signedUnit p (decide (p ≠ 0)) :: mixedClauses k t

private abbrev pairWord (n k t : Nat) : BinaryWord :=
  CNFCode.encode (paddedFormula k t (n - (9 * k + 17)))

private theorem encode_mixedClauses_length (k t : Nat) :
    (CNFCode.encode (mixedClauses k t)).length = 9 * k + 1 := by
  induction k with
  | zero => simp [mixedClauses]
  | succ k ih =>
    simp only [mixedClauses, encode_mixed_cons, List.length_append, mixedBlock, List.length_cons,
      List.length_nil, ih]
    omega

private theorem pairWord_length (n k t : Nat) (hSize : 9 * k + 17 ≤ n) :
    (pairWord n k t).length = n := by
  simp only [pairWord, paddedFormula, encode_unit_cons, List.length_append, unitBlock_length,
    encode_mixedClauses_length]
  omega

private theorem mixedClause_sat (σ : Nat → Bool) (h0 : σ 0 = false) (h1 : σ 1 = true)
    (b c : Bool) : (mixedClause b c).Sat σ ↔ b = false ∨ c = true := by
  cases b <;> cases c <;> simp [mixedClause, signedLiteral, h0, h1]

private theorem mixedClauses_sat (σ : Nat → Bool) (h0 : σ 0 = false) (h1 : σ 1 = true)
    (k t : Nat) : CNF.Sat σ (mixedClauses k t) ↔ ∀ a < k, ¬ 2 * a < t ∨ 2 * a + 1 < t := by
  induction k with
  | zero => simp [mixedClauses]
  | succ k ih =>
    simp only [mixedClauses, CNF.sat_cons, mixedClause_sat σ h0 h1, decide_eq_false_iff_not,
      decide_eq_true_eq, ih]
    constructor
    · rintro ⟨hAt, hRest⟩ a ha
      by_cases eq : a = k
      · simpa only [eq] using hAt
      · exact hRest a (by omega)
    · intro h
      exact ⟨h k (Nat.lt_succ_self k), fun a ha ↦ h a (Nat.lt_succ_of_lt ha)⟩

private theorem paddedFormula_satisfiable (k t p : Nat) (hTime : t ≤ 2 * k) :
    CNF.Satisfiable (paddedFormula k t p) ↔ t % 2 = 0 := by
  constructor
  · rintro ⟨σ, hSat⟩
    simp only [paddedFormula, CNF.sat_cons, signedUnit_sat] at hSat
    obtain ⟨h0, h1, _, hClauses⟩ := hSat
    by_contra hEven
    let a := t / 2
    have ha : a < k := by
      dsimp only [a]
      omega
    have hFirst : 2 * a < t := by
      dsimp only [a]
      omega
    have hSecond : ¬ 2 * a + 1 < t := by
      dsimp only [a]
      omega
    exact ((mixedClauses_sat σ h0 h1 k t).mp hClauses a ha).elim
      (fun h ↦ h hFirst) hSecond
  · intro hEven
    let σ (a : Nat) := decide (a ≠ 0)
    have h0 : σ 0 = false := rfl
    have h1 : σ 1 = true := rfl
    refine ⟨σ, ?_⟩
    simp only [paddedFormula, CNF.sat_cons, signedUnit_sat]
    refine ⟨h0, h1, rfl, (mixedClauses_sat σ h0 h1 k t).mpr ?_⟩
    intro a _
    omega

private def BitsLe (xs ys : BinaryWord) : Prop :=
  ∀ i : Nat, xs[i]? = some true → ys[i]? = some true

private theorem bitsLe_cons {b c : Bool} {xs ys : BinaryWord}
    (h : b = true → c = true) (hs : BitsLe xs ys) : BitsLe (b :: xs) (c :: ys) := by
  intro i
  cases i with
  | zero => simpa using h
  | succ i => simpa using hs i

private theorem bitsLe_append {x y xs ys : BinaryWord} (hLen : x.length = y.length)
    (h : BitsLe x y) (hs : BitsLe xs ys) : BitsLe (x ++ xs) (y ++ ys) := by
  intro i hBit
  by_cases hi : i < x.length
  · have hj : i < y.length := by simpa only [← hLen] using hi
    rw [List.getElem?_append_left hi] at hBit
    rw [List.getElem?_append_left hj]
    exact h i hBit
  · have hx : x.length ≤ i := Nat.le_of_not_gt hi
    have hy : y.length ≤ i := by simpa only [← hLen] using hx
    rw [List.getElem?_append_right hx] at hBit
    rw [List.getElem?_append_right hy, ← hLen]
    exact hs (i - x.length) hBit

private theorem mixedBlock_bitsLe {b c b' c' : Bool}
    (hb : b = true → b' = true) (hc : c = true → c' = true) :
    BitsLe (mixedBlock b c) (mixedBlock b' c') := by
  unfold mixedBlock
  apply bitsLe_cons id
  apply bitsLe_cons id
  apply bitsLe_cons hb
  apply bitsLe_cons id
  apply bitsLe_cons id
  exact bitsLe_cons hc (fun _ ↦ id)

private theorem decide_lt_mono {a t u : Nat} (h : t ≤ u) :
    decide (a < t) = true → decide (a < u) = true := by
  simp only [decide_eq_true_eq]
  exact fun ha ↦ Nat.lt_of_lt_of_le ha h

private theorem encode_mixedClauses_bitsLe (k : Nat) {t u : Nat} (h : t ≤ u) :
    BitsLe (CNFCode.encode (mixedClauses k t)) (CNFCode.encode (mixedClauses k u)) := by
  induction k with
  | zero => exact fun _ ↦ id
  | succ k ih =>
    simp only [mixedClauses, encode_mixed_cons]
    exact bitsLe_append rfl (mixedBlock_bitsLe (decide_lt_mono h) (decide_lt_mono h)) ih

private theorem pairWord_bitsLe (n k : Nat) {t u : Nat} (h : t ≤ u) :
    BitsLe (pairWord n k t) (pairWord n k u) := by
  simp only [pairWord, paddedFormula, encode_unit_cons]
  exact bitsLe_append rfl (fun _ ↦ id)
    (bitsLe_append rfl (fun _ ↦ id)
      (bitsLe_append rfl (fun _ ↦ id) (encode_mixedClauses_bitsLe k h)))

/-- Successive inputs change two signs per clause under fixed assignments to variables zero
and one. A consistent unit clause pads the encoding to length exactly n. -/
def pairChain (n k : Nat) (hSize : 9 * k + 17 ≤ n)
    (t : Fin (2 * k + 1)) (j : Fin n) : Bool :=
  (pairWord n k t.val)[j.val]'(by simpa only [pairWord_length n k t.val hSize] using j.isLt)

private theorem ofFn_pairChain (n k : Nat) (hSize : 9 * k + 17 ≤ n) (t : Fin (2 * k + 1)) :
    List.ofFn (pairChain n k hSize t) = pairWord n k t.val := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, pairWord_length n k t.val hSize]
  · intro i hi _
    simp only [List.getElem_ofFn, pairChain]

/-- Every word in the chain is the complete encoding of a formula. -/
theorem pairChain_decodes (n k : Nat) (hSize : 9 * k + 17 ≤ n) (t : Fin (2 * k + 1)) :
    ∃ F, CNFCode.decode (List.ofFn (pairChain n k hSize t)) = some F := by
  rw [ofFn_pairChain]
  exact ⟨_, CNFCode.decode_encode _⟩

/-- No bit changes from true to false between successive inputs. -/
theorem pairChain_monotone (n k : Nat) (hSize : 9 * k + 17 ≤ n)
    (i : Fin (2 * k)) (j : Fin n) :
    pairChain n k hSize i.castSucc j = true → pairChain n k hSize i.succ j = true := by
  have h0 : j.val < (pairWord n k i.val).length := by
    simpa only [pairWord_length n k i.val hSize] using j.isLt
  have h1 : j.val < (pairWord n k (i.val + 1)).length := by
    simpa only [pairWord_length n k (i.val + 1) hSize] using j.isLt
  simpa only [List.getElem?_eq_getElem h0, List.getElem?_eq_getElem h1, Option.some.injEq,
    pairChain, Fin.val_castSucc, Fin.val_succ] using pairWord_bitsLe n k (Nat.le_succ i.val) j.val

/-- The chain is satisfiable exactly at its even steps. -/
theorem pairChain_mem_iff (n k : Nat) (hSize : 9 * k + 17 ≤ n) (t : Fin (2 * k + 1)) :
    List.ofFn (pairChain n k hSize t) ∈ CNFSAT ↔ t.val % 2 = 0 := by
  rw [ofFn_pairChain]
  exact (encode_mem_CNFSAT_iff _).trans
    (paddedFormula_satisfiable k t.val _ (Nat.le_of_lt_succ t.isLt))

end PvsNP.SATCircuitBounds
