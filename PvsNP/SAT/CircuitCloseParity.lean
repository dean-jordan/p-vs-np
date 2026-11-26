module

public import PvsNP.SAT.BinaryLanguage

/-! # XOR and OR restrictions at nearby coordinates of binary CNF-SAT -/

public section

namespace PvsNP.SATCircuitBounds

open CNFCode

private def signed (index : Nat) (sign : Bool) : CNF.Literal Nat :=
  if sign then .pos index else .neg index

private def unitBits (index : Nat) (sign : Bool) : BinaryWord :=
  [true, true, sign] ++ List.replicate index true ++ [false, false]

private theorem length_unitBits (index : Nat) (sign : Bool) :
    (unitBits index sign).length = index + 5 := by
  simp [unitBits]

private theorem encodeIndex_replicate (index : Nat) :
    encodeIndex index = List.replicate index true ++ [false] := by
  induction index with
  | zero => rfl
  | succ index ih => simp only [encodeIndex, ih, List.replicate_succ, List.cons_append]

private theorem encode_signed_unit_cons (index : Nat) (sign : Bool) (rest : CNF.Formula Nat) :
    encode ([signed index sign] :: rest) = unitBits index sign ++ encode rest := by
  cases sign <;> simp [signed, unitBits, encode_cons, encodeClause_cons, encodeLiteral,
    encodeIndex_replicate, List.append_assoc]

private def closeClauses (r : Nat) (a b fixed : Bool) : CNF.Formula Nat :=
  if b then [[signed (r + 1) a, .pos (r + 1)], [signed (r + 1) fixed]]
  else [[signed r a], [.pos r], [signed (r + 1) fixed]]

private theorem true_cons_replicate_append (r : Nat) (rest : BinaryWord) :
    true :: (List.replicate r true ++ rest) = List.replicate r true ++ true :: rest := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [List.replicate_succ, List.cons_append, ih]

private theorem encode_closeClauses (r : Nat) (a b fixed : Bool) (rest : CNF.Formula Nat) :
    encode (closeClauses r a b fixed ++ rest) =
      [true, true, a] ++ List.replicate r true ++ [b, false] ++
        unitBits r true ++ unitBits (r + 1) fixed ++ encode rest := by
  cases a <;> cases b <;> cases fixed <;>
    simp [closeClauses, signed, unitBits, encode_cons, encodeClause_cons, encodeLiteral,
      encodeIndex_replicate, List.replicate_succ, List.append_assoc, true_cons_replicate_append]

private theorem sat_closeClauses (σ : Nat → Bool) (r : Nat) (a b fixed : Bool) :
    CNF.Sat σ (closeClauses r a b fixed) ↔
      σ (r + 1) = fixed ∧
        (if b then a = fixed ∨ fixed = true else σ r = a ∧ σ r = true) := by
  cases a <;> cases b <;> cases fixed <;> cases h : σ (r + 1) <;>
    simp [closeClauses, signed, h, and_comm]

private theorem closeFormula_satisfiable (r before after : Nat) (a b fixed : Bool)
    (hBefore : r + 1 < before) (hAfter : r + 1 < after) :
    CNF.Satisfiable ([.pos before] :: (closeClauses r a b fixed ++ [[.pos after]])) ↔
      if fixed then a = true ∨ b = true else a ≠ b := by
  simp only [CNF.Satisfiable, CNF.sat_cons, CNF.sat_append, CNF.Clause.sat_singleton,
    CNF.Literal.sat_pos, CNF.sat_nil, and_true, sat_closeClauses]
  constructor
  · rintro ⟨σ, _, ⟨_, hValue⟩, _⟩
    cases a <;> cases b <;> cases fixed <;> simp_all
  · intro hSat
    let σ (v : Nat) : Bool := if v = r + 1 then fixed else true
    have hRead : σ (r + 1) = fixed := by simp [σ]
    have hTrue : σ r = true := by simp [σ]
    have hBeforeTrue : σ before = true := by simp [σ, show before ≠ r + 1 by omega]
    have hAfterTrue : σ after = true := by simp [σ, show after ≠ r + 1 by omega]
    refine ⟨σ, hBeforeTrue, ⟨hRead, ?_⟩, hAfterTrue⟩
    cases a <;> cases b <;> cases fixed <;> simp_all

private def pairWord (front middle back : BinaryWord) (a b : Bool) : BinaryWord :=
  front ++ a :: (middle ++ b :: back)

private theorem pairWord_set_left (front middle back : BinaryWord) (a b : Bool) :
    pairWord front middle back a b = (pairWord front middle back false b).set front.length a := by
  rw [pairWord, pairWord, List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self,
    List.set_cons_zero]

private theorem pairWord_set_right (front middle back : BinaryWord) (a b : Bool) :
    pairWord front middle back a b =
      (pairWord front middle back a false).set (front.length + 1 + middle.length) b := by
  rw [pairWord, pairWord, List.set_append_right _ _ (by omega),
    show front.length + 1 + middle.length - front.length = middle.length + 1 by omega,
    List.set_cons_succ, List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self, List.set_cons_zero]

private def wordInput {n : Nat} (word : BinaryWord) (hLength : word.length = n)
    (i : Fin n) : Bool := word[i.val]'(by rw [hLength]; exact i.isLt)

private theorem ofFn_wordInput {n : Nat} (word : BinaryWord) (hLength : word.length = n) :
    List.ofFn (wordInput word hLength) = word := by
  subst n
  exact List.ofFn_getElem

private theorem cnfsat_close_pair_with_pin {n : Nat} (i j : Fin n) (fixed : Bool)
    (hEarly : 13 ≤ i.val)
    (hLate : j.val + 30 ≤ n) (hPos : i.val < j.val) (hClose : j.val - i.val ≤ 4) :
    ∃ x : Bool → Bool → Fin n → Bool,
      (∀ a b, x a b i = a) ∧ (∀ a b, x a b j = b) ∧
      (∀ a b u, u ≠ i → u ≠ j → x a b u = x false false u) ∧
      ∀ a b, List.ofFn (x a b) ∈ CNFSAT ↔ if fixed then a = true ∨ b = true else a ≠ b := by
  let r := j.val - i.val - 1
  let p := i.val - 7
  let q := n - (i.val + 3 * r + 20)
  let front := unitBits p true ++ [true, true]
  let middle := List.replicate r true
  let back := false :: (unitBits r true ++ unitBits (r + 1) fixed ++ encode [[.pos q]])
  let word := pairWord front middle back
  have hFront : front.length = i.val := by
    simp only [front, List.length_append, length_unitBits, List.length_cons, List.length_nil, p]
    omega
  have hMiddle : front.length + 1 + middle.length = j.val := by
    simp only [hFront, middle, List.length_replicate, r]
    omega
  have hLength (a b : Bool) : (word a b).length = n := by
    simp only [word, pairWord, List.length_append, List.length_cons, hFront,
      middle, back, List.length_replicate, length_unitBits]
    rw [show encode [[.pos q]] = unitBits q true ++ [false] from
      (encode_signed_unit_cons q true []).trans (congrArg (unitBits q true ++ ·) encode_nil)]
    simp only [List.length_append, length_unitBits, List.length_cons, List.length_nil, q, r]
    omega
  let x (a b : Bool) := wordInput (word a b) (hLength a b)
  have hGet (a b : Bool) (u : Fin n) : (word a b)[u.val]? = some (x a b u) :=
    List.getElem?_eq_getElem (by rw [hLength]; exact u.isLt)
  have hLeft (a b : Bool) : word a b = (word false b).set i.val a := by
    rw [← hFront]
    exact pairWord_set_left front middle back a b
  have hRight (a b : Bool) : word a b = (word a false).set j.val b := by
    rw [← hMiddle]
    exact pairWord_set_right front middle back a b
  refine ⟨x, ?_, ?_, ?_, ?_⟩
  · intro a b
    apply Option.some.inj
    rw [← hGet, hLeft, List.getElem?_set_self (by rw [hLength]; exact i.isLt)]
  · intro a b
    apply Option.some.inj
    rw [← hGet, hRight, List.getElem?_set_self (by rw [hLength]; exact j.isLt)]
  · intro a b u hi hj
    apply Option.some.inj
    rw [← hGet, ← hGet, hLeft a b, hRight false b,
      List.getElem?_set_ne (fun he ↦ hi (Fin.ext he.symm)),
      List.getElem?_set_ne (fun he ↦ hj (Fin.ext he.symm))]
  · intro a b
    rw [show List.ofFn (x a b) = word a b from ofFn_wordInput ..]
    have hEncoded : encode ([.pos p] :: (closeClauses r a b fixed ++ [[.pos q]])) = word a b := by
      change encode ([signed p true] :: (closeClauses r a b fixed ++ [[.pos q]])) = word a b
      rw [encode_signed_unit_cons, encode_closeClauses]
      simp [word, pairWord, front, middle, back, List.append_assoc]
    rw [← hEncoded, encode_mem_CNFSAT_iff]
    exact closeFormula_satisfiable r p q a b fixed
      (by dsimp [r, p]; omega) (by dsimp [r, q]; omega)

/-- Two nearby bits can switch between clause and literal boundaries, giving XOR. -/
theorem cnfsat_close_pair_xor {n : Nat} (i j : Fin n) (hEarly : 13 ≤ i.val)
    (hLate : j.val + 30 ≤ n) (hPos : i.val < j.val) (hClose : j.val - i.val ≤ 4) :
    ∃ x : Bool → Bool → Fin n → Bool,
      (∀ a b, x a b i = a) ∧ (∀ a b, x a b j = b) ∧
      (∀ a b u, u ≠ i → u ≠ j → x a b u = x false false u) ∧
      ∀ a b, List.ofFn (x a b) ∈ CNFSAT ↔ a ≠ b := by
  simpa only [Bool.false_eq_true, ite_false] using
    cnfsat_close_pair_with_pin i j false hEarly hLate hPos hClose

/-- Using a positive fixed unit in the same layout gives OR. -/
theorem cnfsat_close_pair_or {n : Nat} (i j : Fin n) (hEarly : 13 ≤ i.val)
    (hLate : j.val + 30 ≤ n) (hPos : i.val < j.val) (hClose : j.val - i.val ≤ 4) :
    ∃ x : Bool → Bool → Fin n → Bool,
      (∀ a b, x a b i = a) ∧ (∀ a b, x a b j = b) ∧
      (∀ a b u, u ≠ i → u ≠ j → x a b u = x false false u) ∧
      ∀ a b, List.ofFn (x a b) ∈ CNFSAT ↔ a = true ∨ b = true := by
  simpa only [ite_true] using cnfsat_close_pair_with_pin i j true hEarly hLate hPos hClose

end PvsNP.SATCircuitBounds
