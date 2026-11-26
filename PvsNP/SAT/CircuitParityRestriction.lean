module

public import PvsNP.SAT.BinaryLanguage

/-! # Pairwise XNOR and AND restrictions of binary CNF-SAT

Two units on the same variable enforce equality of their signs. An
additional positive unit on that variable forces both signs to be true.
Padding places the two variable signs at the selected coordinates.
-/

public section

namespace PvsNP.SATCircuitBounds

open CNFCode

private def unit (index : Nat) (sign : Bool) : CNF.Clause Nat :=
  [if sign then .pos index else .neg index]

private def unitBits (index : Nat) (sign : Bool) : BinaryWord :=
  [true, true, sign] ++ encodeIndex index ++ [false]

private theorem encode_unit_cons (index : Nat) (sign : Bool) (tail : CNF.Formula Nat) :
    encode (unit index sign :: tail) = unitBits index sign ++ encode tail := by
  cases sign <;> simp [unit, unitBits, encode_cons, encodeClause_cons, encodeLiteral,
    List.append_assoc]

private theorem length_encodeIndex (index : Nat) : (encodeIndex index).length = index + 1 := by
  induction index with
  | zero => rfl
  | succ index ih => simp only [encodeIndex, List.length_cons, ih]

private theorem length_unitBits (index : Nat) (sign : Bool) :
    (unitBits index sign).length = index + 5 := by
  simp only [unitBits, List.length_append, List.length_cons, List.length_nil, length_encodeIndex]
  omega

private theorem unit_sat (σ : Nat → Bool) (index : Nat) (sign : Bool) :
    CNF.Clause.Sat σ (unit index sign) ↔ σ index = sign := by
  cases sign <;> simp [unit]

private def positiveBits (indices : List Nat) : BinaryWord :=
  indices.flatMap (fun index ↦ unitBits index true)

private theorem encode_positive_append (indices : List Nat) (tail : CNF.Formula Nat) :
    encode (indices.map (fun index ↦ unit index true) ++ tail) =
      positiveBits indices ++ encode tail := by
  induction indices with
  | nil => rfl
  | cons index indices ih =>
    change encode (unit index true :: (indices.map (fun j ↦ unit j true) ++ tail)) =
      (unitBits index true ++ positiveBits indices) ++ encode tail
    rw [encode_unit_cons, ih, List.append_assoc]

private def beforeBits (pre : Nat) : BinaryWord := unitBits pre true ++ [true, true]

private def betweenBits (target : Nat) (middle : List Nat) : BinaryWord :=
  encodeIndex target ++ [false] ++ positiveBits middle ++ [true, true]

private def anchorUnits (target : Nat) (forceTrue : Bool) : List Nat :=
  if forceTrue then [target] else []

private def afterBits (target post : Nat) (forceTrue : Bool) : BinaryWord :=
  encodeIndex target ++ [false] ++ positiveBits (anchorUnits target forceTrue) ++
    unitBits post true ++ [false]

private def pairWord (pre target post : Nat) (middle : List Nat) (forceTrue a b : Bool) :
    BinaryWord :=
  beforeBits pre ++ a :: (betweenBits target middle ++ b :: afterBits target post forceTrue)

private def pairFormula (pre target post : Nat) (middle : List Nat) (forceTrue a b : Bool) :
    CNF.Formula Nat :=
  unit pre true :: unit target a ::
    (middle.map (fun index ↦ unit index true) ++
      unit target b :: ((anchorUnits target forceTrue).map (fun index ↦ unit index true) ++
        [unit post true]))

private theorem pairWord_eq_encode (pre target post : Nat) (middle : List Nat)
    (forceTrue a b : Bool) :
    pairWord pre target post middle forceTrue a b =
      encode (pairFormula pre target post middle forceTrue a b) := by
  simp [pairWord, pairFormula, encode_unit_cons, encode_positive_append, beforeBits, betweenBits,
    afterBits, unitBits, List.append_assoc]

private theorem length_beforeBits (pre : Nat) : (beforeBits pre).length = pre + 7 := by
  simp only [beforeBits, List.length_append, length_unitBits, List.length_cons, List.length_nil]

private theorem length_betweenBits (target : Nat) (middle : List Nat) :
    (betweenBits target middle).length = target + 4 + (positiveBits middle).length := by
  simp only [betweenBits, List.length_append, length_encodeIndex, List.length_cons, List.length_nil]
  omega

private theorem length_anchorBits (target : Nat) (forceTrue : Bool) :
    (positiveBits (anchorUnits target forceTrue)).length = if forceTrue then target + 5 else 0 := by
  cases forceTrue <;> simp [positiveBits, anchorUnits, length_unitBits]

private theorem length_afterBits (target post : Nat) (forceTrue : Bool) :
    (afterBits target post forceTrue).length =
      target + post + 8 + (if forceTrue then target + 5 else 0) := by
  simp only [afterBits, List.length_append, length_encodeIndex, length_unitBits, List.length_cons,
    List.length_nil, length_anchorBits]
  omega

private theorem length_pairWord (pre target post : Nat) (middle : List Nat)
    (forceTrue a b : Bool) :
    (pairWord pre target post middle forceTrue a b).length =
      pre + 2 * target + post + (positiveBits middle).length + 21 +
        (if forceTrue then target + 5 else 0) := by
  simp only [pairWord, List.length_append, List.length_cons, length_beforeBits,
    length_betweenBits, length_afterBits]
  omega

private theorem anchor_sat (σ : Nat → Bool) (target : Nat) (forceTrue : Bool) :
    (∀ i ∈ anchorUnits target forceTrue, σ i = true) ↔ (forceTrue = true → σ target = true) := by
  cases forceTrue <;> simp [anchorUnits]

private theorem pairWord_mem_CNFSAT_iff (pre target post : Nat) (middle : List Nat)
    (hPre : pre ≠ target) (hPost : post ≠ target) (hMiddle : ∀ i ∈ middle, i ≠ target)
    (forceTrue a b : Bool) :
    pairWord pre target post middle forceTrue a b ∈ CNFSAT ↔
      a = b ∧ (forceTrue = true → a = true) := by
  rw [pairWord_eq_encode, encode_mem_CNFSAT_iff]
  simp only [CNF.Satisfiable, pairFormula, CNF.sat_cons, CNF.sat_append, CNF.sat_map,
    unit_sat, CNF.sat_nil, and_true, anchor_sat]
  constructor
  · rintro ⟨σ, _, ha, _, hb, hAnchor, _⟩
    exact ⟨ha.symm.trans hb, fun hForce ↦ ha.symm.trans (hAnchor hForce)⟩
  · rintro ⟨rfl, hAnchor⟩
    let σ (i : Nat) := if i = target then a else true
    exact ⟨σ, by simp [σ, hPre], by simp [σ], fun i hi ↦ by simp [σ, hMiddle i hi],
      by simp [σ], by simpa [σ] using hAnchor, by simp [σ, hPost]⟩

private def parityInput {n : Nat} (word : BinaryWord) (h : word.length = n) : Fin n → Bool :=
  fun l ↦ word[l.val]'(by simpa only [h] using l.isLt)

private theorem ofFn_parityInput {n : Nat} (word : BinaryWord) (h : word.length = n) :
    List.ofFn (parityInput word h) = word := by
  subst n
  exact List.ofFn_getElem

private def HasUnitRestriction {n : Nat} (u v : Fin n) (forceTrue : Bool) : Prop :=
  ∃ x : Bool → Bool → Fin n → Bool,
    (∀ a b, x a b u = a) ∧ (∀ a b, x a b v = b) ∧
    (∀ a b l, l ≠ u → l ≠ v → x a b l = x false false l) ∧
    ∀ a b, List.ofFn (x a b) ∈ CNFSAT ↔ a = b ∧ (forceTrue = true → a = true)

private theorem restriction_of_units {n : Nat} (u v : Fin n) (hDistinct : u ≠ v)
    (pre target post : Nat) (middle : List Nat) (forceTrue : Bool)
    (hPre : pre ≠ target) (hPost : post ≠ target) (hMiddle : ∀ i ∈ middle, i ≠ target)
    (hLeft : u.val = (beforeBits pre).length)
    (hRight : v.val = (beforeBits pre).length + 1 + (betweenBits target middle).length)
    (hLength : pre + 2 * target + post + (positiveBits middle).length + 21 +
      (if forceTrue then target + 5 else 0) = n) :
    HasUnitRestriction u v forceTrue := by
  let word := pairWord pre target post middle forceTrue
  have hSize (a b : Bool) : (word a b).length = n :=
    (length_pairWord pre target post middle forceTrue a b).trans hLength
  let x (a b : Bool) := parityInput (word a b) (hSize a b)
  have hBits (a b : Bool) (l : Fin n) : (word a b)[l.val]? = some (x a b l) :=
    List.getElem?_eq_getElem (by rw [hSize]; exact l.isLt)
  have hSetLeft (a b : Bool) : word a b = (word false b).set u.val a := by
    change pairWord pre target post middle forceTrue a b =
      (pairWord pre target post middle forceTrue false b).set u.val a
    simp only [pairWord, hLeft, List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self,
      List.set_cons_zero]
  have hSplit (a b : Bool) :
      word a b = (beforeBits pre ++ a :: betweenBits target middle) ++
        b :: afterBits target post forceTrue := by
    simp [word, pairWord, List.append_assoc]
  have hSetRight (a b : Bool) : word a b = (word a false).set v.val b := by
    have hFront : (beforeBits pre ++ a :: betweenBits target middle).length = v.val := by
      simp only [hRight, List.length_append, List.length_cons]
      omega
    rw [hSplit a b, hSplit a false, ← hFront,
      List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self, List.set_cons_zero]
  have hDifferent : v.val ≠ u.val := fun e ↦ hDistinct (Fin.ext e.symm)
  refine ⟨x, ?_, ?_, ?_, ?_⟩
  · intro a b
    apply Option.some.inj
    rw [← hBits, hSetRight, hSetLeft, List.getElem?_set_ne hDifferent,
      List.getElem?_set_self (by rw [hSize]; exact u.isLt)]
  · intro a b
    apply Option.some.inj
    rw [← hBits, hSetRight, List.getElem?_set_self (by rw [hSize]; exact v.isLt)]
  · intro a b l hu hv
    apply Option.some.inj
    rw [← hBits, ← hBits, hSetRight, hSetLeft,
      List.getElem?_set_ne (fun eq ↦ hv (Fin.ext eq.symm)),
      List.getElem?_set_ne (fun eq ↦ hu (Fin.ext eq.symm))]
  · intro a b
    rw [show List.ofFn (x a b) = word a b from ofFn_parityInput ..]
    exact pairWord_mem_CNFSAT_iff pre target post middle hPre hPost hMiddle forceTrue a b

private theorem long_pair_restriction {n : Nat} (i j : Fin n) (forceTrue : Bool)
    (hLeft : 13 ≤ i.val) (hRight : j.val + 22 + (if forceTrue then 10 else 0) ≤ n)
    (hGapMin : 5 ≤ j.val - i.val) : HasUnitRestriction i j forceTrue := by
  let gap := j.val - i.val
  let target := if gap ≤ 10 then gap - 5 else 0
  let middle : List Nat := if 11 ≤ gap then [gap - 10] else []
  let pre := i.val - 7
  let extra := if forceTrue then target + 5 else 0
  let post := n - (j.val + 9 + target + extra)
  have hTarget : target ≤ 5 := by dsimp only [target]; split <;> omega
  have hExtra : extra ≤ (if forceTrue then 10 else 0) := by
    cases forceTrue with
    | false => exact Nat.le_refl _
    | true => change target + 5 ≤ 10; omega
  have hGap : target + 5 + (positiveBits middle).length = gap := by
    by_cases hLong : 11 ≤ gap
    · have hNotShort : ¬gap ≤ 10 := by omega
      simp only [target, hNotShort, ite_false, middle, hLong, ite_true, positiveBits,
        List.flatMap_singleton, length_unitBits]
      omega
    · have hShort : gap ≤ 10 := by omega
      simp only [target, hShort, ite_true, middle, hLong, ite_false, positiveBits,
        List.flatMap_nil, List.length_nil]
      omega
  apply restriction_of_units i j (fun h ↦ by have hv := congrArg Fin.val h; omega)
    pre target post middle forceTrue
  · dsimp [pre]
    omega
  · dsimp [post]
    omega
  · intro v hv
    by_cases hLong : 11 ≤ gap
    · have hNotShort : ¬gap ≤ 10 := by omega
      simp only [middle, hLong, ite_true, List.mem_singleton] at hv
      simp only [target, hNotShort, ite_false]
      omega
    · simp [middle, hLong] at hv
  · simp only [length_beforeBits, pre]
    omega
  · rw [length_beforeBits, length_betweenBits]
    dsimp [gap, pre] at *
    omega
  · change pre + 2 * target + post + (positiveBits middle).length + 21 + extra = n
    dsimp [gap, pre, post] at *
    omega

/-- Two well-separated internal coordinates can be signs of units on one variable. -/
theorem cnfsat_long_pair_xnor {n : Nat} (i j : Fin n) (hLeft : 13 ≤ i.val)
    (hRight : j.val + 22 ≤ n) (hGapMin : 5 ≤ j.val - i.val) :
    ∃ x : Bool → Bool → Fin n → Bool,
      (∀ a b, x a b i = a) ∧ (∀ a b, x a b j = b) ∧
      (∀ a b u, u ≠ i → u ≠ j → x a b u = x false false u) ∧
      ∀ a b, List.ofFn (x a b) ∈ CNFSAT ↔ a = b := by
  obtain ⟨x, hI, hJ, hOther, hSat⟩ :=
    long_pair_restriction i j false hLeft hRight hGapMin
  exact ⟨x, hI, hJ, hOther, fun a b ↦ by simpa using hSat a b⟩

/-- A fixed positive unit on the target variable makes both selected signs necessary. -/
theorem cnfsat_long_pair_and {n : Nat} (i j : Fin n) (hLeft : 13 ≤ i.val)
    (hRight : j.val + 32 ≤ n) (hGapMin : 5 ≤ j.val - i.val) :
    ∃ x : Bool → Bool → Fin n → Bool,
      (∀ a b, x a b i = a) ∧ (∀ a b, x a b j = b) ∧
      (∀ a b u, u ≠ i → u ≠ j → x a b u = x false false u) ∧
      ∀ a b, List.ofFn (x a b) ∈ CNFSAT ↔ a = true ∧ b = true := by
  obtain ⟨x, hI, hJ, hOther, hSat⟩ :=
    long_pair_restriction i j true hLeft (by change j.val + 22 + 10 ≤ n; omega) hGapMin
  refine ⟨x, hI, hJ, hOther, fun a b ↦ (hSat a b).trans ?_⟩
  constructor
  · rintro ⟨hEqual, hForce⟩
    exact ⟨hForce rfl, hEqual.symm.trans (hForce rfl)⟩
  · rintro ⟨ha, hb⟩
    exact ⟨ha.trans hb.symm, fun _ ↦ ha⟩

end PvsNP.SATCircuitBounds
