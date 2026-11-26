module

public import PvsNP.SAT.BinaryLanguage

/-! # SAT queries that fix an assignment prefix

Each additional unit clause fixes one variable via its sign bit. The clauses
are prepended directly to the input word, so the same construction also sends
malformed formula words to malformed queries.
-/

@[expose] public section

namespace PvsNP.SATSearch

/-- Prepend unit clauses fixing consecutive variables beginning at `i`. -/
def prefixQueryFrom : Nat → BinaryWord → BinaryWord → BinaryWord
  | _, word, [] => word
  | i, word, bit :: pref =>
    [true, true, bit] ++ CNFCode.encodeIndex i ++ [false] ++ prefixQueryFrom (i + 1) word pref

@[simp] theorem prefixQueryFrom_nil (i : Nat) (word : BinaryWord) :
    prefixQueryFrom i word [] = word := rfl

theorem prefixQueryFrom_cons (i : Nat) (word : BinaryWord) (bit : Bool) (pref : BinaryWord) :
    prefixQueryFrom i word (bit :: pref) =
      [true, true, bit] ++ CNFCode.encodeIndex i ++ [false] ++ prefixQueryFrom (i + 1) word pref :=
  rfl

/-- Fix variables numbered from zero onward. -/
def prefixQuery (word pref : BinaryWord) : BinaryWord := prefixQueryFrom 0 word pref

@[simp] theorem prefixQuery_nil (word : BinaryWord) : prefixQuery word [] = word := rfl

/-- Length of a query from word length `n` and `k` pinned variables beginning at `i`. -/
def prefixQueryLengthFrom : Nat → Nat → Nat → Nat
  | _, n, 0 => n
  | i, n, k + 1 => i + 5 + prefixQueryLengthFrom (i + 1) n k

@[simp] theorem prefixQueryLengthFrom_nil (i n : Nat) : prefixQueryLengthFrom i n 0 = n :=
  rfl

theorem prefixQueryLengthFrom_cons (i n k : Nat) :
    prefixQueryLengthFrom i n (k + 1) = i + 5 + prefixQueryLengthFrom (i + 1) n k :=
  rfl

/-- Length of a query fixing a prefix of length `k`. -/
def prefixQueryLength (n k : Nat) : Nat := prefixQueryLengthFrom 0 n k

theorem length_encodeQueryIndex (i : Nat) : (CNFCode.encodeIndex i).length = i + 1 := by
  have h := CNFCode.length_encodeLiteral (.pos i)
  simp only [CNFCode.encodeLiteral, CNFCode.literalIndex, List.length_cons] at h
  omega

/-- Query length depends only on the two input lengths and the initial index. -/
@[simp] theorem length_prefixQueryFrom (i : Nat) (word pref : BinaryWord) :
    (prefixQueryFrom i word pref).length = prefixQueryLengthFrom i word.length pref.length := by
  induction pref generalizing i with
  | nil => rfl
  | cons bit pref ih =>
    rw [prefixQueryFrom_cons]
    simp only [List.length_append, List.length_cons, List.length_nil, length_encodeQueryIndex,
      prefixQueryLengthFrom_cons, ih]
    omega

@[simp] theorem length_prefixQuery (word pref : BinaryWord) :
    (prefixQuery word pref).length = prefixQueryLength word.length pref.length :=
  length_prefixQueryFrom 0 word pref

theorem prefixQueryLengthFrom_le (i n k : Nat) :
    prefixQueryLengthFrom i n k ≤ n + k * (i + k + 5) := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [prefixQueryLengthFrom_cons, Nat.succ_mul]
    have h := ih (i + 1)
    have hIndex : i + 1 + k + 5 = i + (k + 1) + 5 := by omega
    rw [hIndex] at h
    omega

theorem prefixQueryLength_le (n k : Nat) (hk : k ≤ n) :
    prefixQueryLength n k ≤ n + n * (n + 5) := by
  unfold prefixQueryLength
  refine (prefixQueryLengthFrom_le 0 n k).trans (Nat.add_le_add_left ?_ n)
  simpa only [Nat.zero_add] using Nat.mul_le_mul hk (Nat.add_le_add_right hk 5)

/-- Any family of prefixes of length at most its formula length yields polynomial query lengths. -/
theorem prefixQueryLength_polynomiallyBounded (k : Nat → Nat) (hk : ∀ n, k n ≤ n) :
    PolynomiallyBounded (fun n ↦ prefixQueryLength n (k n)) :=
  (PolynomiallyBounded.id.add
    (PolynomiallyBounded.id.mul (PolynomiallyBounded.id.add (PolynomiallyBounded.const 5)))).mono
      (fun n ↦ prefixQueryLength_le n (k n) (hk n))

/-- The clauses encoded by the query prefix. -/
def prefixClausesFrom : Nat → BinaryWord → CNF.Formula Nat
  | _, [] => []
  | i, bit :: pref =>
    [if bit then .pos i else .neg i] :: prefixClausesFrom (i + 1) pref

private theorem unitPrefix_eq (i : Nat) (bit : Bool) (rest : BinaryWord) :
    [true, true, bit] ++ CNFCode.encodeIndex i ++ [false] ++ rest =
      true :: (CNFCode.encodeClause [if bit then .pos i else .neg i] ++ rest) := by
  cases bit <;> simp [CNFCode.encodeClause_cons, CNFCode.encodeLiteral, List.append_assoc]

/-- Decoding the query prepends the unit clauses to the result of decoding the input. -/
theorem decode_prefixQueryFrom (i : Nat) (word pref : BinaryWord) :
    CNFCode.decode (prefixQueryFrom i word pref) =
      (CNFCode.decode word).map (fun F ↦ prefixClausesFrom i pref ++ F) := by
  induction pref generalizing i with
  | nil =>
    rw [prefixQueryFrom_nil]
    cases CNFCode.decode word <;> rfl
  | cons bit pref ih =>
    rw [prefixQueryFrom_cons, unitPrefix_eq, CNFCode.decode_prepend_clause, ih]
    cases CNFCode.decode word <;> rfl

theorem decode_prefixQuery (word pref : BinaryWord) :
    CNFCode.decode (prefixQuery word pref) =
      (CNFCode.decode word).map (fun F ↦ prefixClausesFrom 0 pref ++ F) :=
  decode_prefixQueryFrom 0 word pref

private theorem sat_unit_bit (σ : Nat → Bool) (i : Nat) (bit : Bool) :
    CNF.Clause.Sat σ [if bit then .pos i else .neg i] ↔ σ i = bit := by
  cases bit <;> simp

theorem sat_prefixClausesFrom_iff (σ : Nat → Bool) (i : Nat) (pref : BinaryWord) :
    CNF.Sat σ (prefixClausesFrom i pref) ↔
      ∀ j : Fin pref.length, σ (i + j.val) = pref[j.val] := by
  induction pref generalizing i with
  | nil => simp [prefixClausesFrom]
  | cons bit pref ih =>
    rw [prefixClausesFrom, CNF.sat_cons, sat_unit_bit, ih]
    have hIndex (j : Fin pref.length) : i + (j.val + 1) = i + 1 + j.val := by omega
    constructor
    · rintro ⟨hHead, hTail⟩ j
      refine Fin.cases ?_ (fun a ↦ ?_) j
      · simpa using hHead
      · simpa only [hIndex, Fin.val_succ, List.getElem_cons_succ] using hTail a
    · intro h
      refine ⟨?_, fun a ↦ ?_⟩
      · simpa using h 0
      · simpa only [hIndex, Fin.val_succ, List.getElem_cons_succ] using h a.succ

/-- A yes answer certifies a satisfying assignment extending the supplied prefix. -/
theorem prefixQuery_mem_CNFSAT_iff (word pref : BinaryWord) :
    prefixQuery word pref ∈ CNFSAT ↔
      ∃ F, CNFCode.decode word = some F ∧
        ∃ σ, CNF.Sat σ F ∧ (∀ i : Fin pref.length, σ i.val = pref[i.val]) := by
  change (∃ F, CNFCode.decode (prefixQuery word pref) = some F ∧ CNF.Satisfiable F) ↔ _
  rw [decode_prefixQuery]
  cases CNFCode.decode word with
  | none => simp
  | some F =>
    simp only [Option.map_some, Option.some.injEq, exists_eq_left', CNF.Satisfiable, CNF.sat_append,
      sat_prefixClausesFrom_iff, Nat.zero_add, and_comm]

end PvsNP.SATSearch
