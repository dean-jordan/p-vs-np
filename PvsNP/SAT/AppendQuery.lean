module

public import PvsNP.SAT.SearchOracleQuery

/-! # SAT queries that append one unit clause at a time

Replace the final formula terminator with a unit clause and a new
terminator. Each new clause has one sign bit that can be updated in place.
-/

@[expose] public section

namespace PvsNP.SATSearch

/-- A unit clause followed by the formula terminator. -/
def appendUnitBlock (i : Nat) (b : Bool) : BinaryWord :=
  [true, true, b] ++ CNFCode.encodeIndex i ++ [false, false]

/-- Extend a formula word by fixing variable `i` to `b`. -/
def appendUnitQuery (word : BinaryWord) (i : Nat) (b : Bool) : BinaryWord :=
  word.dropLast ++ appendUnitBlock i b

private theorem encode_ne_nil (F : CNF.Formula Nat) : CNFCode.encode F ≠ [] := by
  cases F <;> simp [CNFCode.encode_cons]

private theorem dropLast_encode_append (F G : CNF.Formula Nat) :
    (CNFCode.encode F).dropLast ++ CNFCode.encode G = CNFCode.encode (F ++ G) := by
  induction F with
  | nil => simp
  | cons c F ih =>
    rw [CNFCode.encode_cons, List.cons_append, CNFCode.encode_cons]
    change (((true :: CNFCode.encodeClause c) ++ CNFCode.encode F).dropLast ++ CNFCode.encode G) =
      (true :: CNFCode.encodeClause c) ++ CNFCode.encode (F ++ G)
    rw [List.dropLast_append_of_ne_nil (encode_ne_nil F), List.append_assoc, ih]

theorem appendUnitBlock_eq_encode (i : Nat) (b : Bool) :
    appendUnitBlock i b = CNFCode.encode [[if b then .pos i else .neg i]] := by
  cases b <;> simp [appendUnitBlock, CNFCode.encode_cons, CNFCode.encodeClause_cons,
    CNFCode.encodeLiteral, List.append_assoc]

theorem appendUnitQuery_encode (F : CNF.Formula Nat) (i : Nat) (b : Bool) :
    appendUnitQuery (CNFCode.encode F) i b =
      CNFCode.encode (F ++ [[if b then .pos i else .neg i]]) := by
  rw [appendUnitQuery, appendUnitBlock_eq_encode, dropLast_encode_append]

@[simp] theorem length_appendUnitBlock (i : Nat) (b : Bool) :
    (appendUnitBlock i b).length = i + 6 := by
  simp only [appendUnitBlock, List.length_append, List.length_cons, List.length_nil,
    length_encodeQueryIndex]
  omega

@[simp] theorem length_appendUnitQuery (word : BinaryWord) (i : Nat) (b : Bool) :
    (appendUnitQuery word i b).length = word.dropLast.length + (i + 6) := by
  simp only [appendUnitQuery, List.length_append, length_appendUnitBlock]

theorem length_appendUnitQuery_of_ne_nil {word : BinaryWord} (hWord : word ≠ [])
    (i : Nat) (b : Bool) : (appendUnitQuery word i b).length = word.length + (i + 5) := by
  have hLength := List.length_pos_iff.mpr hWord
  rw [length_appendUnitQuery, List.length_dropLast]
  omega

/-- Updating the new unit clause's sign bit is exactly a change of its pinned value. -/
theorem appendUnitQuery_set_sign (word : BinaryWord) (i : Nat) (trial bit : Bool) :
    (appendUnitQuery word i trial).set (word.dropLast.length + 2) bit =
      appendUnitQuery word i bit := by
  change (word.dropLast ++ appendUnitBlock i trial).set (word.dropLast.length + 2) bit = _
  rw [List.set_append_right _ _ (Nat.le_add_right ..), Nat.add_sub_cancel_left]
  rfl

/-- Extend a formula word with a prefix of assignments starting at index `i`. -/
def appendPrefixQueryFrom : Nat → BinaryWord → BinaryWord → BinaryWord
  | _, word, [] => word
  | i, word, bit :: pref => appendPrefixQueryFrom (i + 1) (appendUnitQuery word i bit) pref

/-- Extend a formula word with assignments to variables beginning at zero. -/
def appendPrefixQuery (word pref : BinaryWord) : BinaryWord := appendPrefixQueryFrom 0 word pref

@[simp] theorem appendPrefixQuery_nil (word : BinaryWord) : appendPrefixQuery word [] = word :=
  rfl

theorem appendPrefixQueryFrom_append (i : Nat) (word pref suffix : BinaryWord) :
    appendPrefixQueryFrom i word (pref ++ suffix) =
      appendPrefixQueryFrom (i + pref.length) (appendPrefixQueryFrom i word pref) suffix := by
  induction pref generalizing i word with
  | nil => simp [appendPrefixQueryFrom]
  | cons bit pref ih =>
    simp only [List.cons_append, appendPrefixQueryFrom, ih, List.length_cons]
    have hIndex : i + 1 + pref.length = i + (pref.length + 1) := by omega
    rw [hIndex]

/-- One new prefix bit adds just one block to the current query. -/
theorem appendPrefixQuery_append_bit (word pref : BinaryWord) (bit : Bool) :
    appendPrefixQuery word (pref ++ [bit]) =
      appendUnitQuery (appendPrefixQuery word pref) pref.length bit := by
  simp only [appendPrefixQuery, appendPrefixQueryFrom_append, Nat.zero_add, appendPrefixQueryFrom]

theorem appendPrefixQueryFrom_encode (i : Nat) (F : CNF.Formula Nat) (pref : BinaryWord) :
    appendPrefixQueryFrom i (CNFCode.encode F) pref =
      CNFCode.encode (F ++ prefixClausesFrom i pref) := by
  induction pref generalizing i F with
  | nil => simp [appendPrefixQueryFrom, prefixClausesFrom]
  | cons bit pref ih =>
    rw [appendPrefixQueryFrom, appendUnitQuery_encode, ih]
    simp only [prefixClausesFrom, List.append_assoc, List.singleton_append]

theorem appendPrefixQuery_encode (F : CNF.Formula Nat) (pref : BinaryWord) :
    appendPrefixQuery (CNFCode.encode F) pref = CNFCode.encode (F ++ prefixClausesFrom 0 pref) :=
  appendPrefixQueryFrom_encode 0 F pref

private theorem prefixQueryFrom_encode (i : Nat) (F : CNF.Formula Nat) (pref : BinaryWord) :
    prefixQueryFrom i (CNFCode.encode F) pref = CNFCode.encode (prefixClausesFrom i pref ++ F) :=
  CNFCode.decode_eq_some_iff.mp (by simp [decode_prefixQueryFrom])

/-- On a well-formed word, adding the prefix clauses on either end gives the same SAT answer. -/
theorem appendPrefixQueryFrom_mem_CNFSAT_iff (i : Nat) (word pref : BinaryWord)
    (hWellFormed : ∃ F, CNFCode.decode word = some F) :
    appendPrefixQueryFrom i word pref ∈ CNFSAT ↔ prefixQueryFrom i word pref ∈ CNFSAT := by
  obtain ⟨F, hF⟩ := hWellFormed
  rw [CNFCode.decode_eq_some_iff.mp hF, appendPrefixQueryFrom_encode, prefixQueryFrom_encode]
  simp only [encode_mem_CNFSAT_iff, CNF.Satisfiable, CNF.sat_append, and_comm]

theorem appendPrefixQuery_mem_CNFSAT_iff (word pref : BinaryWord)
    (hWellFormed : ∃ F, CNFCode.decode word = some F) :
    appendPrefixQuery word pref ∈ CNFSAT ↔ prefixQuery word pref ∈ CNFSAT :=
  appendPrefixQueryFrom_mem_CNFSAT_iff 0 word pref hWellFormed

private theorem length_encode_append_comm (F G : CNF.Formula Nat) :
    (CNFCode.encode (F ++ G)).length = (CNFCode.encode (G ++ F)).length := by
  rw [← dropLast_encode_append F G, ← dropLast_encode_append G F]
  simp only [List.length_append, List.length_dropLast]
  have hF := List.length_pos_iff.mpr (encode_ne_nil F)
  have hG := List.length_pos_iff.mpr (encode_ne_nil G)
  omega

theorem length_appendPrefixQuery_eq_prefixQuery (word pref : BinaryWord)
    (hWellFormed : ∃ F, CNFCode.decode word = some F) :
    (appendPrefixQuery word pref).length = (prefixQuery word pref).length := by
  obtain ⟨F, hF⟩ := hWellFormed
  rw [CNFCode.decode_eq_some_iff.mp hF, appendPrefixQuery_encode, prefixQuery,
    prefixQueryFrom_encode]
  exact length_encode_append_comm F (prefixClausesFrom 0 pref)

end PvsNP.SATSearch
