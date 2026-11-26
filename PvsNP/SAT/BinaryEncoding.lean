module

public import PvsNP.SAT.CNF

/-! # A binary code for CNF formulas

A list of items is written as one `1` before each encoded item and a final
`0`. Formulas frame a list of clauses, and clauses frame a list of literals.
A literal consists of a sign bit followed by a unary index, written as that
many `1` bits followed by a `0`.
-/

public section

namespace PvsNP.CNFCode

open CNF (Clause Formula Literal)

/-- The natural-number index printed by a literal. -/
@[expose] def literalIndex : Literal Nat → Nat
  | .pos a => a
  | .neg a => a

/-- A unary index followed by its terminating zero. -/
@[expose] def encodeIndex : Nat → List Bool
  | 0 => [false]
  | n + 1 => true :: encodeIndex n

/-- A sign bit followed by the code of the variable index. -/
@[expose] def encodeLiteral : Literal Nat → List Bool
  | .pos a => true :: encodeIndex a
  | .neg a => false :: encodeIndex a

private def encodeList {α : Type} (encodeItem : α → List Bool) : List α → List Bool
  | [] => [false]
  | a :: xs => true :: (encodeItem a ++ encodeList encodeItem xs)

/-- The framed list of literals in a clause. -/
def encodeClause (c : Clause Nat) : List Bool := encodeList encodeLiteral c

/-- Encode the formula as a finite binary word. -/
def encode (F : Formula Nat) : List Bool := encodeList encodeClause F

@[simp] theorem encodeClause_nil : encodeClause [] = [false] := by unfold encodeClause; rfl

theorem encodeClause_cons (l : Literal Nat) (c : Clause Nat) :
    encodeClause (l :: c) = true :: (encodeLiteral l ++ encodeClause c) := by
  unfold encodeClause
  rfl

@[simp] theorem encode_nil : encode [] = [false] := by unfold encode; rfl

theorem encode_cons (c : Clause Nat) (F : Formula Nat) :
    encode (c :: F) = true :: (encodeClause c ++ encode F) := by
  unfold encode
  rfl

private def parseIndex : List Bool → Option (Nat × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => (parseIndex rest).map fun (a, tail) ↦ (a + 1, tail)

private def parseLiteral : List Bool → Option (Literal Nat × List Bool)
  | [] => none
  | sign :: rest => (parseIndex rest).map fun (a, tail) ↦
    (if sign then .pos a else .neg a, tail)

private def parseListWithFuel {α : Type} (parseItem : List Bool → Option (α × List Bool)) :
    Nat → List Bool → Option (List α × List Bool)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, false :: rest => some ([], rest)
  | fuel + 1, true :: rest => (parseItem rest).bind fun (a, tail) ↦
    (parseListWithFuel parseItem fuel tail).map fun (xs, suffix) ↦ (a :: xs, suffix)

private def parseList {α : Type} (parseItem : List Bool → Option (α × List Bool))
    (bits : List Bool) : Option (List α × List Bool) :=
  parseListWithFuel parseItem bits.length bits

private def parseClause (bits : List Bool) : Option (Clause Nat × List Bool) :=
  parseList parseLiteral bits

/-- Read one formula from the front of a word and return the unconsumed bits. -/
def parsePrefix (bits : List Bool) : Option (Formula Nat × List Bool) :=
  parseList parseClause bits

/-- Read a whole formula word, failing on malformed input or trailing bits. -/
def decode (bits : List Bool) : Option (Formula Nat) :=
  (parsePrefix bits).bind fun (F, rest) ↦ if rest.isEmpty then some F else none

private theorem parseIndex_encode_append (a : Nat) (rest : List Bool) :
    parseIndex (encodeIndex a ++ rest) = some (a, rest) := by
  induction a with
  | zero => rfl
  | succ a ih => simp only [encodeIndex, List.cons_append, parseIndex, ih, Option.map_some]

private theorem parseIndex_sound {bits rest : List Bool} {a : Nat}
    (h : parseIndex bits = some (a, rest)) : bits = encodeIndex a ++ rest := by
  induction bits generalizing a rest with
  | nil => simp [parseIndex] at h
  | cons bit bits ih =>
    cases bit with
    | false =>
      simp only [parseIndex, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    | true =>
      cases parsed : parseIndex bits with
      | none => simp [parseIndex, parsed] at h
      | some cursor =>
        obtain ⟨n, suffix⟩ := cursor
        simp only [parseIndex, parsed, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact congrArg (List.cons true) (ih parsed)

private theorem parseLiteral_encode_append (l : Literal Nat) (rest : List Bool) :
    parseLiteral (encodeLiteral l ++ rest) = some (l, rest) := by
  cases l <;> simp [encodeLiteral, parseLiteral, parseIndex_encode_append]

private theorem parseLiteral_sound {bits rest : List Bool} {l : Literal Nat}
    (h : parseLiteral bits = some (l, rest)) : bits = encodeLiteral l ++ rest := by
  cases bits with
  | nil => simp [parseLiteral] at h
  | cons bit bits =>
    cases parsed : parseIndex bits with
    | none => simp [parseLiteral, parsed] at h
    | some cursor =>
      obtain ⟨n, suffix⟩ := cursor
      simp only [parseLiteral, parsed, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [parseIndex_sound parsed]
      cases bit <;> rfl

private theorem itemCount_lt_length {α : Type} (encodeItem : α → List Bool) (xs : List α) :
    xs.length < (encodeList encodeItem xs).length := by
  induction xs with
  | nil => simp [encodeList]
  | cons a xs ih =>
    simp only [List.length_cons, encodeList, List.length_append]
    omega

private theorem parseListWithFuel_encode_append {α : Type} (encodeItem : α → List Bool)
    (parseItem : List Bool → Option (α × List Bool))
    (itemCorrect : ∀ a tail, parseItem (encodeItem a ++ tail) = some (a, tail))
    (xs : List α) (rest : List Bool) {fuel : Nat} (fuelEnough : xs.length < fuel) :
    parseListWithFuel parseItem fuel (encodeList encodeItem xs ++ rest) = some (xs, rest) := by
  induction xs generalizing fuel with
  | nil => cases fuel <;> simp_all [encodeList, parseListWithFuel]
  | cons a xs ih =>
    cases fuel with
    | zero => simp at fuelEnough
    | succ fuel =>
      have ih' := ih (Nat.lt_of_succ_lt_succ fuelEnough)
      simp only [encodeList, List.cons_append, List.append_assoc, parseListWithFuel,
        itemCorrect, Option.bind_some, ih', Option.map_some]

private theorem parseListWithFuel_sound {α : Type} (encodeItem : α → List Bool)
    (parseItem : List Bool → Option (α × List Bool))
    (itemSound : ∀ {a bits rest}, parseItem bits = some (a, rest) → bits = encodeItem a ++ rest)
    (fuel : Nat) {xs : List α} {bits rest : List Bool}
    (h : parseListWithFuel parseItem fuel bits = some (xs, rest)) :
    bits = encodeList encodeItem xs ++ rest := by
  induction fuel generalizing xs bits rest with
  | zero => simp [parseListWithFuel] at h
  | succ fuel ih =>
    cases bits with
    | nil => simp [parseListWithFuel] at h
    | cons bit bits =>
      cases bit with
      | false =>
        simp only [parseListWithFuel, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rfl
      | true =>
        cases item : parseItem bits with
        | none => simp [parseListWithFuel, item] at h
        | some cursor =>
          obtain ⟨a, tail⟩ := cursor
          cases items : parseListWithFuel parseItem fuel tail with
          | none => simp [parseListWithFuel, item, items] at h
          | some cursor =>
            obtain ⟨ys, suffix⟩ := cursor
            simp only [parseListWithFuel, item, items, Option.bind_some, Option.map_some,
              Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rw [itemSound item, ih items, encodeList, List.cons_append, List.append_assoc]

private theorem parseList_encode_append {α : Type} (encodeItem : α → List Bool)
    (parseItem : List Bool → Option (α × List Bool))
    (itemCorrect : ∀ a tail, parseItem (encodeItem a ++ tail) = some (a, tail))
    (xs : List α) (rest : List Bool) :
    parseList parseItem (encodeList encodeItem xs ++ rest) = some (xs, rest) := by
  apply parseListWithFuel_encode_append encodeItem parseItem itemCorrect
  have h := itemCount_lt_length encodeItem xs
  rw [List.length_append]
  omega

private theorem parseClause_encode_append (c : Clause Nat) (rest : List Bool) :
    parseClause (encodeClause c ++ rest) = some (c, rest) :=
  parseList_encode_append encodeLiteral parseLiteral parseLiteral_encode_append c rest

private theorem parseClause_sound {c : Clause Nat} {bits rest : List Bool}
    (h : parseClause bits = some (c, rest)) : bits = encodeClause c ++ rest :=
  parseListWithFuel_sound encodeLiteral parseLiteral parseLiteral_sound bits.length h

/-- Prefix parsing identifies exactly one complete formula and leaves the suffix untouched. -/
theorem parsePrefix_eq_some_iff {F : Formula Nat} {bits rest : List Bool} :
    parsePrefix bits = some (F, rest) ↔ bits = encode F ++ rest := by
  refine ⟨parseListWithFuel_sound encodeClause parseClause parseClause_sound bits.length, ?_⟩
  rintro rfl
  exact parseList_encode_append encodeClause parseClause parseClause_encode_append F rest

/-- A parser result requires the entire word to be the code of that formula. -/
theorem decode_eq_some_iff {F : Formula Nat} {bits : List Bool} :
    decode bits = some F ↔ bits = encode F := by
  constructor
  · intro h
    cases parsed : parsePrefix bits with
    | none => simp [decode, parsed] at h
    | some cursor =>
      obtain ⟨G, rest⟩ := cursor
      cases rest with
      | nil =>
        have hEq : G = F := by simpa [decode, parsed] using h
        simpa only [List.append_nil, hEq] using parsePrefix_eq_some_iff.mp parsed
      | cons b rest => simp [decode, parsed] at h
  · rintro rfl
    have parsed : parsePrefix (encode F) = some (F, []) :=
      parsePrefix_eq_some_iff.mpr (List.append_nil _).symm
    simp [decode, parsed]

@[simp] theorem decode_encode (F : Formula Nat) : decode (encode F) = some F :=
  decode_eq_some_iff.mpr rfl

/-- A framed clause is prepended to a decoded formula, and malformed suffixes still fail. -/
theorem decode_prepend_clause (c : Clause Nat) (word : List Bool) :
    decode (true :: (encodeClause c ++ word)) = (decode word).map (c :: ·) := by
  cases hWord : decode word with
  | some F =>
    apply decode_eq_some_iff.mpr
    rw [decode_eq_some_iff.mp hWord, encode_cons]
  | none =>
    cases hPrefix : decode (true :: (encodeClause c ++ word)) with
    | none => rfl
    | some F =>
      have hCode := decode_eq_some_iff.mp hPrefix
      cases F with
      | nil => simp at hCode
      | cons d F =>
        rw [encode_cons] at hCode
        have hParse := congrArg parseClause (List.cons.inj hCode).2
        rw [parseClause_encode_append, parseClause_encode_append] at hParse
        have hSuffix : word = encode F := (Prod.mk.inj (Option.some.inj hParse)).2
        have hImpossible : none = some F := hWord.symm.trans (decode_eq_some_iff.mpr hSuffix)
        cases hImpossible

/-- A valid formula prefix followed by any nonempty suffix is rejected. -/
theorem decode_encode_append (F : Formula Nat) (rest : List Bool) :
    decode (encode F ++ rest) = if rest.isEmpty then some F else none := by
  have h : parsePrefix (encode F ++ rest) = some (F, rest) := parsePrefix_eq_some_iff.mpr rfl
  simp [decode, h]

/-- Different formulas have different binary codes. -/
theorem encode_injective : Function.Injective encode := by
  intro F G h
  have hd := congrArg decode h
  simpa only [decode_encode, Option.some.injEq] using hd

private theorem length_encodeIndex (a : Nat) : (encodeIndex a).length = a + 1 := by
  induction a with
  | zero => rfl
  | succ a ih => simp only [encodeIndex, List.length_cons, ih]

/-- A sign and a unary terminator add two bits to the index length. -/
theorem length_encodeLiteral (l : Literal Nat) :
    (encodeLiteral l).length = literalIndex l + 2 := by
  cases l <;> simp only [encodeLiteral, literalIndex, List.length_cons, length_encodeIndex]

private theorem length_item_le_encodeList {α : Type} (encodeItem : α → List Bool)
    {xs : List α} {a : α} (h : a ∈ xs) :
    (encodeItem a).length ≤ (encodeList encodeItem xs).length := by
  induction xs with
  | nil => simp at h
  | cons b bs ih =>
    simp only [encodeList, List.length_cons, List.length_append]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have h := ih h
      omega

/-- Each variable index in a formula is smaller than the length of its binary code. -/
theorem literalIndex_lt_length_encode {F : Formula Nat} {c : Clause Nat} {l : Literal Nat}
    (hc : c ∈ F) (hl : l ∈ c) : literalIndex l < (encode F).length := by
  have hLiteral : (encodeLiteral l).length ≤ (encodeClause c).length :=
    length_item_le_encodeList encodeLiteral hl
  have hClause : (encodeClause c).length ≤ (encode F).length :=
    length_item_le_encodeList encodeClause hc
  rw [length_encodeLiteral] at hLiteral
  omega

private theorem length_encodeClause_le (c : Clause Nat) (B : Nat)
    (bound : ∀ l ∈ c, literalIndex l ≤ B) : (encodeClause c).length ≤ 1 + (B + 3) * c.length := by
  induction c with
  | nil => simp [encodeClause, encodeList]
  | cons l c ih =>
    have hl := bound l (List.mem_cons_self ..)
    have hc := ih fun l hl ↦ bound l (List.mem_cons_of_mem _ hl)
    change (true :: (encodeLiteral l ++ encodeClause c)).length ≤ 1 + (B + 3) * (c.length + 1)
    simp only [List.length_cons, List.length_append, length_encodeLiteral, Nat.mul_add, Nat.mul_one]
    omega

/-- Bounded unary indices give a bit-length bound linear in the CNF symbol count. -/
theorem length_encode_le (F : Formula Nat) (B : Nat)
    (bound : ∀ c ∈ F, ∀ l ∈ c, literalIndex l ≤ B) :
    (encode F).length ≤ 1 + (B + 3) * CNF.size F := by
  induction F with
  | nil => simp [encode, encodeList]
  | cons c F ih =>
    have hc := length_encodeClause_le c B (bound c (List.mem_cons_self ..))
    have hF := ih fun d hd ↦ bound d (List.mem_cons_of_mem _ hd)
    change (true :: (encodeClause c ++ encode F)).length ≤ 1 + (B + 3) * (c.length + 1 + CNF.size F)
    simp only [List.length_cons, List.length_append, Nat.mul_add, Nat.mul_one]
    omega

end PvsNP.CNFCode
