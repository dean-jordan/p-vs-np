module

public import PvsNP.CookLevin.Tableau

/-! # Size bound for computation tableaux

The bounds count literal occurrences and one delimiter per clause. Atom
names are still abstract; the cost of representing them as bits comes from
the binary encoding.
-/

@[expose] public section

namespace PvsNP.Tableau

variable {Q Γ : Type} {width : Nat}

/-- One positive clause and at most `n²` negative clauses of size three. -/
def oneHotSize (n : Nat) : Nat := n + 1 + 3 * n ^ 2

/-- A row has one state field, one head field, and one symbol field per cell. -/
def rowSizeBound (width states symbols : Nat) : Nat :=
  oneHotSize states + oneHotSize width + width * oneHotSize symbols

/-- A step has an update block per rule key and a copy block per head, cell, and symbol. -/
def stepSizeBound (width states symbols : Nat) : Nat :=
  states * (width * (symbols * 15)) + width * (width * (symbols * 4))

/-- A computation of `steps` transitions has `steps + 1` rows. -/
def traceSizeBound (steps width states symbols : Nat) : Nat :=
  (steps + 1) * rowSizeBound width states symbols + steps * stepSizeBound width states symbols

private theorem size_finRange_flatMap_le {α : Type} (n : Nat) (f : Fin n → CNF.Formula α)
    (B : Nat) (h : ∀ i, CNF.size (f i) ≤ B) :
    CNF.size ((List.finRange n).flatMap f) ≤ n * B := by
  simpa only [List.length_finRange] using
    CNF.size_flatMap_le (List.finRange n) f B (fun i _ ↦ h i)

private theorem size_exactlyOne_map_le {α β : Type} [DecidableEq α] (xs : List β) (f : β → α) :
    CNF.size (CNF.exactlyOne (xs.map f)) ≤ oneHotSize xs.length := by
  simpa only [List.length_map, oneHotSize] using CNF.size_exactlyOne_le (xs.map f)

/-- The shape constraints are bounded by the sizes of the one-hot fields. -/
theorem size_rowClauses_le [DecidableEq Q] [DecidableEq Γ]
    (qs : List Q) (symbols : List Γ) (t : Nat) :
    CNF.size (rowClauses (width := width) qs symbols t) ≤
      rowSizeBound width qs.length symbols.length := by
  simp only [rowClauses, CNF.size_append, rowSizeBound]
  apply Nat.add_le_add
  · exact Nat.add_le_add (size_exactlyOne_map_le qs (Atom.state t))
      (by simpa only [List.length_finRange] using
        size_exactlyOne_map_le (List.finRange width) (Atom.head (Q := Q) (Γ := Γ) t))
  · exact size_finRange_flatMap_le width _ _ fun i ↦
      size_exactlyOne_map_le symbols (Atom.cell t i)

/-- Three update clauses each have three guard literals and one conclusion. -/
theorem size_localUpdate (rule : Rule Q Γ width) (t : Nat) (q : Q) (i : Fin width) (a : Γ) :
    CNF.size (localUpdate rule t q i a) = 15 := by
  simp [localUpdate, CNF.size_guard]

/-- A copy clause has two guard literals and one conclusion, if a copy is needed. -/
theorem size_localCopy_le (t : Nat) (i j : Fin width) (a : Γ) :
    CNF.size (localCopy (Q := Q) t i j a) ≤ 4 := by
  by_cases h : i = j <;> simp [localCopy, h, CNF.size_guard]

/-- The rule-key and copy blocks separately have the sizes given in `stepSizeBound`. -/
theorem size_stepClauses_le (qs : List Q) (symbols : List Γ) (rule : Rule Q Γ width) (t : Nat) :
    CNF.size (stepClauses qs symbols rule t) ≤ stepSizeBound width qs.length symbols.length := by
  simp only [stepClauses, CNF.size_append, stepSizeBound]
  apply Nat.add_le_add
  · apply CNF.size_flatMap_le
    intro q _
    apply size_finRange_flatMap_le
    intro i
    apply CNF.size_flatMap_le
    exact fun a _ ↦ Nat.le_of_eq (size_localUpdate rule t q i a)
  · apply size_finRange_flatMap_le
    intro i
    apply size_finRange_flatMap_le
    intro j
    apply CNF.size_flatMap_le
    exact fun a _ ↦ size_localCopy_le t i j a

/-- The entire trace fits in an explicit polynomial in the construction parameters. -/
theorem size_traceClauses_le [DecidableEq Q] [DecidableEq Γ] (qs : List Q) (symbols : List Γ)
    (rule : Rule Q Γ width) (steps : Nat) :
    CNF.size (traceClauses qs symbols rule steps) ≤
      traceSizeBound steps width qs.length symbols.length := by
  simp only [traceClauses, CNF.size_append, traceSizeBound]
  apply Nat.add_le_add
  · simpa only [List.length_range] using
      CNF.size_flatMap_le (List.range (steps + 1)) (rowClauses qs symbols) _
        (fun t _ ↦ size_rowClauses_le (width := width) qs symbols t)
  · simpa only [List.length_range] using
      CNF.size_flatMap_le (List.range steps) (stepClauses qs symbols rule) _
        (fun t _ ↦ size_stepClauses_le qs symbols rule t)

/-- The initial constraints contribute their own size and the accepting unit clause costs two. -/
theorem size_acceptingClauses_le [DecidableEq Q] [DecidableEq Γ]
    (qs : List Q) (symbols : List Γ) (rule : Rule Q Γ width) (steps : Nat) (accept : Q)
    (initial : CNF.Formula (Atom Q Γ width)) :
    CNF.size (acceptingClauses qs symbols rule steps accept initial) ≤
      CNF.size initial + traceSizeBound steps width qs.length symbols.length + 2 := by
  simp only [acceptingClauses, CNF.size_append, CNF.size_cons, CNF.size_nil, List.length_cons,
    List.length_nil]
  exact Nat.add_le_add_right
    (Nat.add_le_add_left (size_traceClauses_le qs symbols rule steps) (CNF.size initial)) 2

end PvsNP.Tableau
