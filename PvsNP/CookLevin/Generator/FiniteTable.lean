module

public import PvsNP.CookLevin.BinaryReduction
public import Init.Data.Vector.OfFn

/-!
# Finite constants for the binary tableau generator

The verifier's state and symbol types are relabeled using their enumeration
indices. In a local transition, the state and symbol determine the table
entry. The only input-dependent operation on the head is the bounded move
specified by that entry.
-/

@[expose] public section

namespace PvsNP.CookLevin

/-- An indexed transition, with no movement after the verifier halts. -/
structure IndexedTransition (qCount symbolCount : Nat) where
  next : Fin qCount
  written : Fin symbolCount
  move : Option Turing.Dir

/-- All the verifier-specific constants used to generate its indexed tableau. -/
structure FiniteTable (qCount symbolCount certificateCount : Nat) where
  entries : Vector (Vector (IndexedTransition qCount symbolCount) symbolCount) qCount
  initial : Fin qCount
  accept : Fin qCount
  reject : Fin qCount
  blank : Fin symbolCount
  bitZero : Fin symbolCount
  bitOne : Fin symbolCount
  separator : Fin symbolCount
  certificates : Vector (Fin symbolCount) certificateCount

variable {qCount symbolCount certificateCount : Nat}

namespace FiniteTable

variable (table : FiniteTable qCount symbolCount certificateCount)

/-- Look up an entry by control state and scanned symbol. -/
def entry (q : Fin qCount) (read : Fin symbolCount) : IndexedTransition qCount symbolCount :=
  table.entries[q.val][read.val]

/-- The indexed tape symbol for a bit of the instance word. -/
def bit (b : Bool) : Fin symbolCount :=
  if b then table.bitOne else table.bitZero

/-- The indexed tape symbol for a certificate letter. -/
def certificate (c : Fin certificateCount) : Fin symbolCount :=
  table.certificates[c.val]

/-- The indexed input prefix consists of the instance followed by its separator. -/
def fixedPrefix (x : BinaryWord) : List (Fin symbolCount) :=
  x.map table.bit ++ [table.separator]

/-- Apply a fixed transition entry at any position in the bounded tape window. -/
def windowAdvance {width : Nat} :
    Tableau.Rule (Fin qCount) (Fin symbolCount) width :=
  fun q head read ↦
    let entry := table.entry q read
    ⟨entry.next, entry.move.elim head (fun dir ↦ Machine.windowMoveHead dir head), entry.written⟩

end FiniteTable

variable {A : CheckingAlphabet} (M : Machine A.Symbol)
    (qIndex : M.State ⊕ Bool ≃ Fin qCount) (sIndex : M.Symbol ≃ Fin symbolCount)
    (cIndex : A.Certificate ≃ Fin certificateCount)

/-- Extract the constant indexed transitions and input symbols of the verifier. -/
def finiteTable : FiniteTable qCount symbolCount certificateCount where
  entries := Vector.ofFn fun q ↦ Vector.ofFn fun read ↦
    match qIndex.symm q with
    | .inr _ => ⟨q, read, none⟩
    | .inl state =>
      let ⟨next, written, dir⟩ := M.transition state (sIndex.symm read)
      ⟨qIndex next, sIndex written, some dir⟩
  initial := qIndex (.inl M.initial)
  accept := qIndex (.inr true)
  reject := qIndex (.inr false)
  blank := sIndex M.blank
  bitZero := sIndex (M.input (A.bit false))
  bitOne := sIndex (M.input (A.bit true))
  separator := sIndex (M.input A.separator)
  certificates := Vector.ofFn fun c ↦ sIndex (M.input (A.certificate (cIndex.symm c)))

@[simp] theorem finiteTable_entry_halted (b : Bool) (read : Fin symbolCount) :
    (finiteTable M qIndex sIndex cIndex).entry (qIndex (.inr b)) read =
      ⟨qIndex (.inr b), read, none⟩ := by
  simp [FiniteTable.entry, finiteTable]

@[simp] theorem finiteTable_entry_running (q : M.State) (read : M.Symbol) :
    (finiteTable M qIndex sIndex cIndex).entry (qIndex (.inl q)) (sIndex read) =
      let ⟨next, written, dir⟩ := M.transition q read
      ⟨qIndex next, sIndex written, some dir⟩ := by
  simp [FiniteTable.entry, finiteTable]

/-- The indexed table preserves the whole local update, including endpoint behavior. -/
theorem finiteTable_windowAdvance {width : Nat} (q : M.State ⊕ Bool)
    (head : Fin width) (read : M.Symbol) :
    (finiteTable M qIndex sIndex cIndex).windowAdvance (qIndex q) head (sIndex read) =
      let next := M.windowAdvance width q head read
      ⟨qIndex next.1, next.2.1, sIndex next.2.2⟩ := by
  cases q with
  | inl q =>
    simp only [FiniteTable.windowAdvance, finiteTable_entry_running, Machine.windowAdvance]
    cases M.transition q read with
    | mk next rest =>
      cases rest
      rfl
  | inr b =>
    simp [FiniteTable.windowAdvance, Machine.windowAdvance]

@[simp] theorem finiteTable_bit (b : Bool) :
    (finiteTable M qIndex sIndex cIndex).bit b = sIndex (M.input (A.bit b)) := by
  cases b <;> rfl

@[simp] theorem finiteTable_certificate (c : Fin certificateCount) :
    (finiteTable M qIndex sIndex cIndex).certificate c =
      sIndex (M.input (A.certificate (cIndex.symm c))) := by
  simp [FiniteTable.certificate, finiteTable]

theorem finiteTable_fixedPrefix (x : BinaryWord) :
    (finiteTable M qIndex sIndex cIndex).fixedPrefix x =
      (TableauInput.fixedPrefix A M x).map sIndex := by
  simp only [FiniteTable.fixedPrefix, TableauInput.fixedPrefix, CheckingAlphabet.encode,
    List.map_append, List.map_cons, List.map_nil, List.map_map]
  congr 1
  apply List.map_congr_left
  intro b _
  exact finiteTable_bit M qIndex sIndex cIndex b

theorem finiteTable_fixedPrefix_at (x : BinaryWord) (i : Nat) :
    (((finiteTable M qIndex sIndex cIndex).fixedPrefix x)[i]?).getD
        (finiteTable M qIndex sIndex cIndex).blank =
      sIndex ((TableauInput.fixedPrefix A M x)[i]?.getD M.blank) := by
  rw [finiteTable_fixedPrefix, List.getElem?_map]
  cases (TableauInput.fixedPrefix A M x)[i]? <;> rfl

/-- The index relabeling preserves the clock and head coordinates of every atom. -/
def indexAtom {Q Γ : Type} {width : Nat} (q : Q → Fin qCount) (s : Γ → Fin symbolCount) :
    Tableau.Atom Q Γ width → Tableau.Atom (Fin qCount) (Fin symbolCount) width
  | .state t state => .state t (q state)
  | .head t i => .head t i
  | .cell t i a => .cell t i (s a)

/-- Numeric names of indexed atoms use their state and tape symbol indices directly. -/
def indexedAtomName {width : Nat} :
    Tableau.Atom (Fin qCount) (Fin symbolCount) width → Nat :=
  Tableau.Atom.name (Function.Embedding.refl _) (Function.Embedding.refl _)

@[simp] theorem indexedAtomName_indexAtom {Q Γ : Type} {width : Nat}
    (q : Q ↪ Fin qCount) (s : Γ ↪ Fin symbolCount) (a : Tableau.Atom Q Γ width) :
    indexedAtomName (indexAtom q s a) = a.name q s := by
  cases a <;> rfl

namespace FiniteTable

variable (table : FiniteTable qCount symbolCount certificateCount)

/-- Constraint on one initial tape cell, using indexed symbol constants. -/
def initialCell {width : Nat} (x : BinaryWord) (capacity offset : Nat) (i : Fin width) :
    CNF.Formula (Tableau.Atom (Fin qCount) (Fin symbolCount) width) :=
  if i.val < offset then [[.pos (.cell 0 i table.blank)]]
  else if i.val < offset + x.length + 1 then
    [[.pos (.cell 0 i ((table.fixedPrefix x)[i.val - offset]?.getD table.blank))]]
  else if i.val < offset + x.length + 1 + capacity then
    [.pos (.cell 0 i table.blank) :: (List.finRange certificateCount).map fun c ↦
      .pos (.cell 0 i (table.certificate c))]
  else [[.pos (.cell 0 i table.blank)]]

/-- The neighboring certificate blank constraints. -/
def initialGap {width : Nat} (x : BinaryWord) (capacity offset : Nat) (i j : Fin width) :
    CNF.Formula (Tableau.Atom (Fin qCount) (Fin symbolCount) width) :=
  if offset + x.length + 1 ≤ i.val ∧ j.val = i.val + 1 ∧
      j.val < offset + x.length + 1 + capacity then
    [[.neg (.cell 0 i table.blank), .pos (.cell 0 j table.blank)]]
  else []

/-- The complete indexed initial tableau row constraints. -/
def initialClauses {width : Nat} (head : Fin width) (x : BinaryWord) (capacity : Nat) :
    CNF.Formula (Tableau.Atom (Fin qCount) (Fin symbolCount) width) :=
  [[.pos (.state 0 table.initial)], [.pos (.head 0 head)]] ++
  (List.finRange width).flatMap (table.initialCell x capacity head.val) ++
  (List.finRange width).flatMap fun i ↦
    (List.finRange width).flatMap (table.initialGap x capacity head.val i)

/-- The verifier formula with only numeric indices and fixed table lookups. -/
def verifierFormula (x : BinaryWord) (k d : Nat) :
    CNF.Formula (Tableau.Atom (Fin qCount) (Fin symbolCount) (2 * horizon x.length k d + 1)) :=
  let t := horizon x.length k d
  Tableau.acceptingClauses (List.finRange qCount) (List.finRange symbolCount)
    table.windowAdvance t table.accept
    (table.initialClauses (Machine.windowCenter t) x (x.length ^ k))

/-- The binary output of the indexed tableau generator. -/
def binaryVerifierMap (x : BinaryWord) (k d : Nat) : BinaryWord :=
  CNFCode.encode (CNF.mapAtoms indexedAtomName (table.verifierFormula x k d))

end FiniteTable

private theorem mapAtoms_append {α β : Type} (f : α → β) (F G : CNF.Formula α) :
    CNF.mapAtoms f (F ++ G) = CNF.mapAtoms f F ++ CNF.mapAtoms f G :=
  List.map_append

private theorem mapAtoms_flatMap {α β γ : Type} (f : α → β) (xs : List γ)
    (g : γ → CNF.Formula α) :
    CNF.mapAtoms f (xs.flatMap g) = xs.flatMap (fun x ↦ CNF.mapAtoms f (g x)) :=
  List.map_flatMap

private theorem map_initialCell {width : Nat} (x : BinaryWord) (capacity offset : Nat)
    (i : Fin width) :
    CNF.mapAtoms (indexAtom qIndex sIndex) (initialCell M x capacity offset (enumerate cIndex) i) =
      (finiteTable M qIndex sIndex cIndex).initialCell x capacity offset i := by
  unfold initialCell FiniteTable.initialCell
  split
  · rfl
  · split
    · rw [finiteTable_fixedPrefix_at]
      rfl
    · split
      · simp [CNF.mapAtoms, CNF.Literal.map, indexAtom, enumerate, List.map_map, Function.comp_def]
        rfl
      · rfl

private theorem map_initialGap {width : Nat} (x : BinaryWord) (capacity offset : Nat)
    (i j : Fin width) :
    CNF.mapAtoms (indexAtom qIndex sIndex) (initialGap M x capacity offset i j) =
      (finiteTable M qIndex sIndex cIndex).initialGap x capacity offset i j := by
  unfold initialGap FiniteTable.initialGap
  split <;> rfl

theorem finiteTable_initialClauses {width : Nat} (head : Fin width) (x : BinaryWord)
    (capacity : Nat) :
    CNF.mapAtoms (indexAtom qIndex sIndex)
        (initialClauses M head x capacity (enumerate cIndex)) =
      (finiteTable M qIndex sIndex cIndex).initialClauses head x capacity := by
  simp only [initialClauses, FiniteTable.initialClauses, mapAtoms_append, mapAtoms_flatMap,
    map_initialCell, map_initialGap M qIndex sIndex cIndex]
  rfl

private theorem mapAtoms_exactlyOne {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (xs : List α) :
    CNF.mapAtoms f (CNF.exactlyOne xs) = CNF.exactlyOne (xs.map f) := by
  simp only [CNF.exactlyOne, CNF.mapAtoms, List.map_cons, List.map_map, List.map_flatMap,
    List.flatMap_map, List.filter_map, Function.comp_def]
  congr 1
  apply List.flatMap_congr
  intro a _
  have hFilter : (xs.filter fun b ↦ decide (f b ≠ f a)) = xs.filter (fun b ↦ decide (b ≠ a)) := by
    apply List.filter_congr
    intro b _
    simp [hf.eq_iff]
  rw [hFilter]
  rfl

section TableauTransport

open Tableau

variable {Q Γ : Type} {width : Nat}
    (q : Q ≃ Fin qCount) (s : Γ ≃ Fin symbolCount)

private theorem indexAtom_injective : Function.Injective (indexAtom q s (width := width)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [indexAtom, q.injective.eq_iff, s.injective.eq_iff]

private theorem map_rowClauses [DecidableEq Q] [DecidableEq Γ]
    (qs : List Q) (symbols : List Γ) (t : Nat) :
    CNF.mapAtoms (indexAtom q s) (rowClauses (width := width) qs symbols t) =
      rowClauses (qs.map q) (symbols.map s) t := by
  simp only [rowClauses, mapAtoms_append, mapAtoms_flatMap,
    mapAtoms_exactlyOne _ (indexAtom_injective q s), List.map_map]
  rfl

variable (rule : Rule Q Γ width) (indexed : Rule (Fin qCount) (Fin symbolCount) width)
    (hRule : ∀ state head read, indexed (q state) head (s read) =
      let next := rule state head read
      ⟨q next.1, next.2.1, s next.2.2⟩)

include hRule in
private theorem map_localUpdate (t : Nat) (state : Q) (head : Fin width) (read : Γ) :
    CNF.mapAtoms (indexAtom q s) (localUpdate rule t state head read) =
      localUpdate indexed t (q state) head (s read) := by
  unfold localUpdate
  rw [hRule]
  rfl

private theorem map_localCopy (t : Nat) (head cell : Fin width) (sym : Γ) :
    CNF.mapAtoms (indexAtom q s) (localCopy t head cell sym) =
      localCopy t head cell (s sym) := by
  unfold localCopy
  split <;> rfl

include hRule in
private theorem map_stepClauses (qs : List Q) (symbols : List Γ) (t : Nat) :
    CNF.mapAtoms (indexAtom q s) (stepClauses qs symbols rule t) =
      stepClauses (qs.map q) (symbols.map s) indexed t := by
  simp only [stepClauses, mapAtoms_append, mapAtoms_flatMap, List.flatMap_map,
    map_localUpdate q s rule indexed hRule, map_localCopy]

include hRule in
private theorem map_traceClauses [DecidableEq Q] [DecidableEq Γ]
    (qs : List Q) (symbols : List Γ) (steps : Nat) :
    CNF.mapAtoms (indexAtom q s) (traceClauses qs symbols rule steps) =
      traceClauses (qs.map q) (symbols.map s) indexed steps := by
  simp only [traceClauses, mapAtoms_append, mapAtoms_flatMap, map_rowClauses,
    map_stepClauses q s rule indexed hRule]

include hRule in
private theorem map_acceptingClauses [DecidableEq Q] [DecidableEq Γ]
    (qs : List Q) (symbols : List Γ) (steps : Nat)
    (accept : Q) (initial : CNF.Formula (Atom Q Γ width)) :
    CNF.mapAtoms (indexAtom q s) (acceptingClauses qs symbols rule steps accept initial) =
      acceptingClauses (qs.map q) (symbols.map s) indexed steps (q accept)
        (CNF.mapAtoms (indexAtom q s) initial) := by
  simp only [acceptingClauses, mapAtoms_append, map_traceClauses q s rule indexed hRule]
  rfl

end TableauTransport

private theorem map_enumerate {α : Type} {n : Nat} (e : α ≃ Fin n) :
    (enumerate e).map e = List.finRange n := by
  simp [enumerate, Function.comp_def]

/-- Relabeling preserves each clause and its position in the generated formula. -/
theorem finiteTable_verifierFormula [DecidableEq M.State] [DecidableEq M.Symbol]
    (x : BinaryWord) (k d : Nat) :
    CNF.mapAtoms (indexAtom qIndex sIndex)
        (verifierFormula M (enumerate qIndex) (enumerate sIndex) (enumerate cIndex) x k d) =
      (finiteTable M qIndex sIndex cIndex).verifierFormula x k d := by
  unfold verifierFormula FiniteTable.verifierFormula
  rw [map_acceptingClauses qIndex sIndex _ _ (finiteTable_windowAdvance M qIndex sIndex cIndex),
    map_enumerate, map_enumerate, finiteTable_initialClauses]
  rfl

/-- The indexed generator computes exactly the existing binary reduction word. -/
theorem finiteTable_binaryVerifierMap [DecidableEq M.State] [DecidableEq M.Symbol]
    (x : BinaryWord) (k d : Nat) :
    (finiteTable M qIndex sIndex cIndex).binaryVerifierMap x k d =
      binaryVerifierMap M qIndex.toEmbedding sIndex.toEmbedding
        (enumerate qIndex) (enumerate sIndex) (enumerate cIndex) x k d := by
  unfold FiniteTable.binaryVerifierMap binaryVerifierMap
  rw [← finiteTable_verifierFormula]
  have hMap {α β γ : Type} (f : α → β) (g : β → γ) (F : CNF.Formula α) :
      CNF.mapAtoms g (CNF.mapAtoms f F) = CNF.mapAtoms (g ∘ f) F := by
    have hLit (l : CNF.Literal α) : (l.map f).map g = l.map (g ∘ f) := by cases l <;> rfl
    simp only [CNF.mapAtoms, List.map_map, Function.comp_def]
    congr 1
    funext c
    exact List.map_congr_left fun l _ ↦ hLit l
  rw [hMap]
  have hName : (indexedAtomName (width := 2 * horizon x.length k d + 1) ∘ indexAtom qIndex sIndex) =
      Tableau.Atom.name qIndex.toEmbedding sIndex.toEmbedding :=
    funext (indexedAtomName_indexAtom qIndex.toEmbedding sIndex.toEmbedding)
  rw [hName]

/-- A compiler for the indexed generator suffices for the original verifier reduction. -/
theorem binaryTableauxPolyTime_of_indexed
    (hCompile : ∀ {q s c : Nat} (table : FiniteTable q s c) (k d : Nat),
      PolynomialTimeMap (fun x ↦ table.binaryVerifierMap x k d)) :
    BinaryTableauxPolyTime := by
  intro A M k d q s c _ _ qIndex sIndex cIndex
  simpa only [finiteTable_binaryVerifierMap] using
    hCompile (finiteTable M qIndex sIndex cIndex) k d

end PvsNP.CookLevin
