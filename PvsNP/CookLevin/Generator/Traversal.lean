module

public import PvsNP.CookLevin.Generator.FiniteTable
public import PvsNP.CookLevin.Generator.Serialization

/-! # Descending loops for the indexed tableau generator -/

@[expose] public section

namespace PvsNP.CookLevin

namespace Traversal

variable {σ : Type}

/-- Visit `n - 1, ..., 0` by counting down. -/
def foldNatDesc (step : σ → Nat → σ) (acc : σ) : Nat → σ
  | 0 => acc
  | n + 1 => foldNatDesc step (step acc n) n

theorem foldNatDesc_eq (step : σ → Nat → σ) (acc : σ) (n : Nat) :
    foldNatDesc step acc n = (List.range n).reverse.foldl step acc := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih => simp [foldNatDesc, ih, List.range_succ]

/-- Visit all elements of `Fin n` in descending index order. -/
def foldFinDesc : (n : Nat) → (σ → Fin n → σ) → σ → σ
  | 0, _, acc => acc
  | n + 1, step, acc =>
    foldFinDesc n (fun acc i ↦ step acc i.castSucc) (step acc (Fin.last n))

theorem foldFinDesc_eq (n : Nat) (step : σ → Fin n → σ) (acc : σ) :
    foldFinDesc n step acc = (List.finRange n).reverse.foldl step acc := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih =>
    simp only [foldFinDesc, ih, List.finRange_succ_last, List.reverse_append,
      List.reverse_singleton, List.singleton_append, List.foldl_cons, ← List.map_reverse,
      List.foldl_map]

private theorem foldReverse_flatMap {α β : Type} (items : List α) (block : α → List β)
    (step : σ → β → σ) (acc : σ) :
    (items.flatMap block).reverse.foldl step acc =
      items.reverse.foldl (fun acc item ↦ (block item).reverse.foldl step acc) acc := by
  simp [List.reverse_flatMap, List.foldl_flatMap, Function.comp_def]

/-- Visit negative pairs with descending index loops, then emit the positive clause. -/
def foldExactlyOne {α : Type} (n : Nat) (atom : Fin n → α)
    (emit : σ → CNF.Clause α → σ) (acc : σ) : σ :=
  let pairs := foldFinDesc n (fun acc i ↦
    foldFinDesc n (fun acc j ↦ if j = i then acc else emit acc [.neg (atom i), .neg (atom j)])
      acc) acc
  emit pairs ((List.finRange n).map fun i ↦ .pos (atom i))

theorem foldExactlyOne_eq {α : Type} [DecidableEq α] {n : Nat} (atom : Fin n → α)
    (hAtom : Function.Injective atom) (emit : σ → CNF.Clause α → σ) (acc : σ) :
    foldExactlyOne n atom emit acc =
      (CNF.exactlyOne ((List.finRange n).map atom)).reverse.foldl emit acc := by
  simp only [foldExactlyOne, CNF.exactlyOne, foldFinDesc_eq, List.reverse_cons, List.foldl_append,
    List.foldl_cons, List.foldl_nil, List.map_map, foldReverse_flatMap, ← List.map_reverse,
    List.foldl_map, List.filter_map, Function.comp_def, ← List.filter_reverse, List.foldl_filter,
    hAtom.eq_iff, decide_eq_true_eq, ite_not]

end Traversal

namespace FiniteTable

open Tableau Traversal

variable {qCount symbolCount certificateCount width : Nat} {σ : Type}
    (table : FiniteTable qCount symbolCount certificateCount)

local notation "IndexedAtom" => Atom (Fin qCount) (Fin symbolCount) width

/-- Visit every exactly-one block of the given row, in reverse clause order. -/
def foldRowClauses (emit : σ → CNF.Clause IndexedAtom → σ) (acc : σ) (t : Nat) : σ :=
  let cells := foldFinDesc width
    (fun acc i ↦ foldExactlyOne symbolCount (Atom.cell t i) emit acc) acc
  let head := foldExactlyOne width (Atom.head t) emit cells
  foldExactlyOne qCount (Atom.state t) emit head

theorem foldRowClauses_eq (emit : σ → CNF.Clause IndexedAtom → σ) (acc : σ) (t : Nat) :
    foldRowClauses emit acc t =
      (Tableau.rowClauses (List.finRange qCount) (List.finRange symbolCount) t).reverse.foldl
        emit acc := by
  have hCell (i : Fin width) : Function.Injective (Atom.cell t i : Fin symbolCount → IndexedAtom) :=
    fun _ _ h ↦ (Atom.cell.inj h).2.2
  have hHead : Function.Injective (Atom.head t : Fin width → IndexedAtom) :=
    fun _ _ h ↦ (Atom.head.inj h).2
  have hState : Function.Injective (Atom.state t : Fin qCount → IndexedAtom) :=
    fun _ _ h ↦ (Atom.state.inj h).2
  simp only [foldRowClauses, Tableau.rowClauses, foldExactlyOne_eq _ hState,
    foldExactlyOne_eq _ hHead, foldExactlyOne_eq _ (hCell _), foldFinDesc_eq, List.reverse_append,
    List.foldl_append, foldReverse_flatMap]

/-- Visit the copy blocks, then the rule-update blocks, each with descending loop indices. -/
def foldStepClauses (emit : σ → CNF.Clause IndexedAtom → σ) (acc : σ) (t : Nat) : σ :=
  let copies := foldFinDesc width (fun acc i ↦ foldFinDesc width (fun acc j ↦
    foldFinDesc symbolCount (fun acc s ↦ (Tableau.localCopy t i j s).reverse.foldl emit acc)
      acc) acc) acc
  foldFinDesc qCount (fun acc q ↦ foldFinDesc width (fun acc i ↦
    foldFinDesc symbolCount
      (fun acc s ↦ (Tableau.localUpdate table.windowAdvance t q i s).reverse.foldl emit acc)
        acc) acc) copies

theorem foldStepClauses_eq (emit : σ → CNF.Clause IndexedAtom → σ) (acc : σ) (t : Nat) :
    table.foldStepClauses emit acc t =
      (Tableau.stepClauses (List.finRange qCount) (List.finRange symbolCount)
        table.windowAdvance t).reverse.foldl emit acc := by
  simp only [foldStepClauses, Tableau.stepClauses, foldFinDesc_eq, List.reverse_append,
    List.foldl_append, foldReverse_flatMap]

/-- Visit the initial gaps, cells, head, and state, in reverse clause order. -/
def foldInitialClauses (emit : σ → CNF.Clause IndexedAtom → σ) (acc : σ) (head : Fin width)
    (x : BinaryWord) (capacity : Nat) : σ :=
  let gaps := foldFinDesc width (fun acc i ↦ foldFinDesc width (fun acc j ↦
    (table.initialGap x capacity head.val i j).reverse.foldl emit acc) acc) acc
  let cells := foldFinDesc width (fun acc i ↦
    (table.initialCell x capacity head.val i).reverse.foldl emit acc) gaps
  emit (emit cells [.pos (.head 0 head)]) [.pos (.state 0 table.initial)]

theorem foldInitialClauses_eq (emit : σ → CNF.Clause IndexedAtom → σ) (acc : σ)
    (head : Fin width) (x : BinaryWord) (capacity : Nat) :
    table.foldInitialClauses emit acc head x capacity =
      (table.initialClauses head x capacity).reverse.foldl emit acc := by
  simp only [foldInitialClauses, FiniteTable.initialClauses, foldFinDesc_eq, List.reverse_append,
    List.foldl_append, foldReverse_flatMap, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, List.foldl_cons, List.foldl_nil]

/-- Emit the indexed clauses in reverse order using nested countdown loops. -/
def foldVerifierClauses (x : BinaryWord) (k d : Nat)
    (emit : σ → CNF.Clause
      (Atom (Fin qCount) (Fin symbolCount) (2 * horizon x.length k d + 1)) → σ) (acc : σ) : σ :=
  let horizon := horizon x.length k d
  let final := emit acc [.pos (.state horizon table.accept)]
  let steps := foldNatDesc (table.foldStepClauses emit) final horizon
  let rows := foldNatDesc (foldRowClauses emit) steps (horizon + 1)
  table.foldInitialClauses emit rows (Machine.windowCenter horizon) x (x.length ^ k)

/-- The countdown traversal visits precisely the original indexed clauses in reverse order. -/
theorem foldVerifierClauses_eq (x : BinaryWord) (k d : Nat)
    (emit : σ → CNF.Clause
      (Atom (Fin qCount) (Fin symbolCount) (2 * horizon x.length k d + 1)) → σ) (acc : σ) :
    table.foldVerifierClauses x k d emit acc =
      (table.verifierFormula x k d).reverse.foldl emit acc := by
  simp only [foldVerifierClauses, FiniteTable.verifierFormula, Tableau.acceptingClauses,
    Tableau.traceClauses, foldInitialClauses_eq, ← foldStepClauses_eq, ← foldRowClauses_eq,
    foldNatDesc_eq, List.reverse_append, List.foldl_append, List.reverse_singleton, List.foldl_cons,
    List.foldl_nil, foldReverse_flatMap]

/-- Generate binary bits directly from descending loops over the verifier table. -/
def emitVerifier (x : BinaryWord) (k d : Nat) (emit : σ → Bool → σ) (acc : σ) : σ :=
  table.foldVerifierClauses x k d
    (fun acc clause ↦ emit (Serialization.emitClause emit acc
      (clause.map (CNF.Literal.map indexedAtomName))) true) (emit acc false)

/-- The direct traversal emits the exact binary word in reverse chronological order. -/
theorem emitVerifier_eq_foldl (x : BinaryWord) (k d : Nat) (emit : σ → Bool → σ) (acc : σ) :
    table.emitVerifier x k d emit acc = (table.binaryVerifierMap x k d).reverse.foldl emit acc := by
  rw [emitVerifier, foldVerifierClauses_eq, FiniteTable.binaryVerifierMap,
    ← Serialization.emitFormula_eq_foldl]
  simp only [Serialization.emitFormula, CNF.mapAtoms, ← List.map_reverse, List.foldl_map]

/-- Prepending each bit during the traversal produces the canonical binary output. -/
theorem emitVerifier_prepend (x : BinaryWord) (k d : Nat) (suffix : BinaryWord) :
    table.emitVerifier x k d (fun acc bit ↦ bit :: acc) suffix =
      table.binaryVerifierMap x k d ++ suffix := by
  rw [emitVerifier_eq_foldl, List.foldl_flip_cons_eq_append', List.reverse_reverse]

end FiniteTable

end PvsNP.CookLevin
