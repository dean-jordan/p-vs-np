module

public import PvsNP.SAT.BinaryLanguage
public import PvsNP.SAT.BranchRefutation
public import PvsNP.SAT.PigeonholeFormula

/-! # The pigeonhole formulas as binary CNF words -/

@[expose] public section

namespace PvsNP.SATBranching

variable {α β : Type}

/-- Rename the queries that have a preimage. Take the false branch at any other query. -/
def Tree.pullback (recover : β → Option α) : Tree β → Tree α
  | .leaf => .leaf
  | .branch v onFalse onTrue =>
    match recover v with
    | none => onFalse.pullback recover
    | some a => .branch a (onFalse.pullback recover) (onTrue.pullback recover)

theorem Tree.leaves_pullback_le (recover : β → Option α) (tree : Tree β) :
    (tree.pullback recover).leaves ≤ tree.leaves := by
  induction tree with
  | leaf => exact Nat.le_refl _
  | branch v onFalse onTrue ihFalse ihTrue =>
    cases h : recover v with
    | none =>
      simp only [Tree.pullback, h, Tree.leaves]
      exact Nat.le_trans ihFalse (Nat.le_add_right _ _)
    | some a =>
      simp only [Tree.pullback, h, Tree.leaves]
      exact Nat.add_le_add ihFalse ihTrue

private theorem falsified_map (name : α → β) (p : PartialAssignment β) (c : CNF.Clause α)
    (h : Falsified p (c.map (CNF.Literal.map name))) : Falsified (p ∘ name) c := by
  intro l hl
  have hLiteral := h (l.map name) (List.mem_map_of_mem hl)
  cases l <;> exact hLiteral

/-- Reflect a refutation through a decidable partial inverse. Queries outside the image may
be removed because their assignments affect none of the original literals. -/
theorem Refutes.pullback [DecidableEq α] [DecidableEq β] {name : α → β}
    {F : CNF.Formula α} {p : PartialAssignment β} {tree : Tree β}
    (h : Refutes (CNF.mapAtoms name F) p tree) (recover : β → Option α)
    (hRecover : ∀ a, recover (name a) = some a)
    (hName : ∀ {v a}, recover v = some a → name a = v) :
    Refutes F (p ∘ name) (tree.pullback recover) := by
  have hInjective : Function.Injective name := by
    intro a b hEq
    exact Option.some.inj ((hRecover a).symm.trans ((congrArg recover hEq).trans (hRecover b)))
  induction h with
  | leaf hConflict =>
    obtain ⟨mapped, hMapped, hFalsified⟩ := hConflict
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hMapped
    exact .leaf ⟨c, hc, falsified_map name _ c hFalsified⟩
  | @branch p v onFalse onTrue hFresh _ _ ihFalse ihTrue =>
    cases h : recover v with
    | none =>
      have hAssign : assign p v false ∘ name = p ∘ name := by
        funext a
        have hOther : name a ≠ v := by
          intro hEq
          rw [← hEq, hRecover] at h
          cases h
        simp [Function.comp_apply, assign, hOther]
      simpa only [Tree.pullback, h, hAssign] using ihFalse
    | some a =>
      have hEq : name a = v := hName h
      have hAssign (b : Bool) : assign p v b ∘ name = assign (p ∘ name) a b := by
        funext a'
        have hEqIff : name a' = v ↔ a' = a := by
          rw [← hEq]
          exact hInjective.eq_iff
        simp only [Function.comp_apply, assign, hEqIff]
      have hFresh' : (p ∘ name) a = none := by simpa only [Function.comp_apply, hEq] using hFresh
      simp only [Tree.pullback, h]
      exact .branch hFresh' (hAssign false ▸ ihFalse) (hAssign true ▸ ihTrue)

end PvsNP.SATBranching

namespace PvsNP.Pigeonhole

open SATBranching

/-- Name a variable by its offset in the row-major ordering. -/
def variableName {n : Nat} (v : Variable n) : Nat := n * v.1.val + v.2.val

/-- Recover a row and column when both coordinates are in range. -/
def variableOfName (n v : Nat) : Option (Variable n) :=
  if h : v / n < n + 1 ∧ v % n < n then some (⟨v / n, h.1⟩, ⟨v % n, h.2⟩) else none

@[simp] theorem variableOfName_variableName {n : Nat} (v : Variable n) :
    variableOfName n (variableName v) = some v := by
  have hn : 0 < n := Nat.zero_lt_of_lt v.2.isLt
  have hDiv : variableName v / n = v.1.val := by
    simp [variableName, Nat.mul_add_div hn, Nat.div_eq_of_lt v.2.isLt]
  have hMod : variableName v % n = v.2.val := by
    simp [variableName, Nat.mod_eq_of_lt v.2.isLt]
  unfold variableOfName
  rw [dite_eq_left ⟨hDiv ▸ v.1.isLt, hMod ▸ v.2.isLt⟩]
  congr 1
  exact Prod.ext (Fin.ext hDiv) (Fin.ext hMod)

theorem variableName_of_variableOfName {n v : Nat} {a : Variable n}
    (h : variableOfName n v = some a) : variableName a = v := by
  unfold variableOfName at h
  split at h
  · obtain rfl := Option.some.inj h
    exact Nat.div_add_mod v n
  · cases h

theorem variableName_injective (n : Nat) : Function.Injective (@variableName n) := by
  intro u v h
  simpa only [variableOfName_variableName, Option.some.injEq] using congrArg (variableOfName n) h

theorem variableName_lt {n : Nat} (v : Variable n) : variableName v < (n + 1) * n := by
  calc
    variableName v < n * v.1.val + n := Nat.add_lt_add_left v.2.isLt _
    _ = n * (v.1.val + 1) := by rw [Nat.mul_succ]
    _ ≤ n * (n + 1) := Nat.mul_le_mul_left _ v.1.isLt
    _ = (n + 1) * n := Nat.mul_comm ..

/-- The pigeonhole clauses with natural-number variable names. -/
def encodedFormula (n : Nat) : CNF.Formula Nat := CNF.mapAtoms variableName (formula n)

/-- A binary instance in the project's standard unary-name CNF format. -/
def word (n : Nat) : BinaryWord := CNFCode.encode (encodedFormula n)

theorem word_not_mem_CNFSAT (n : Nat) : word n ∉ CNFSAT := by
  intro h
  exact formula_not_satisfiable n ((CNF.satisfiable_mapAtoms_iff _ (variableName_injective n) _).mp
    ((encode_mem_CNFSAT_iff _).mp h))

theorem word_length_le (n : Nat) : (word n).length ≤
    1 + ((n + 1) * n + 3) * ((n + 1) * (n + 1) + 3 * ((n + 1) * n) ^ 2) := by
  unfold word
  calc
    _ ≤ 1 + ((n + 1) * n + 3) * CNF.size (encodedFormula n) := by
      apply CNFCode.length_encode_le
      intro c hc l hl
      obtain ⟨d, _, rfl⟩ := List.mem_map.mp hc
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hl
      cases a <;> exact Nat.le_of_lt (variableName_lt _)
    _ ≤ _ := by
      apply Nat.add_le_add_left
      apply Nat.mul_le_mul_left
      simpa only [encodedFormula, CNF.size_mapAtoms] using formula_size_le n

theorem word_length_polynomiallyBounded : PolynomiallyBounded (fun n ↦ (word n).length) := by
  let c := PolynomiallyBounded.const
  let hNext := PolynomiallyBounded.id.add (c 1)
  let hVars := hNext.mul PolynomiallyBounded.id
  exact ((c 1).add ((hVars.add (c 3)).mul
    ((hNext.mul hNext).add ((c 3).mul (hVars.pow 2))))).mono word_length_le

/-- Transfer the refutation to pair variables and account for every retained leaf. -/
theorem refutation_pullback {n : Nat} {tree : Tree Nat}
    (h : Refutes (encodedFormula n) (fun _ ↦ none) tree) :
    ∃ t : Tree (Variable n), Refutes (formula n) (fun _ ↦ none) t ∧ t.leaves ≤ tree.leaves := by
  exact ⟨tree.pullback (variableOfName n),
    h.pullback (variableOfName n) variableOfName_variableName variableName_of_variableOfName,
    tree.leaves_pullback_le (variableOfName n)⟩

end PvsNP.Pigeonhole
