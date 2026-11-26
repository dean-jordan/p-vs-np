module

public import Init.Data.List.Lemmas

/-! # Conjunctive normal form and constraint encodings

Clauses are disjunctions of literals, and formulas are conjunctions of clauses.
The encodings below use list concatenation to combine finite families of
constraints. `size` counts literal occurrences and one delimiter per clause.
-/

@[expose] public section

namespace PvsNP.CNF

/-- A positive or negative occurrence of one atom. -/
inductive Literal (α : Type) where
  | pos : α → Literal α
  | neg : α → Literal α
  deriving DecidableEq

/-- A disjunction, with the empty list representing false. -/
abbrev Clause (α : Type) := List (Literal α)

/-- A conjunction, with the empty list representing true. -/
abbrev Formula (α : Type) := List (Clause α)

variable {α β : Type}

/-- Truth of a literal under a Boolean assignment. -/
def Literal.Sat (σ : α → Bool) : Literal α → Prop
  | .pos a => σ a = true
  | .neg a => σ a = false

/-- The opposite sign on the same atom. -/
def Literal.complement : Literal α → Literal α
  | .pos a => .neg a
  | .neg a => .pos a

@[simp] theorem Literal.sat_pos (σ : α → Bool) (a : α) : (Literal.pos a).Sat σ ↔ σ a = true :=
  Iff.rfl

@[simp] theorem Literal.sat_neg (σ : α → Bool) (a : α) : (Literal.neg a).Sat σ ↔ σ a = false :=
  Iff.rfl

@[simp] theorem Literal.sat_complement (σ : α → Bool) (l : Literal α) :
    l.complement.Sat σ ↔ ¬ l.Sat σ := by
  cases l with
  | pos a => cases h : σ a <;> simp [Literal.complement, h]
  | neg a => cases h : σ a <;> simp [Literal.complement, h]

/-- Rename the atom while preserving the literal's sign. -/
def Literal.map (f : α → β) : Literal α → Literal β
  | .pos a => .pos (f a)
  | .neg a => .neg (f a)

@[simp] theorem Literal.sat_map (σ : β → Bool) (f : α → β) (l : Literal α) :
    (l.map f).Sat σ ↔ l.Sat (σ ∘ f) := by
  cases l <;> rfl

/-- A clause is true when it contains a true literal. -/
def Clause.Sat (σ : α → Bool) (c : Clause α) : Prop := ∃ l ∈ c, l.Sat σ

/-- A formula is true when each of its clauses is true. -/
def Sat (σ : α → Bool) (F : Formula α) : Prop := ∀ c ∈ F, Clause.Sat σ c

/-- A formula is satisfiable when some assignment makes it true. -/
def Satisfiable (F : Formula α) : Prop := ∃ σ, Sat σ F

@[simp] theorem Clause.sat_nil (σ : α → Bool) : ¬ Clause.Sat σ [] := by simp [Clause.Sat]

@[simp] theorem Clause.sat_cons (σ : α → Bool) (l : Literal α) (c : Clause α) :
    Clause.Sat σ (l :: c) ↔ l.Sat σ ∨ Clause.Sat σ c := by
  simp [Clause.Sat, List.mem_cons, or_and_right, exists_or]

@[simp] theorem Clause.sat_singleton (σ : α → Bool) (l : Literal α) :
    Clause.Sat σ [l] ↔ l.Sat σ := by simp

theorem Clause.sat_append (σ : α → Bool) (c d : Clause α) :
    Clause.Sat σ (c ++ d) ↔ Clause.Sat σ c ∨ Clause.Sat σ d := by
  simp [Clause.Sat, List.mem_append, or_and_right, exists_or]

@[simp] theorem sat_nil (σ : α → Bool) : Sat σ [] := by simp [Sat]

@[simp] theorem sat_cons (σ : α → Bool) (c : Clause α) (F : Formula α) :
    Sat σ (c :: F) ↔ Clause.Sat σ c ∧ Sat σ F := by
  simp [Sat, List.mem_cons, forall_eq_or_imp]

@[simp] theorem sat_unit (σ : α → Bool) (l : Literal α) : Sat σ [[l]] ↔ l.Sat σ := by simp

theorem sat_append (σ : α → Bool) (F G : Formula α) : Sat σ (F ++ G) ↔ Sat σ F ∧ Sat σ G := by
  constructor
  · intro h
    exact ⟨fun c hc ↦ h c (List.mem_append_left _ hc), fun c hc ↦ h c (List.mem_append_right _ hc)⟩
  · rintro ⟨hF, hG⟩ c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hF c hc
    · exact hG c hc

theorem sat_map (σ : α → Bool) (xs : List β) (f : β → Clause α) :
    Sat σ (xs.map f) ↔ ∀ x ∈ xs, Clause.Sat σ (f x) := by
  constructor
  · exact fun h x hx ↦ h (f x) (List.mem_map_of_mem hx)
  · intro h c hc
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
    exact h x hx

theorem sat_flatMap (σ : α → Bool) (xs : List β) (f : β → Formula α) :
    Sat σ (xs.flatMap f) ↔ ∀ x ∈ xs, Sat σ (f x) := by
  constructor
  · exact fun h x hx c hc ↦ h c (List.mem_flatMap_of_mem hx hc)
  · intro h c hc
    obtain ⟨x, hx, hxc⟩ := List.mem_flatMap.mp hc
    exact h x hx c hxc

/-- Rename every atom of the formula. -/
def mapAtoms (f : α → β) (F : Formula α) : Formula β := F.map (List.map (Literal.map f))

theorem Clause.sat_mapAtoms (σ : β → Bool) (f : α → β) (c : Clause α) :
    Clause.Sat σ (c.map (Literal.map f)) ↔ Clause.Sat (σ ∘ f) c := by
  induction c with
  | nil => simp
  | cons l c ih => simp [ih]

theorem sat_mapAtoms (σ : β → Bool) (f : α → β) (F : Formula α) :
    Sat σ (mapAtoms f F) ↔ Sat (σ ∘ f) F := by
  induction F with
  | nil => simp [mapAtoms]
  | cons c F ih =>
    change Sat σ (c.map (Literal.map f) :: mapAtoms f F) ↔ Sat (σ ∘ f) (c :: F)
    simp [Clause.sat_mapAtoms, ih]

/-- Injective renaming preserves satisfiability. Values outside the image can be set false. -/
theorem satisfiable_mapAtoms_iff (f : α → β) (hf : Function.Injective f) (F : Formula α) :
    Satisfiable (mapAtoms f F) ↔ Satisfiable F := by
  classical
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ ∘ f, (sat_mapAtoms σ f F).mp hσ⟩
  · rintro ⟨σ, hσ⟩
    let ρ : β → Bool := fun b ↦ if h : ∃ a, f a = b then σ (Classical.choose h) else false
    have h : ρ ∘ f = σ := by
      funext a
      have he : ∃ a', f a' = f a := ⟨a, rfl⟩
      simp only [Function.comp_apply, ρ, dite_eq_left he, hf (Classical.choose_spec he)]
    refine ⟨ρ, (sat_mapAtoms ρ f F).mpr ?_⟩
    rwa [h]

/-- Add the negated antecedents to each clause of the conclusion. -/
def guard (gs : List (Literal α)) (F : Formula α) : Formula α :=
  F.map fun c ↦ gs.map Literal.complement ++ c

/-- A guarded formula expresses implication from the conjunction of the guards. -/
theorem sat_guard (σ : α → Bool) (gs : List (Literal α)) (F : Formula α) :
    Sat σ (guard gs F) ↔ ((∀ l ∈ gs, l.Sat σ) → Sat σ F) := by
  classical
  simp only [guard, sat_map, Clause.sat_append]
  constructor
  · intro h hg c hc
    rcases h c hc with hneg | hsat
    · obtain ⟨l, hl, hσ⟩ := hneg
      obtain ⟨g, hmem, rfl⟩ := List.mem_map.mp hl
      exact ((Literal.sat_complement σ g).mp hσ (hg g hmem)).elim
    · exact hsat
  · intro h c hc
    by_cases hbad : ∃ l ∈ gs, ¬ l.Sat σ
    · obtain ⟨l, hl, hσ⟩ := hbad
      exact Or.inl ⟨_, List.mem_map_of_mem hl, (Literal.sat_complement σ l).mpr hσ⟩
    · exact Or.inr (h (fun l hl ↦ Classical.byContradiction fun hn ↦ hbad ⟨l, hl, hn⟩) c hc)

theorem sat_guard_unit (σ : α → Bool) (gs : List (Literal α)) (l : Literal α) :
    Sat σ (guard gs [[l]]) ↔ ((∀ g ∈ gs, g.Sat σ) → l.Sat σ) := by
  simp only [sat_guard, sat_unit]

/-- Assert that exactly one distinct atom in the supplied list is true. -/
def exactlyOne [DecidableEq α] (xs : List α) : Formula α :=
  xs.map Literal.pos :: xs.flatMap fun a ↦
    (xs.filter (fun b ↦ decide (b ≠ a))).map fun b ↦ [.neg a, .neg b]

/-- The positive clause forces a true atom, and the negative clauses forbid distinct true atoms. -/
theorem sat_exactlyOne [DecidableEq α] (σ : α → Bool) (xs : List α) :
    Sat σ (exactlyOne xs) ↔ ∃ a, a ∈ xs ∧ σ a = true ∧ ∀ b ∈ xs, σ b = true → b = a := by
  simp only [exactlyOne, sat_cons, sat_flatMap, sat_map]
  constructor
  · rintro ⟨h, hpair⟩
    obtain ⟨l, hl, hσ⟩ := h
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hl
    refine ⟨a, ha, hσ, fun b hb hσb ↦ ?_⟩
    by_cases hne : b = a
    · exact hne
    · have hb' : b ∈ xs.filter (fun b ↦ decide (b ≠ a)) := by simp [hb, hne]
      have hd := hpair a ha b hb'
      have hσa : σ a = true := hσ
      simp [hσa, hσb] at hd
  · rintro ⟨a, ha, hσa, hunique⟩
    refine ⟨⟨Literal.pos a, List.mem_map_of_mem ha, hσa⟩, ?_⟩
    intro b hb c hc
    have ⟨hmem, hne⟩ : c ∈ xs ∧ c ≠ b := by simpa using hc
    simp only [Clause.sat_cons, Clause.sat_nil, or_false, Literal.sat_neg]
    cases hσb : σ b with
    | false => exact Or.inl rfl
    | true =>
      cases hσc : σ c with
      | false => exact Or.inr rfl
      | true => exact (hne ((hunique c hmem hσc).trans (hunique b hb hσb).symm)).elim

/-- Number of literal occurrences plus one delimiter for every clause. -/
def size : Formula α → Nat
  | [] => 0
  | c :: F => c.length + 1 + size F

@[simp] theorem size_nil : size ([] : Formula α) = 0 := rfl

@[simp] theorem size_cons (c : Clause α) (F : Formula α) :
    size (c :: F) = c.length + 1 + size F := rfl

theorem length_le_size (F : Formula α) : F.length ≤ size F := by
  induction F with
  | nil => simp
  | cons c F ih => simp only [List.length_cons, size_cons]; omega

theorem size_append (F G : Formula α) : size (F ++ G) = size F + size G := by
  induction F with
  | nil => simp
  | cons c F ih => simp [ih, Nat.add_assoc]

@[simp] theorem size_mapAtoms (f : α → β) (F : Formula α) :
    size (mapAtoms f F) = size F := by
  induction F with
  | nil => rfl
  | cons c F ih =>
    change size (c.map (Literal.map f) :: mapAtoms f F) = size (c :: F)
    simp [ih]

/-- A uniform bound on each block gives a bound on their concatenation. -/
theorem size_flatMap_le (xs : List β) (f : β → Formula α) (B : Nat)
    (h : ∀ x ∈ xs, size (f x) ≤ B) : size (xs.flatMap f) ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    change size (f x ++ xs.flatMap f) ≤ (xs.length + 1) * B
    rw [size_append, Nat.add_mul, Nat.one_mul, Nat.add_comm (size (f x))]
    exact Nat.add_le_add (ih fun y hy ↦ h y (List.mem_cons_of_mem _ hy)) (h x (by simp))

theorem size_map_of_length (xs : List β) (f : β → Clause α) (n : Nat)
    (h : ∀ x ∈ xs, (f x).length = n) : size (xs.map f) = xs.length * (n + 1) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have h' := ih fun y hy ↦ h y (List.mem_cons_of_mem _ hy)
    simp only [List.map_cons, size_cons, hx, h', List.length_cons, Nat.add_mul, Nat.one_mul]
    exact Nat.add_comm ..

/-- Guarding a formula adds exactly one copy of the guards to every clause. -/
theorem size_guard (gs : List (Literal α)) (F : Formula α) :
    size (guard gs F) = size F + F.length * gs.length := by
  induction F with
  | nil => simp [guard]
  | cons c F ih =>
    change size ((gs.map Literal.complement ++ c) :: guard gs F) =
      size (c :: F) + (F.length + 1) * gs.length
    simp only [size_cons, List.length_append, List.length_map, ih, Nat.add_mul, Nat.one_mul]
    omega

/-- The exactly-one encoding uses one positive clause and at most quadratically many
two-literal negative clauses. -/
theorem size_exactlyOne_le [DecidableEq α] (xs : List α) :
    size (exactlyOne xs) ≤ xs.length + 1 + 3 * xs.length ^ 2 := by
  simp only [exactlyOne, size_cons, List.length_map, Nat.add_le_add_iff_left]
  calc
    _ ≤ xs.length * (3 * xs.length) := by
      apply size_flatMap_le
      intro a _
      rw [size_map_of_length _ _ 2 (fun _ _ ↦ rfl), Nat.mul_comm]
      exact Nat.mul_le_mul_left 3 (List.length_filter_le ..)
    _ = 3 * xs.length ^ 2 := by rw [Nat.pow_succ, Nat.pow_one]; ac_rfl

end PvsNP.CNF
