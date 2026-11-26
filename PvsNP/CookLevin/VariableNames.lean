module

public import Mathlib.Logic.Embedding.Basic
public import PvsNP.CookLevin.Tableau

/-!
# Dense names for tableau variables

Each time has a block for state, head, and cell atoms. The block width is
`stateCount + width + width * symbolCount`, so atoms in a bounded trace receive
bounded natural-number names, even when a field has no possible values.
-/

@[expose] public section

namespace PvsNP.CNF.Literal

/-- The atom occurring in a literal, independent of its sign. -/
def atom {α : Type} : Literal α → α
  | .pos a => a
  | .neg a => a

@[simp] theorem atom_map {α β : Type} (f : α → β) (l : Literal α) :
    (l.map f).atom = f l.atom := by
  cases l <;> rfl

end PvsNP.CNF.Literal

namespace PvsNP.Tableau

variable {Q Γ : Type} {width qCount symbolCount : Nat}

/-- The clock tick of an atom. -/
def Atom.time : Atom Q Γ width → Nat
  | .state t _ | .head t _ | .cell t _ _ => t

/-- The number of natural-number names allocated to one row. -/
def atomStride (qCount width symbolCount : Nat) : Nat := qCount + width + width * symbolCount

/-- The index within a row's block, with the three sorts in disjoint intervals. -/
def Atom.offset (qIndex : Q ↪ Fin qCount) (symbolIndex : Γ ↪ Fin symbolCount) :
    Atom Q Γ width → Nat
  | .state _ q => (qIndex q).val
  | .head _ i => qCount + i.val
  | .cell _ i a => qCount + width + (i.val * symbolCount + (symbolIndex a).val)

/-- A natural-number name for an atom. -/
def Atom.name (qIndex : Q ↪ Fin qCount) (symbolIndex : Γ ↪ Fin symbolCount)
    (a : Atom Q Γ width) : Nat :=
  a.time * atomStride qCount width symbolCount + a.offset qIndex symbolIndex

private theorem block_lt_next {stride offset : Nat} (block : Nat) (h : offset < stride) :
    block * stride + offset < (block + 1) * stride := by
  rw [Nat.add_mul, Nat.one_mul]
  exact Nat.add_lt_add_left h _

private theorem block_eq_of_name_eq {stride t u a b : Nat} (ha : a < stride) (hb : b < stride)
    (h : t * stride + a = u * stride + b) : t = u ∧ a = b := by
  have ht : t = u := by
    rcases Nat.lt_trichotomy t u with hlt | heq | hgt
    · have hs : (t + 1) * stride ≤ u * stride :=
        Nat.mul_le_mul_right stride (Nat.succ_le_of_lt hlt)
      have ha' := block_lt_next t ha
      omega
    · exact heq
    · have hs : (u + 1) * stride ≤ t * stride :=
        Nat.mul_le_mul_right stride (Nat.succ_le_of_lt hgt)
      have hb' := block_lt_next u hb
      omega
  subst u
  exact ⟨rfl, Nat.add_left_cancel h⟩

private theorem cellIndex_lt (i : Fin width) (a : Fin symbolCount) :
    i.val * symbolCount + a.val < width * symbolCount :=
  Nat.lt_of_lt_of_le (block_lt_next i.val a.isLt)
    (Nat.mul_le_mul_right _ (Nat.succ_le_of_lt i.isLt))

theorem Atom.offset_lt (qIndex : Q ↪ Fin qCount) (symbolIndex : Γ ↪ Fin symbolCount)
    (a : Atom Q Γ width) : a.offset qIndex symbolIndex < atomStride qCount width symbolCount := by
  cases a with
  | state t q =>
    have hq := (qIndex q).isLt
    simp only [Atom.offset, atomStride]
    omega
  | head t i =>
    have hi := i.isLt
    simp only [Atom.offset, atomStride]
    omega
  | cell t i a =>
    have ha := cellIndex_lt i (symbolIndex a)
    simp only [Atom.offset, atomStride]
    omega

private theorem Atom.eq_of_time_offset_eq (qIndex : Q ↪ Fin qCount)
    (symbolIndex : Γ ↪ Fin symbolCount) {a b : Atom Q Γ width} (ht : a.time = b.time)
    (h : a.offset qIndex symbolIndex = b.offset qIndex symbolIndex) : a = b := by
  cases a with
  | state t q =>
    have hq := (qIndex q).isLt
    cases b with
    | state u p =>
      simp only [Atom.time, Atom.offset] at ht h
      have hp := qIndex.injective (Fin.ext h)
      subst u
      subst p
      rfl
    | head u i => simp only [Atom.offset] at h; omega
    | cell u i a => simp only [Atom.offset] at h; omega
  | head t i =>
    have hi := i.isLt
    cases b with
    | state u p =>
      have hp := (qIndex p).isLt
      simp only [Atom.offset] at h
      omega
    | head u j =>
      simp only [Atom.time, Atom.offset] at ht h
      have hj : i = j := Fin.ext (Nat.add_left_cancel h)
      subst u
      subst j
      rfl
    | cell u j b => simp only [Atom.offset] at h; omega
  | cell t i a =>
    cases b with
    | state u p =>
      have hp := (qIndex p).isLt
      simp only [Atom.offset] at h
      omega
    | head u j =>
      have hj := j.isLt
      simp only [Atom.offset] at h
      omega
    | cell u j b =>
      simp only [Atom.time, Atom.offset] at ht h
      obtain ⟨hi, ha⟩ := block_eq_of_name_eq (symbolIndex a).isLt (symbolIndex b).isLt
        (Nat.add_left_cancel h)
      have hj : i = j := Fin.ext hi
      have hb : a = b := symbolIndex.injective (Fin.ext ha)
      subst u
      subst j
      subst b
      rfl

/-- The block name distinguishes every atom, including atoms outside a bounded trace. -/
theorem Atom.name_injective (qIndex : Q ↪ Fin qCount) (symbolIndex : Γ ↪ Fin symbolCount) :
    Function.Injective (Atom.name (width := width) qIndex symbolIndex) := by
  intro a b h
  obtain ⟨ht, ho⟩ := block_eq_of_name_eq (a.offset_lt qIndex symbolIndex)
    (b.offset_lt qIndex symbolIndex) h
  exact Atom.eq_of_time_offset_eq qIndex symbolIndex ht ho

/-- Names through the last tick fit in the number of rows times the block width. -/
theorem Atom.name_lt_of_time_le (qIndex : Q ↪ Fin qCount) (symbolIndex : Γ ↪ Fin symbolCount)
    (a : Atom Q Γ width) {steps : Nat} (h : a.time ≤ steps) :
    a.name qIndex symbolIndex < (steps + 1) * atomStride qCount width symbolCount :=
  Nat.lt_of_lt_of_le (block_lt_next a.time (a.offset_lt qIndex symbolIndex))
    (Nat.mul_le_mul_right _ (Nat.succ_le_succ h))

/-- Every literal's clock tick is at most `steps`. -/
def TimeBounded (steps : Nat) (F : CNF.Formula (Atom Q Γ width)) : Prop :=
  ∀ c ∈ F, ∀ l ∈ c, l.atom.time ≤ steps

theorem TimeBounded.mono {F : CNF.Formula (Atom Q Γ width)} {s t : Nat}
    (h : TimeBounded s F) (hst : s ≤ t) : TimeBounded t F :=
  fun c hc l hl ↦ Nat.le_trans (h c hc l hl) hst

theorem timeBounded_append (s : Nat) (F G : CNF.Formula (Atom Q Γ width)) :
    TimeBounded s (F ++ G) ↔ TimeBounded s F ∧ TimeBounded s G := by
  simp [TimeBounded, List.mem_append, or_imp, forall_and]

private theorem timeBounded_flatMap {α : Type} (s : Nat) (xs : List α)
    (f : α → CNF.Formula (Atom Q Γ width)) :
    TimeBounded s (xs.flatMap f) ↔ ∀ x ∈ xs, TimeBounded s (f x) := by
  constructor
  · intro h x hx c hc
    exact h c (List.mem_flatMap_of_mem hx hc)
  · intro h c hc
    obtain ⟨x, hx, hxc⟩ := List.mem_flatMap.mp hc
    exact h x hx c hxc

private theorem timeBounded_exactlyOne [DecidableEq Q] [DecidableEq Γ]
    (xs : List (Atom Q Γ width)) {s : Nat} (h : ∀ a ∈ xs, a.time ≤ s) :
    TimeBounded s (CNF.exactlyOne xs) := by
  intro c hc l hl
  simp only [CNF.exactlyOne, List.mem_cons, List.mem_flatMap, List.mem_map] at hc
  rcases hc with rfl | ⟨a, ha, b, hb, rfl⟩
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hl
    exact h a ha
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · exact h a ha
    · exact h b (List.mem_filter.mp hb).1

/-- The row constraints refer only to that row. -/
theorem timeBounded_rowClauses [DecidableEq Q] [DecidableEq Γ]
    (qs : List Q) (symbols : List Γ) (t : Nat) :
    TimeBounded t (rowClauses (width := width) qs symbols t) := by
  simp only [rowClauses, timeBounded_append, timeBounded_flatMap]
  refine ⟨⟨timeBounded_exactlyOne _ ?_, timeBounded_exactlyOne _ ?_⟩,
    fun i _ ↦ timeBounded_exactlyOne _ ?_⟩
  all_goals
    intro a ha
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    exact Nat.le_refl t

private theorem timeBounded_localUpdate (rule : Rule Q Γ width) (t : Nat)
    (q : Q) (i : Fin width) (a : Γ) : TimeBounded (t + 1) (localUpdate rule t q i a) := by
  simp [localUpdate, CNF.guard, CNF.Literal.complement, TimeBounded, CNF.Literal.atom, Atom.time]

private theorem timeBounded_localCopy (t : Nat) (i j : Fin width) (a : Γ) :
    TimeBounded (t + 1) (localCopy (Q := Q) t i j a) := by
  by_cases h : i = j <;>
    simp [localCopy, h, CNF.guard, CNF.Literal.complement, TimeBounded, CNF.Literal.atom, Atom.time]

/-- Step clauses never refer to a row after the next tick. -/
theorem timeBounded_stepClauses (qs : List Q) (symbols : List Γ) (rule : Rule Q Γ width) (t : Nat) :
    TimeBounded (t + 1) (stepClauses qs symbols rule t) := by
  simp only [stepClauses, timeBounded_append, timeBounded_flatMap]
  exact ⟨fun q _ i _ a _ ↦ timeBounded_localUpdate rule t q i a,
    fun i _ j _ a _ ↦ timeBounded_localCopy t i j a⟩

/-- The trace constraints mention only ticks through the stated time horizon. -/
theorem timeBounded_traceClauses [DecidableEq Q] [DecidableEq Γ]
    (qs : List Q) (symbols : List Γ) (rule : Rule Q Γ width) (steps : Nat) :
    TimeBounded steps (traceClauses qs symbols rule steps) := by
  simp only [traceClauses, timeBounded_append, timeBounded_flatMap, List.mem_range]
  exact ⟨fun t ht ↦ (timeBounded_rowClauses qs symbols t).mono (Nat.le_of_lt_succ ht),
    fun t ht ↦ (timeBounded_stepClauses qs symbols rule t).mono (Nat.succ_le_of_lt ht)⟩

/-- With a bounded initial block, the entire tableau fits through the accepting tick. -/
theorem timeBounded_acceptingClauses [DecidableEq Q] [DecidableEq Γ]
    (qs : List Q) (symbols : List Γ) (rule : Rule Q Γ width) (steps : Nat) (accept : Q)
    (initial : CNF.Formula (Atom Q Γ width)) (h : TimeBounded steps initial) :
    TimeBounded steps (acceptingClauses qs symbols rule steps accept initial) := by
  simp only [acceptingClauses, timeBounded_append]
  exact ⟨⟨h, timeBounded_traceClauses qs symbols rule steps⟩,
    by simp [TimeBounded, CNF.Literal.atom, Atom.time]⟩

/-- Every renamed literal has a natural name below the number of allocated indices. -/
theorem TimeBounded.names_lt (qIndex : Q ↪ Fin qCount) (symbolIndex : Γ ↪ Fin symbolCount)
    {F : CNF.Formula (Atom Q Γ width)} {steps : Nat} (h : TimeBounded steps F) :
    ∀ c ∈ CNF.mapAtoms (Atom.name qIndex symbolIndex) F, ∀ l ∈ c,
      l.atom < (steps + 1) * atomStride qCount width symbolCount := by
  intro c hc l hl
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hl
  rw [CNF.Literal.atom_map]
  exact k.atom.name_lt_of_time_le qIndex symbolIndex (h d hd k hk)

/-- The dense names in the accepting tableau are uniformly bounded, also when written in unary. -/
theorem acceptingClauses_names_lt [DecidableEq Q] [DecidableEq Γ]
    (qIndex : Q ↪ Fin qCount) (symbolIndex : Γ ↪ Fin symbolCount)
    (qs : List Q) (symbols : List Γ) (rule : Rule Q Γ width) (steps : Nat) (accept : Q)
    (initial : CNF.Formula (Atom Q Γ width)) (h : TimeBounded steps initial) :
    ∀ c ∈ CNF.mapAtoms (Atom.name qIndex symbolIndex)
      (acceptingClauses qs symbols rule steps accept initial), ∀ l ∈ c,
      l.atom < (steps + 1) * atomStride qCount width symbolCount :=
  TimeBounded.names_lt qIndex symbolIndex
    (timeBounded_acceptingClauses qs symbols rule steps accept initial h)

end PvsNP.Tableau
