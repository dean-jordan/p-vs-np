module

public import PvsNP.SAT.BranchRefutation
public import PvsNP.SAT.PigeonholeFormula

import Init.Data.List.Nat.Pairwise
import Init.Data.List.Perm

/-! # A branching lower bound for the functional pigeonhole principle -/

public section

namespace PvsNP.Pigeonhole

open SATBranching

variable {n : Nat}

private def UniqueBy {β : Type} (key : Variable n → β) (xs : List (Variable n)) : Prop :=
  ∀ ⦃u v⦄, u ∈ xs → v ∈ xs → key u = key v → u = v

private theorem uniqueBy_cons {β : Type} (key : Variable n → β) {xs : List (Variable n)}
    {v : Variable n} (hOld : UniqueBy key xs) (hNew : key v ∉ xs.map key) :
    UniqueBy key (v :: xs) := by
  intro u w hu hw hKey
  rcases List.mem_cons.mp hu with he | hu'
  · subst u
    rcases List.mem_cons.mp hw with he | hw'
    · subst w
      rfl
    · exact (hNew (List.mem_map.mpr ⟨w, hw', hKey.symm⟩)).elim
  · rcases List.mem_cons.mp hw with he | hw'
    · subst w
      exact (hNew (List.mem_map.mpr ⟨u, hu', hKey⟩)).elim
    · exact hOld hu' hw' hKey

/-- True entries form a partial matching. A false entry is blocked by that matching or
recorded among the explicitly excluded pairs. -/
private structure GameState (n : Nat) where
  value : PartialAssignment (Variable n)
  placed : List (Variable n)
  excluded : List (Variable n)
  positive : ∀ v, value v = some true ↔ v ∈ placed
  negative : ∀ v, value v = some false →
    v.1 ∈ placed.map Prod.fst ∨ v.2 ∈ placed.map Prod.snd ∨ v ∈ excluded
  rows : UniqueBy Prod.fst placed
  columns : UniqueBy Prod.snd placed

namespace GameState

private def initial (n : Nat) : GameState n where
  value := fun _ ↦ none
  placed := []
  excluded := []
  positive := by simp
  negative := by simp
  rows := by simp [UniqueBy]
  columns := by simp [UniqueBy]

private def score (s : GameState n) : Nat := s.placed.length + s.excluded.length

private def putFalse (s : GameState n) (v : Variable n) (excluded : List (Variable n))
    (fresh : s.value v = none) (hKeep : s.excluded ⊆ excluded)
    (hReason : v.1 ∈ s.placed.map Prod.fst ∨ v.2 ∈ s.placed.map Prod.snd ∨ v ∈ excluded) :
    GameState n where
  value := assign s.value v false
  placed := s.placed
  excluded := excluded
  positive := by
    intro u
    by_cases h : u = v
    · subst u
      simpa [fresh] using s.positive v
    · simpa [h] using s.positive u
  negative := by
    intro u hFalse
    by_cases h : u = v
    · subst u
      exact hReason
    · have hOld : s.value u = some false := by simpa [h] using hFalse
      rcases s.negative u hOld with hRow | hColumn | hExcluded
      · exact Or.inl hRow
      · exact Or.inr (Or.inl hColumn)
      · exact Or.inr (Or.inr (hKeep hExcluded))
  rows := s.rows
  columns := s.columns

private def putTrue (s : GameState n) (v : Variable n)
    (hRow : v.1 ∉ s.placed.map Prod.fst) (hColumn : v.2 ∉ s.placed.map Prod.snd) :
    GameState n where
  value := assign s.value v true
  placed := v :: s.placed
  excluded := s.excluded
  positive := by
    intro u
    by_cases h : u = v
    · subst u
      simp
    · simpa [h] using s.positive u
  negative := by
    intro u hFalse
    by_cases h : u = v
    · subst u
      simp at hFalse
    · have hOld : s.value u = some false := by simpa [h] using hFalse
      rcases s.negative u hOld with hUsedRow | hUsedColumn | hExcluded
      · exact Or.inl (List.mem_cons_of_mem _ hUsedRow)
      · exact Or.inr (Or.inl (List.mem_cons_of_mem _ hUsedColumn))
      · exact Or.inr (Or.inr hExcluded)
  rows := uniqueBy_cons _ s.rows hRow
  columns := uniqueBy_cons _ s.columns hColumn

private theorem le_score_of_falsified_row (s : GameState n) (row : Fin (n + 1))
    (hFalse : Falsified s.value (rowClause row)) : n ≤ s.score := by
  have hAll (col : Fin n) : s.value (row, col) = some false :=
    hFalse _ (mem_rowClause_iff.mpr ⟨col, rfl⟩)
  have hRow : row ∉ s.placed.map Prod.fst := by
    intro hUsed
    obtain ⟨v, hv, he⟩ := List.mem_map.mp hUsed
    have hPair : (row, v.2) = v := Prod.ext he.symm rfl
    have hVal := hAll v.2
    rw [hPair, (s.positive v).mpr hv] at hVal
    cases hVal
  have hCover : List.finRange n ⊆ (s.placed ++ s.excluded).map Prod.snd := by
    intro col _
    rw [List.map_append, List.mem_append]
    rcases s.negative (row, col) (hAll col) with hUsedRow | hUsedColumn | hExcluded
    · exact (hRow hUsedRow).elim
    · exact Or.inl hUsedColumn
    · exact Or.inr (List.mem_map.mpr ⟨(row, col), hExcluded, rfl⟩)
  simpa only [List.length_finRange, List.length_map, List.length_append, score] using
    (List.nodup_finRange n).length_le_of_subset hCover

private theorem noConflict (s : GameState n) (hScore : s.score < n) :
    ¬ ∃ c ∈ formula n, Falsified s.value c := by
  rintro ⟨c, hc, hFalse⟩
  rcases mem_formula_iff.mp hc with ⟨row, rfl⟩ | ⟨u, v, hNe, hKey, rfl⟩
  · exact Nat.not_le_of_lt hScore (s.le_score_of_falsified_row row hFalse)
  · have hu : u ∈ s.placed := (s.positive u).mp (hFalse _ (List.mem_cons_self ..))
    have hv : v ∈ s.placed := (s.positive v).mp (hFalse _ (List.mem_cons_of_mem _
      (List.mem_singleton_self _)))
    exact hNe (hKey.elim (s.rows hu hv) (s.columns hu hv))

end GameState

/-- A free pair permits either answer and contributes one point to the score. A pair blocked
by the matching can be assigned false without changing the score. -/
private def strategy (n : Nat) : Strategy (formula n) n where
  State := GameState n
  value := GameState.value
  score := GameState.score
  noConflict := GameState.noConflict
  respond := by
    intro s v hFresh
    by_cases hBlocked : v.1 ∈ s.placed.map Prod.fst ∨ v.2 ∈ s.placed.map Prod.snd
    · let next := s.putFalse v s.excluded hFresh (fun _ h ↦ h) (by
        rcases hBlocked with hRow | hColumn
        · exact Or.inl hRow
        · exact Or.inr (Or.inl hColumn))
      exact Or.inl ⟨false, next, rfl, Nat.le_refl _⟩
    · let no := s.putFalse v (v :: s.excluded) hFresh (fun _ h ↦ List.mem_cons_of_mem _ h)
        (Or.inr (Or.inr (List.mem_cons_self ..)))
      let yes := s.putTrue v (fun h ↦ hBlocked (Or.inl h)) (fun h ↦ hBlocked (Or.inr h))
      refine Or.inr ⟨⟨no, rfl, ?_⟩, ⟨yes, rfl, ?_⟩⟩
      · simp only [GameState.score, no, GameState.putFalse, List.length_cons]
        omega
      · simp only [GameState.score, yes, GameState.putTrue, List.length_cons]
        omega

/-- Every branching refutation of the functional pigeonhole principle has at least
`2^n` leaves, even when the branch variable depends on the preceding assignments. -/
theorem formula_refutation_leaves (n : Nat) {tree : Tree (Variable n)}
    (h : Refutes (formula n) (fun _ ↦ none) tree) : 2 ^ n ≤ tree.leaves := by
  exact (strategy n).leaves_lower_bound (GameState.initial n) h

end PvsNP.Pigeonhole
