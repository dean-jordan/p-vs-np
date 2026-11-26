module

public import PvsNP.SAT.CNF

import Init.Data.List.FinRange
import Init.Data.List.Nat.Pairwise
import Init.Data.List.Nat.Sum
import Init.Data.List.Perm

/-! # Pigeonhole formulas with functional rows -/

public section

namespace PvsNP.Pigeonhole

open CNF (Clause Formula Literal)

/-- Variable `(row, hole)` says that the pigeon in `row` occupies `hole`. -/
abbrev Variable (n : Nat) := Fin (n + 1) × Fin n

/-- Each pigeon must occupy some hole. -/
@[expose] def rowClause {n : Nat} (row : Fin (n + 1)) : Clause (Variable n) :=
  (List.finRange n).map fun hole ↦ .pos (row, hole)

private def variables (n : Nat) : List (Variable n) :=
  (List.finRange (n + 1)).flatMap fun row ↦ (List.finRange n).map fun hole ↦ (row, hole)

private def exclusionClauses (n : Nat) : Formula (Variable n) :=
  (variables n).flatMap fun u ↦
    ((variables n).filter fun v ↦ decide (u ≠ v ∧ (u.1 = v.1 ∨ u.2 = v.2))).map
      fun v ↦ [.neg u, .neg v]

/-- The row clauses require all pigeons to occupy holes. The pair clauses make the
occupied positions injective in each coordinate. -/
def formula (n : Nat) : Formula (Variable n) :=
  ((List.finRange (n + 1)).map rowClause) ++ exclusionClauses n

theorem mem_rowClause_iff {n : Nat} {row : Fin (n + 1)} {l : Literal (Variable n)} :
    l ∈ rowClause row ↔ ∃ hole : Fin n, l = .pos (row, hole) := by
  constructor
  · intro h
    obtain ⟨hole, _, rfl⟩ := List.mem_map.mp h
    exact ⟨hole, rfl⟩
  · rintro ⟨hole, rfl⟩
    exact List.mem_map_of_mem (List.mem_finRange hole)

private theorem mem_variables {n : Nat} (v : Variable n) : v ∈ variables n :=
  List.mem_flatMap.mpr ⟨v.1, List.mem_finRange v.1,
    List.mem_map_of_mem (List.mem_finRange v.2)⟩

/-- Membership records exactly the row clauses and the incompatible pairs. -/
theorem mem_formula_iff {n : Nat} {c : Clause (Variable n)} :
    c ∈ formula n ↔ (∃ row : Fin (n + 1), c = rowClause row) ∨
      (∃ u v : Variable n, u ≠ v ∧ (u.1 = v.1 ∨ u.2 = v.2) ∧ c = [.neg u, .neg v]) := by
  constructor
  · intro h
    rcases List.mem_append.mp h with h | h
    · obtain ⟨row, _, rfl⟩ := List.mem_map.mp h
      exact Or.inl ⟨row, rfl⟩
    · obtain ⟨u, _, h⟩ := List.mem_flatMap.mp h
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp h
      have hPair := of_decide_eq_true (List.mem_filter.mp hv).2
      exact Or.inr ⟨u, v, hPair.1, hPair.2, rfl⟩
  · rintro (⟨row, rfl⟩ | ⟨u, v, hNe, hEq, rfl⟩)
    · exact List.mem_append_left _ (List.mem_map_of_mem (List.mem_finRange row))
    · exact List.mem_append_right _ <| List.mem_flatMap.mpr ⟨u, mem_variables u,
        List.mem_map_of_mem (List.mem_filter.mpr ⟨mem_variables v, decide_eq_true ⟨hNe, hEq⟩⟩)⟩

private theorem length_rowClause {n : Nat} (row : Fin (n + 1)) :
    (rowClause row).length = n := by
  simp [rowClause]

private theorem length_variables (n : Nat) : (variables n).length = (n + 1) * n := by
  simp only [variables, List.length_flatMap, List.length_map, List.length_finRange,
    List.map_const', List.sum_replicate_nat]

/-- The formula has polynomial size even when incompatible pairs are listed in both orders. -/
theorem formula_size_le (n : Nat) :
    CNF.size (formula n) ≤ (n + 1) * (n + 1) + 3 * ((n + 1) * n) ^ 2 := by
  unfold formula
  rw [CNF.size_append, CNF.size_map_of_length _ _ n (fun row _ ↦ length_rowClause row),
    List.length_finRange, Nat.add_le_add_iff_left]
  calc
    CNF.size (exclusionClauses n) ≤ (variables n).length * ((variables n).length * 3) := by
      apply CNF.size_flatMap_le
      intro u _
      rw [CNF.size_map_of_length _ _ 2 (fun _ _ ↦ rfl)]
      exact Nat.mul_le_mul_right 3 (List.length_filter_le ..)
    _ = 3 * ((n + 1) * n) ^ 2 := by rw [length_variables, Nat.pow_two]; ac_rfl

/-- With at least one hole, a refutation must inspect variables to find a conflict. -/
theorem nil_not_mem_formula {n : Nat} (hPos : 0 < n) : ([] : Clause (Variable n)) ∉ formula n := by
  intro h
  rcases mem_formula_iff.mp h with ⟨row, hRow⟩ | ⟨_, _, _, _, hPair⟩
  · have hLength := congrArg List.length hRow
    rw [length_rowClause] at hLength
    exact Nat.ne_of_gt hPos hLength.symm
  · cases hPair

/-- A satisfying assignment would give an injection of `n + 1` pigeons into `n` holes. -/
theorem formula_not_satisfiable (n : Nat) : ¬ CNF.Satisfiable (formula n) := by
  classical
  rintro ⟨σ, hSat⟩
  have hExists (row : Fin (n + 1)) : ∃ hole : Fin n, σ (row, hole) = true := by
    obtain ⟨l, hl, hLiteral⟩ := hSat _ (mem_formula_iff.mpr (Or.inl ⟨row, rfl⟩))
    obtain ⟨hole, rfl⟩ := mem_rowClause_iff.mp hl
    exact ⟨hole, hLiteral⟩
  let pick (row : Fin (n + 1)) := Classical.choose (hExists row)
  have hTrue (row : Fin (n + 1)) : σ (row, pick row) = true := Classical.choose_spec (hExists row)
  have hInjective : Function.Injective pick := by
    intro a b hHole
    by_cases hRows : a = b
    · exact hRows
    · have hPair : (a, pick a) ≠ (b, pick b) := fun h ↦ hRows (congrArg Prod.fst h)
      have hClause := hSat _ (mem_formula_iff.mpr (Or.inr
        ⟨(a, pick a), (b, pick b), hPair, Or.inr hHole, rfl⟩))
      simp [hTrue] at hClause
  have hNodup : ((List.finRange (n + 1)).map pick).Nodup :=
    List.Pairwise.map _ (fun _ _ hNe hEq ↦ hNe (hInjective hEq)) (List.nodup_finRange _)
  have hLength := hNodup.length_le_of_subset (l₂ := List.finRange n) fun {hole} _ ↦
    List.mem_finRange hole
  exact Nat.not_succ_le_self n (by simpa only [List.length_map, List.length_finRange] using hLength)

end PvsNP.Pigeonhole
