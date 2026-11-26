module

public import PvsNP.Circuits.TruthTable

import Init.Data.List.Nat.TakeDrop

/-! # Index truth-table rows without enumerating them -/

public section

namespace PvsNP.MCSP

open AssignmentQueryTree (allAssignments length_allAssignments mem_allAssignments)
open Circuits (truthTable length_truthTable)

variable {n : Nat}

private def rankFrom : {n : Nat} → (Fin n → Bool) → Nat → Nat
  | 0, _, acc => acc
  | n + 1, bits, acc => rankFrom (fun i : Fin n ↦ bits i.succ) (2 * acc + (bits 0).toNat)

/-- The big-endian index of the row, computed by reading its bits once. -/
def rank (bits : Fin n → Bool) : Nat := rankFrom bits 0

private theorem rankFrom_eq (bits : Fin n → Bool) (acc : Nat) :
    rankFrom bits acc = acc * 2 ^ n + rankFrom bits 0 := by
  induction n generalizing acc with
  | zero => simp [rankFrom]
  | succ n ih =>
    let tail (i : Fin n) := bits i.succ
    let b := (bits 0).toNat
    change rankFrom tail (2 * acc + b) = acc * 2 ^ (n + 1) + rankFrom tail (2 * 0 + b)
    rw [Nat.mul_zero, Nat.zero_add, ih tail (2 * acc + b), ih tail b, Nat.pow_succ, Nat.add_mul]
    ac_rfl

@[simp] theorem rank_zero (bits : Fin 0 → Bool) : rank bits = 0 := by simp [rank, rankFrom]

theorem rank_cases (b : Bool) (tail : Fin n → Bool) :
    rank (Fin.cases (motive := fun _ ↦ Bool) b tail) = b.toNat * 2 ^ n + rank tail := by
  simp only [rank, rankFrom, Fin.cases_zero, Fin.cases_succ, Nat.mul_zero, Nat.zero_add]
  rw [rankFrom_eq]

theorem rank_lt (bits : Fin n → Bool) : rank bits < 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    let tail (i : Fin n) := bits i.succ
    have hBits : Fin.cases (bits 0) tail = bits := funext fun i ↦
      Fin.cases (by simp) (fun _ ↦ by simp [tail]) i
    have hTail := ih tail
    have hHead := Nat.mul_le_mul_right (2 ^ n) (Bool.toNat_le (bits 0))
    rw [Nat.one_mul] at hHead
    rw [← hBits, rank_cases, Nat.pow_succ]
    omega

private theorem rank_of_getElem? {n i : Nat} {bits : Fin n → Bool}
    (h : (allAssignments n)[i]? = some bits) : rank bits = i := by
  induction n generalizing i with
  | zero =>
    have hi : i = 0 := by
      have hLt := (List.getElem?_eq_some_iff.mp h).1
      simp only [allAssignments, List.length_singleton] at hLt
      omega
    simp only [rank_zero, hi]
  | succ n ih =>
    let low := (allAssignments n).map (fun a ↦ Fin.cases (motive := fun _ ↦ Bool) false a)
    let high := (allAssignments n).map (fun a ↦ Fin.cases (motive := fun _ ↦ Bool) true a)
    change (low ++ high)[i]? = some bits at h
    by_cases hLow : i < (allAssignments n).length
    · rw [List.getElem?_append_left (by simpa only [low, List.length_map] using hLow)] at h
      simp only [low, List.getElem?_map, List.getElem?_eq_getElem hLow, Option.map_some] at h
      rw [← Option.some.inj h, rank_cases]
      simpa only [Bool.toNat_false, Nat.zero_mul, Nat.zero_add] using
        ih (List.getElem?_eq_getElem hLow)
    · have hRight : low.length ≤ i := by
        simpa only [low, List.length_map] using Nat.le_of_not_gt hLow
      rw [List.getElem?_append_right hRight] at h
      simp only [high, List.getElem?_map] at h
      obtain ⟨tail, hTail, hBits⟩ := Option.map_eq_some_iff.mp h
      have hRank := ih hTail
      rw [← hBits, rank_cases, hRank]
      have hLength : low.length = 2 ^ n := by
        simp only [low, List.length_map, length_allAssignments]
      simp only [Bool.toNat_true, Nat.one_mul, ← hLength]
      omega

theorem rank_assignment_at (n i : Nat) (hi : i < (allAssignments n).length) :
    rank ((allAssignments n)[i]'hi) = i :=
  rank_of_getElem? (List.getElem?_eq_getElem hi)

theorem rank_injective (n : Nat) : Function.Injective (rank : (Fin n → Bool) → Nat) := by
  intro x y hRank
  obtain ⟨i, hi, hx⟩ := List.mem_iff_getElem.mp (mem_allAssignments x)
  obtain ⟨j, hj, hy⟩ := List.mem_iff_getElem.mp (mem_allAssignments y)
  rw [← hx, ← hy, rank_assignment_at n i hi, rank_assignment_at n j hj] at hRank
  subst j
  exact hx.symm.trans hy

theorem assignment_at_rank (bits : Fin n → Bool) :
    (allAssignments n)[rank bits]'(by rw [length_allAssignments]; exact rank_lt bits) = bits :=
  rank_injective n (rank_assignment_at n _ _)

theorem mem_take_allAssignments_iff_rank_lt (bits : Fin n → Bool) (k : Nat) :
    bits ∈ (allAssignments n).take k ↔ rank bits < k := by
  rw [List.mem_take_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [rank_assignment_at]
    exact (Nat.lt_min.mp hi).1
  · intro hRank
    have hLength : rank bits < (allAssignments n).length := by
      rw [length_allAssignments]
      exact rank_lt bits
    exact ⟨rank bits, Nat.lt_min.mpr ⟨hRank, hLength⟩, assignment_at_rank bits⟩

/-- Two circuits or Boolean functions agree on the table prefix exactly when
they agree on every input whose numerical rank lies in that prefix. -/
theorem truthTable_agree_on_take_iff (f g : (Fin n → Bool) → Bool) (k : Nat) :
    (truthTable n f).take k = (truthTable n g).take k ↔ ∀ x, rank x < k → f x = g x := by
  rw [truthTable, truthTable, ← List.map_take, ← List.map_take, List.map_inj_left]
  simp only [mem_take_allAssignments_iff_rank_lt]

theorem truthTable_take_succ (f : (Fin n → Bool) → Bool) (i : Nat) (hi : i < 2 ^ n) :
    (truthTable n f).take (i + 1) =
      (truthTable n f).take i ++ [f ((allAssignments n)[i]'(by rwa [length_allAssignments]))] := by
  rw [List.take_succ_eq_append_getElem (by rwa [length_truthTable])]
  simp only [truthTable, List.getElem_map]

end PvsNP.MCSP
