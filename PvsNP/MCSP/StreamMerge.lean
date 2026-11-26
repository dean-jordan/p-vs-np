module

public import PvsNP.MCSP.Agreement
public import PvsNP.MCSP.PrefixOrder

/-! # One-bit circuit-minimization merge requests -/

public section

namespace PvsNP.MCSP

open Circuits
open AssignmentQueryTree (allAssignments length_allAssignments)

variable {n : Nat}

/-- A candidate agrees with the old circuit on earlier rows and with the
new bit on the next row. The old circuit may have any values later. -/
@[expose] def MergeAgrees (old : BooleanCircuit n) (seen : Nat) (bit : Bool)
    (candidate : BooleanCircuit n) : Prop :=
  (∀ x, rank x < seen → candidate.eval x = old.eval x) ∧
    ∀ x, rank x = seen → candidate.eval x = bit

abbrev MergeOracle (n : Nat) := BooleanCircuit n → Nat → Bool → Option (BooleanCircuit n)

/-- The merger must find a bounded circuit whenever the request has one. -/
structure CorrectMerge (merge : MergeOracle n) (cap : Nat) : Prop where
  sound : ∀ old seen bit candidate, merge old seen bit = some candidate →
    candidate.size ≤ cap ∧ MergeAgrees old seen bit candidate
  complete : ∀ old seen bit, (∃ c : BooleanCircuit n, c.size ≤ cap ∧ MergeAgrees old seen bit c) →
    ∃ c, merge old seen bit = some c

/-- Exhaustive reference merger used to validate the interface. -/
@[expose] def referenceMerge (n cap : Nat) : MergeOracle n := fun old seen bit ↦
  findBoundedAgreement n cap (fun x ↦ decide (rank x ≤ seen))
    (fun x ↦ if rank x < seen then old.eval x else bit)

theorem referenceMerge_correct (n cap : Nat) : CorrectMerge (referenceMerge n cap) cap := by
  constructor
  · intro old seen bit candidate hFound
    obtain ⟨hSize, hEval⟩ := size_eq_and_agrees_of_findBoundedAgreement_eq_some
      (show findBoundedAgreement n cap (fun x ↦ decide (rank x ≤ seen))
        (fun x ↦ if rank x < seen then old.eval x else bit) = some candidate from hFound)
    refine ⟨Nat.le_of_eq hSize, ?_, ?_⟩
    · intro x hx
      simpa only [ite_eq_left hx] using hEval x (decide_eq_true (Nat.le_of_lt hx))
    · intro x hx
      simpa only [ite_eq_right (Nat.not_lt.mpr (Nat.le_of_eq hx.symm))] using
        hEval x (decide_eq_true (Nat.le_of_eq hx))
  · intro old seen bit hExists
    apply Option.isSome_iff_exists.mp
    apply (findBoundedAgreement_isSome_iff n cap _ _).mpr
    obtain ⟨c, hSize, hOld, hNew⟩ := hExists
    refine ⟨c, hSize, fun x hx ↦ ?_⟩
    rcases Nat.lt_or_eq_of_le (of_decide_eq_true hx) with hEarlier | hNext
    · exact (hOld x hEarlier).trans (ite_eq_left hEarlier).symm
    · exact (hNew x hNext).trans (ite_eq_right (Nat.not_lt.mpr (Nat.le_of_eq hNext.symm))).symm

/-- Only the rows read so far constrain the retained circuit. -/
@[expose] def MatchesPrefix (c : BooleanCircuit n) (pref : BinaryWord) : Prop :=
  (truthTable n c.eval).take pref.length = pref

theorem length_le_of_matchesPrefix {c : BooleanCircuit n} {pref : BinaryWord}
    (h : MatchesPrefix c pref) : pref.length ≤ 2 ^ n := by
  have hLength := congrArg List.length h
  simp only [List.length_take, length_truthTable] at hLength
  exact hLength ▸ Nat.min_le_right ..

theorem matchesPrefix_of_append_bit {c : BooleanCircuit n} {pref : BinaryWord} {bit : Bool}
    (h : MatchesPrefix c (pref ++ [bit])) : MatchesPrefix c pref := by
  have hTake := congrArg (List.take pref.length) h
  rw [List.take_take, Nat.min_eq_left (by simp), List.take_left] at hTake
  exact hTake

/-- The local merge condition is exactly agreement on the expanded prefix. -/
theorem matchesPrefix_append_bit_iff {old c : BooleanCircuit n} (pref : BinaryWord)
    (bit : Bool) (hOld : MatchesPrefix old pref) (hRoom : pref.length < 2 ^ n) :
    MatchesPrefix c (pref ++ [bit]) ↔ MergeAgrees old pref.length bit c := by
  have hIndex : pref.length < (allAssignments n).length := by rwa [length_allAssignments]
  let x := (allAssignments n)[pref.length]'hIndex
  have hRank : rank x = pref.length := rank_assignment_at n _ hIndex
  have hTake : (truthTable n c.eval).take (pref ++ [bit]).length =
      (truthTable n c.eval).take pref.length ++ [c.eval x] := by
    simpa only [List.length_append, List.length_singleton, x] using
      truthTable_take_succ c.eval pref.length hRoom
  constructor
  · intro h
    have hEarlier := matchesPrefix_of_append_bit h
    have hEq : (truthTable n c.eval).take pref.length =
        (truthTable n old.eval).take pref.length := hEarlier.trans hOld.symm
    refine ⟨(truthTable_agree_on_take_iff c.eval old.eval _).mp hEq, fun y hy ↦ ?_⟩
    have hSame : y = x := rank_injective n (hy.trans hRank.symm)
    subst y
    change (truthTable n c.eval).take (pref ++ [bit]).length = _ at h
    rw [hTake, hEarlier] at h
    exact List.singleton_inj.mp (List.append_cancel_left h)
  · rintro ⟨hEarlier, hNext⟩
    have hEq := (truthTable_agree_on_take_iff c.eval old.eval _).mpr hEarlier
    change (truthTable n c.eval).take (pref ++ [bit]).length = _
    rw [hTake, hEq, hOld, hNext x hRank]

end PvsNP.MCSP
