module

public import Mathlib.Data.Fintype.BigOperators

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card

/-! # Counting injective crossing transcripts -/

namespace PvsNP.Crossing

open scoped BigOperators

private theorem card_short_le {I S : Type*} [Fintype I] [Fintype S]
    (transcript : I → List S) (ℓ : Nat) (hInjective : Function.Injective transcript) :
    ((Finset.univ : Finset I).filter fun i ↦ (transcript i).length < ℓ).card ≤
      (Fintype.card S + 1) ^ ℓ := by
  classical
  let short := (Finset.univ : Finset I).filter fun i ↦ (transcript i).length < ℓ
  let padded (i : short) (p : Fin ℓ) : Option S := (transcript i.val)[p.val]?
  have hPadded : Function.Injective padded := by
    intro a b hab
    apply Subtype.ext
    apply hInjective
    apply List.ext_getElem?
    intro p
    by_cases hp : p < ℓ
    · exact congrFun hab ⟨p, hp⟩
    · have ha : (transcript a.val).length < ℓ := (Finset.mem_filter.mp a.property).2
      have hb : (transcript b.val).length < ℓ := (Finset.mem_filter.mp b.property).2
      rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  have hCard := Fintype.card_le_of_injective padded hPadded
  simpa only [Fintype.card_coe, Fintype.card_pi_const, Fintype.card_option, short] using hCard

private theorem column_length_lower {I S : Type*} [Fintype I] [Fintype S]
    (transcript : I → List S) (ℓ : Nat) (hInjective : Function.Injective transcript)
    (hCount : 2 * (Fintype.card S + 1) ^ ℓ ≤ Fintype.card I) :
    Fintype.card I * ℓ ≤ 2 * ∑ i : I, (transcript i).length := by
  classical
  let long := (Finset.univ : Finset I).filter fun i ↦ ¬ (transcript i).length < ℓ
  have hShort := card_short_le transcript ℓ hInjective
  have hSplit :
      ((Finset.univ : Finset I).filter fun i ↦ (transcript i).length < ℓ).card +
        long.card = Fintype.card I := by
    simpa only [Finset.card_univ, long] using
      Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset I)) (fun i ↦ (transcript i).length < ℓ)
  have hHalf : Fintype.card I ≤ 2 * long.card := by omega
  have hLong : long.card * ℓ ≤ ∑ i : I, (transcript i).length := calc
    _ = ∑ _i ∈ long, ℓ := by simp only [Finset.sum_const, Nat.nsmul_eq_mul]
    _ ≤ ∑ i ∈ long, (transcript i).length := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.le_of_not_gt (Finset.mem_filter.mp hi).2
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ long)
  calc
    Fintype.card I * ℓ ≤ (2 * long.card) * ℓ := Nat.mul_le_mul_right ℓ hHalf
    _ = 2 * (long.card * ℓ) := Nat.mul_assoc ..
    _ ≤ _ := Nat.mul_le_mul_left 2 hLong

/-- If each cut distinguishes the rows and at most half the rows can
have a transcript shorter than `ℓ`, one row has total length at least
half the number of cuts times `ℓ`. -/
public theorem exists_row_large_transcript_sum {I J S : Type*}
    [Fintype I] [Fintype J] [Fintype S]
    (F : I → J → List S) (ℓ : Nat) (hInjective : ∀ j, Function.Injective (fun i ↦ F i j))
    (hCount : 2 * (Fintype.card S + 1) ^ ℓ ≤ Fintype.card I) :
    ∃ i : I, Fintype.card J * ℓ ≤ 2 * ∑ j : J, (F i j).length := by
  classical
  have hPositive : 0 < Fintype.card I :=
    (Nat.mul_pos (by decide) (Nat.pow_pos (Nat.succ_pos _))).trans_le hCount
  let _ : Nonempty I := Fintype.card_pos_iff.mp hPositive
  have hColumns := Finset.sum_le_sum (s := (Finset.univ : Finset J))
    (fun j _ ↦ column_length_lower (fun i ↦ F i j) ℓ (hInjective j) hCount)
  have hTotal :
      Fintype.card J * (Fintype.card I * ℓ) ≤
        2 * ∑ j : J, ∑ i : I, (F i j).length := by
    simpa only [Finset.sum_const, Nat.nsmul_eq_mul, Finset.card_univ,
      Nat.two_mul, Finset.sum_add_distrib] using hColumns
  rw [Finset.sum_comm] at hTotal
  by_contra hNone
  have hRows (i : I) : 2 * (∑ j : J, (F i j).length) < Fintype.card J * ℓ :=
    Nat.lt_of_not_ge (fun hi ↦ hNone ⟨i, hi⟩)
  have hStrict :
      2 * (∑ i : I, ∑ j : J, (F i j).length) <
        Fintype.card I * (Fintype.card J * ℓ) := by
    have hSum := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset I))
      Finset.univ_nonempty (fun i _ ↦ hRows i)
    simpa only [Finset.sum_const, Nat.nsmul_eq_mul, Finset.card_univ,
      Nat.two_mul, Finset.sum_add_distrib] using hSum
  have hImpossible := hTotal.trans_lt hStrict
  rw [Nat.mul_left_comm (Fintype.card J) (Fintype.card I)] at hImpossible
  exact (Nat.lt_irrefl _) hImpossible

end PvsNP.Crossing
