module

public import PvsNP.SAT.CrossingFamily
public import PvsNP.SAT.CrossingScale
public import PvsNP.TuringMachine.Crossing.Counting
public import PvsNP.TuringMachine.Crossing.Input
public import PvsNP.TuringMachine.Crossing.Splice
public import PvsNP.TuringMachine.Crossing.Time
public import Mathlib.SetTheory.Cardinal.Finite

/-! # A crossing-sequence time lower bound for binary CNF-SAT -/

public section

namespace PvsNP.SATCrossing

open scoped BigOperators

private theorem absolute_rejects_diagonal (M : Machine Bool) (hDecides : M.Decides CNFSAT)
    (word : BinaryWord) (t : Nat) (hReject : word ∉ CNFSAT) (h : M.HaltsWithin word t) :
    (M.absoluteRun t (M.absoluteStart word)).state = .inr false := by
  rw [M.absoluteRun_start_state]
  obtain ⟨answer, hAnswer⟩ := (M.haltsWithin_iff _ t).mp h
  cases answer
  · exact hAnswer
  · exact (hReject ((hDecides _).mpr ⟨t, hAnswer⟩)).elim

private theorem splice_diagonal_start {I : Type} (M : Machine Bool)
    (left right : I → BinaryWord) (middle : BinaryWord) (B k : Nat)
    (hLeft : ∀ a, (left a).length = B) (hPositive : 0 < B) (a b : I) (hk : k ≤ middle.length) :
    M.spliceConfig ((B + k : Nat) : Int)
        (M.absoluteStart (left a ++ middle ++ right a))
        (M.absoluteStart (left b ++ middle ++ right b)) =
      M.absoluteStart (left a ++ middle ++ right b) := by
  let front (i : I) := left i ++ middle.take k
  let back (i : I) := middle.drop k ++ right i
  have hLength (i : I) : (front i).length = B + k := by
    simp only [front, List.length_append, hLeft, List.length_take, Nat.min_eq_left hk]
  have hParts (i j : I) : front i ++ back j = left i ++ middle ++ right j := by
    simp only [front, back, List.append_assoc]
    rw [← List.append_assoc (middle.take k), List.take_append_drop]
  have hPos : 0 < (front a).length := by
    rw [hLength]
    omega
  have hJoin := M.spliceConfig_absoluteStart_append (front a) (front b) (back a) (back b)
    ((hLength a).trans (hLength b).symm) hPos
  simpa only [hLength, hParts] using hJoin

private theorem diagonal_transcripts_injective {I : Type} (M : Machine Bool)
    (hDecides : M.Decides CNFSAT) (left right : I → BinaryWord) (middle : BinaryWord) (B t k : Nat)
    (hLeft : ∀ a, (left a).length = B) (hPositive : 0 < B)
    (hReject : ∀ a, left a ++ middle ++ right a ∉ CNFSAT)
    (hAccept : ∀ a b, a ≠ b → left a ++ middle ++ right b ∈ CNFSAT)
    (hk : k ≤ middle.length)
    (hClock : ∀ a, M.HaltsWithin (left a ++ middle ++ right a) t) :
    Function.Injective (fun a : I ↦ M.crossingTranscript ((B + k : Nat) : Int)
      t (M.absoluteStart (left a ++ middle ++ right a))) := by
  intro a b hTrace
  by_contra hNe
  let cut : Int := ((B + k : Nat) : Int)
  let start (i : I) := M.absoluteStart (left i ++ middle ++ right i)
  have hSide : (start a).position < cut ↔ (start b).position < cut := Iff.rfl
  obtain ⟨stop, hMixedReject⟩ := M.absolute_halts_splice_of_crossingTranscript_eq cut
    (start a) (start b) t t false hSide
    (absolute_rejects_diagonal M hDecides _ t (hReject a) (hClock a))
    (absolute_rejects_diagonal M hDecides _ t (hReject b) (hClock b)) hTrace
  have hSplice : M.spliceConfig cut (start a) (start b) =
      M.absoluteStart (left a ++ middle ++ right b) :=
    splice_diagonal_start M left right middle B k hLeft hPositive a b hk
  rw [hSplice, M.absoluteRun_start_state] at hMixedReject
  obtain ⟨_, hMixedAccept⟩ := (hDecides _).mp (hAccept a b hNe)
  cases M.halt_result_unique _ hMixedReject hMixedAccept

/-- Rejecting diagonal inputs with accepting mixed halves require distinct transcripts
at each cut of the common middle word. -/
theorem separated_word_crossing_clock_lower_bound {I : Type} [Fintype I]
    (M : Machine Bool) (hDecides : M.Decides CNFSAT) (left right : I → BinaryWord)
    (middle : BinaryWord) (B t ℓ : Nat) (hLeft : ∀ a, (left a).length = B) (hPositive : 0 < B)
    (hReject : ∀ a, left a ++ middle ++ right a ∉ CNFSAT)
    (hAccept : ∀ a b, a ≠ b → left a ++ middle ++ right b ∈ CNFSAT)
    (hCount : 2 * (Nat.card M.State + 3) ^ ℓ ≤ Fintype.card I)
    (hClock : ∀ a, M.HaltsWithin (left a ++ middle ++ right a) t) :
    middle.length * ℓ ≤ 2 * t := by
  classical
  let _ : Finite M.State := M.stateFinite
  let _ : Fintype M.State := Fintype.ofFinite M.State
  let cut (j : Fin middle.length) : Int := ((B + j.val : Nat) : Int)
  have hCut : Function.Injective cut := by
    intro i j h
    apply Fin.ext
    dsimp [cut] at h
    omega
  let word (a : I) := left a ++ middle ++ right a
  let transcript (a : I) (j : Fin middle.length) :=
    M.crossingTranscript (cut j) t (M.absoluteStart (word a))
  have hInjective (j : Fin middle.length) : Function.Injective (fun a ↦ transcript a j) :=
    diagonal_transcripts_injective M hDecides left right middle B t j.val hLeft hPositive
      hReject hAccept j.isLt.le hClock
  have hStates : Fintype.card (M.State ⊕ Bool) + 1 = Nat.card M.State + 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_bool]
  obtain ⟨a, hRow⟩ := Crossing.exists_row_large_transcript_sum transcript ℓ hInjective (by
    rwa [hStates])
  rw [Fintype.card_fin] at hRow
  exact hRow.trans (Nat.mul_le_mul_left 2
    (M.sum_crossingTranscript_length_le cut hCut t (M.absoluteStart (word a))))

/-- Use the shared block of `p` tautological clauses as the middle word. -/
theorem separated_crossing_clock_lower_bound {I : Type} [Fintype I]
    (M : Machine Bool) (hDecides : M.Decides CNFSAT) (left right : I → BinaryWord)
    (B p t ℓ : Nat) (hLeft : ∀ a, (left a).length = B) (hPositive : 0 < B)
    (hReject : ∀ a, left a ++ paddingBlock p ++ right a ∉ CNFSAT)
    (hAccept : ∀ a b, a ≠ b → left a ++ paddingBlock p ++ right b ∈ CNFSAT)
    (hCount : 2 * (Nat.card M.State + 3) ^ ℓ ≤ Fintype.card I)
    (hClock : ∀ a, M.HaltsWithin (left a ++ paddingBlock p ++ right a) t) :
    8 * p * ℓ ≤ 2 * t := by
  simpa only [length_paddingBlock] using separated_word_crossing_clock_lower_bound
    M hDecides left right (paddingBlock p) B t ℓ hLeft hPositive hReject hAccept hCount hClock

/-- Every common clock for these equal-table inputs pays for the crossing
sequences at all `8 * p` cuts in their shared padding. -/
theorem crossing_clock_lower_bound (M : Machine Bool) (hDecides : M.Decides CNFSAT)
    (r p t ℓ : Nat) (hCount : 2 * (Nat.card M.State + 3) ^ ℓ ≤ 2 ^ (2 ^ r))
    (hClock : ∀ a : Table r, M.HaltsWithin (crossingWord r p a a) t) :
    8 * p * ℓ ≤ 2 * t := by
  refine separated_crossing_clock_lower_bound M hDecides (leftBlock r) (rightBlock r)
    (blockWidth r) p t ℓ (length_leftBlock r) (blockWidth_pos r)
    (crossingWord_diagonal_not_mem_CNFSAT r p)
    (fun a b ↦ (crossingWord_mem_CNFSAT_iff_ne r p a b).mpr) ?_ hClock
  simpa [Table, Address] using hCount

/-- At the explicit lengths `10 * blockWidth r + 1`, every uniform bound on
the rejecting family has order at least squared length divided by log-squared
length, up to the displayed additive term and fixed machine factor. -/
theorem cnfsat_square_length_le_crossing_time (M : Machine Bool) (hDecides : M.Decides CNFSAT)
    (r t : Nat) (hClock : ∀ a : Table r,
      M.HaltsWithin (crossingWord r (blockWidth r) a a) t) :
    let n := 10 * blockWidth r + 1
    n ^ 2 ≤ 121 * (2 + (Nat.log2 n + 1) * (Nat.log2 n + 3)) *
      (Nat.card M.State + 3) * (t + n) := by
  let q := Nat.card M.State + 3
  have hCount := twice_pow_div_le_pow_two (2 ^ r) q (Nat.two_pow_pos r)
  exact square_length_le_crossing_time r (blockWidth r) q t
    (pow_le_blockWidth r) (blockWidth_le r) (by dsimp [q]; omega)
    (crossing_clock_lower_bound M hDecides r (blockWidth r) t _ hCount hClock)

/-- Every proposed linear clock fails on at least one encoded CNF word. -/
theorem cnfsat_no_linear_clock (M : Machine Bool) (hDecides : M.Decides CNFSAT) (C : Nat) :
    ∃ word, ¬ M.HaltsWithin word (C * (word.length + 1)) := by
  by_contra! hTime
  let q := Nat.card M.State + 3
  let ℓ := 4 * (C + 1)
  let r := q * ℓ + 1
  let B := blockWidth r
  let t := C * (2 * B + 8 * B + 1 + 1)
  have hq : 0 < q := by dsimp [q]; omega
  have hSize : r < 2 ^ r := Nat.lt_two_pow_self
  have hThreshold : ℓ ≤ (2 ^ r - 1) / q := by
    apply (Nat.le_div_iff_mul_le hq).mpr
    rw [Nat.mul_comm ℓ q]
    change q * ℓ + 1 < 2 ^ r at hSize
    omega
  have hCount : 2 * q ^ ℓ ≤ 2 ^ (2 ^ r) :=
    (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right hq hThreshold)).trans
      (twice_pow_div_le_pow_two (2 ^ r) q (Nat.two_pow_pos r))
  have hClock (a : Table r) : M.HaltsWithin (crossingWord r B a a) t := by
    simpa only [t, B, length_crossingWord] using hTime (crossingWord r B a a)
  have hBound := crossing_clock_lower_bound M hDecides r B t ℓ hCount hClock
  have hB : 0 < B := blockWidth_pos r
  have hT : t ≤ C * (12 * B) := Nat.mul_le_mul_left C (by omega)
  have hTwice : 2 * t ≤ (24 * C) * B := by
    calc
      2 * t ≤ 2 * (C * (12 * B)) := Nat.mul_le_mul_left 2 hT
      _ = (2 * 12) * C * B := by ac_rfl
  have hStrict : (24 * C) * B < (8 * ℓ) * B :=
    Nat.mul_lt_mul_of_pos_right (by dsimp [ℓ]; omega) hB
  have hSwap : (8 * ℓ) * B = 8 * B * ℓ := by ac_rfl
  exact (Nat.not_lt_of_ge hBound) (hTwice.trans_lt (hStrict.trans_eq hSwap))

end PvsNP.SATCrossing
