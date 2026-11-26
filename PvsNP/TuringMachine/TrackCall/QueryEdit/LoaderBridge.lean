module

public import PvsNP.TuringMachine.TrackCall.QueryEdit.Core
public import PvsNP.TuringMachine.TrackCall.Loader.Load

import PvsNP.TuringMachine.OutputBound

/-! # Load an edited query into the scratch track -/

public section

namespace PvsNP.TrackCall.QueryEdit

open Turing

variable {α : Type} (D : Machine α) (ρ : Type) [Finite ρ] [Inhabited ρ]

private def savedMap :
    @PointedMap (machine D (Cell ρ)).Symbol (Cell ρ)
      (machine D (Cell ρ)).tapeInhabited inferInstance :=
  @PointedMap.mk _ _ (machine D (Cell ρ)).tapeInhabited inferInstance
    (fun cell ↦ cell.2.1) rfl

/-- The tape of protected cells, using the same coordinates as the whole tape. -/
def savedTrack (tape : (machine D (Cell ρ)).Tape) : Tape (Cell ρ) :=
  @Tape.map _ _ (machine D (Cell ρ)).tapeInhabited inferInstance (savedMap D ρ) tape

theorem savedTrack_nth (tape : (machine D (Cell ρ)).Tape) (i : Int) :
    (savedTrack D ρ tape).nth i = (@Tape.nth _ (machine D (Cell ρ)).tapeInhabited tape i).2.1 := by
  let _ := (machine D (Cell ρ)).tapeInhabited
  cases i with
  | ofNat n =>
    cases n with
    | zero => rfl
    | succ n =>
      change (tape.right.map (savedMap D ρ)).nth n = (tape.right.nth n).2.1
      rw [ListBlank.nth_map]
      rfl
  | negSucc n =>
    change (tape.left.map (savedMap D ρ)).nth n = (tape.left.nth n).2.1
    rw [ListBlank.nth_map]
    rfl

private theorem tracksAt_nth_origin {tape : (machine D (Cell ρ)).Tape}
    {work : Int → D.Symbol} {data : Int → Cell ρ} (h : TracksAt D ρ tape 0 work data) (i : Int) :
    @Tape.nth _ (machine D (Cell ρ)).tapeInhabited tape i = (work i, data i, decide (i = 0)) := by
  simpa only [Int.sub_zero] using h i

theorem tracksAt_savedTrack {tape : (machine D (Cell ρ)).Tape}
    {work : Int → D.Symbol} {data : Int → Cell ρ} (h : TracksAt D ρ tape 0 work data) (i : Int) :
    (savedTrack D ρ tape).nth i = data i := by
  rw [savedTrack_nth, tracksAt_nth_origin D ρ h i]

theorem tracksAt_frameOrigin {tape : (machine D (Cell ρ)).Tape}
    {work : Int → D.Symbol} {data : Int → Cell ρ} (h : TracksAt D ρ tape 0 work data) :
    FrameAt D (Cell ρ) tape (savedTrack D ρ tape) 0 := by
  intro i
  rw [Int.zero_add, tracksAt_savedTrack D ρ h i, tracksAt_nth_origin D ρ h i]

/-- Read the work symbols in absolute coordinates when the head is at the origin. -/
@[expose] def workAtOrigin (tape : (machine D (Cell ρ)).Tape) (i : Int) : D.Symbol :=
  (@Tape.nth _ (machine D (Cell ρ)).tapeInhabited tape i).1

theorem tracksAt_of_frameOrigin {tape : (machine D (Cell ρ)).Tape}
    {saved : Tape (Cell ρ)} {data : Int → Cell ρ}
    (hFrame : FrameAt D (Cell ρ) tape saved 0) (hData : ∀ i : Int, saved.nth i = data i) :
    TracksAt D ρ tape 0 (workAtOrigin D ρ tape) data := by
  intro i
  rw [Int.sub_zero]
  apply Prod.ext
  · rfl
  · simpa only [Int.zero_add, hData i] using hFrame i

theorem tracksAt_blankOutside_iff {tape : (machine D (Cell ρ)).Tape}
    {work : Int → D.Symbol} {data : Int → Cell ρ} (h : TracksAt D ρ tape 0 work data) (L R : Nat) :
    Loader.BlankOutside D (Cell ρ) tape L R ↔
      ∀ i : Int, i < -(L : Int) ∨ (R : Int) < i → work i = D.blank := by
  unfold Loader.BlankOutside
  simp only [tracksAt_nth_origin D ρ h]

variable {ρ}

/-- The loader reads boundary marks from the payload and input symbols from the query bits. -/
@[expose] def queryLayout (D : Machine Bool) (left right : ρ → Bool) :
    Loader.Layout D (Cell ρ) where
  leftEdge cell := left cell.1
  rightEdge cell := right cell.1
  load cell := (bit cell).elim D.blank (fun b ↦ D.input b)

private theorem start_nth_eq_queryBit (D : Machine Bool) (word : List Bool) (i : Int) :
    (if i < 0 then none else word[i.toNat]?).elim D.blank (fun b ↦ D.input b) =
      @Tape.nth _ D.tapeInhabited (D.start word).tape i := by
  let _ := D.tapeInhabited
  cases i with
  | ofNat n =>
    change (if (n : Int) < 0 then none else word[n]?).elim D.blank (fun b ↦ D.input b) =
      (Tape.mk₁ (word.map D.input)).nth (n : Int)
    rw [ite_eq_right (show ¬ (n : Int) < 0 by omega), Machine.mk₁_nth_nat,
      List.getI_eq_getElem?_getD, List.getElem?_map]
    cases word[n]? <;> rfl
  | negSucc n =>
    have hn : Int.negSucc n < 0 := by omega
    rw [ite_eq_left hn]
    exact (Loader.start_nth_eq_blank D word _ (Or.inl hn)).symm

/-- A tape with these marked boundaries and query bits meets the loader's window specification. -/
theorem windowSpec_of_tracksAt (D : Machine Bool) (ρ : Type) [Finite ρ] [Inhabited ρ]
    (left right : ρ → Bool) (L R : Nat) (word : List Bool)
    {tape : (machine D (Cell ρ)).Tape} {work : Int → D.Symbol} {data : Int → Cell ρ}
    (hTracks : TracksAt D ρ tape 0 work data)
    (hBits : ∀ i : Int, bit (data i) = if i < 0 then none else word[i.toNat]?)
    (hLeftMark : ∀ i : Int, left (data i).1 = true ↔ i = -(L : Int))
    (hRightMark : ∀ i : Int, right (data i).1 = decide (i = (R : Int)))
    (hR : 0 < R) :
    Loader.WindowSpec (queryLayout D left right) (savedTrack D ρ tape) (D.start word).tape L R := by
  refine ⟨hR, ?_, ?_, ?_⟩
  · intro i
    rw [tracksAt_savedTrack D ρ hTracks i]
    exact hLeftMark i
  · intro i
    rw [tracksAt_savedTrack D ρ hTracks i]
    exact hRightMark i
  · intro i _ _
    rw [tracksAt_savedTrack D ρ hTracks i]
    change (bit (data i)).elim D.blank (fun b ↦ D.input b) = _
    rw [hBits]
    exact start_nth_eq_queryBit D word i

end PvsNP.TrackCall.QueryEdit
