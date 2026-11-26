module

public import PvsNP.TuringMachine.TrackCall.Core

import Init.Data.List.Zip

/-! # Scratch and protected tape tracks

The scratch view follows the called machine's tape. The protected view
records its original tape coordinates and marks the initial head position.
-/

public section

namespace PvsNP.TrackCall

open Turing

variable {α : Type} (D : Machine α) (ρ : Type) [Finite ρ] [Inhabited ρ]

private def scratchMap :
    @PointedMap (machine D ρ).Symbol D.Symbol (machine D ρ).tapeInhabited D.tapeInhabited :=
  @PointedMap.mk _ _ (machine D ρ).tapeInhabited D.tapeInhabited Prod.fst rfl

/-- Read the scratch track as a tape over the called machine's alphabet. -/
def scratch (tape : (machine D ρ).Tape) : D.Tape :=
  @Tape.map _ _ (machine D ρ).tapeInhabited D.tapeInhabited (scratchMap D ρ) tape

theorem scratch_head (tape : (machine D ρ).Tape) :
    @Tape.head _ D.tapeInhabited (scratch D ρ tape) =
      (@Tape.head _ (machine D ρ).tapeInhabited tape).1 := by
  unfold scratch
  rfl

theorem scratch_nth (tape : (machine D ρ).Tape) (i : Int) :
    @Tape.nth _ D.tapeInhabited (scratch D ρ tape) i =
      (@Tape.nth _ (machine D ρ).tapeInhabited tape i).1 := by
  let _ := (machine D ρ).tapeInhabited
  let _ := D.tapeInhabited
  cases i with
  | ofNat n =>
    cases n with
    | zero => exact scratch_head D ρ tape
    | succ n =>
      change ((tape.right.map (scratchMap D ρ)).nth n) = (tape.right.nth n).1
      rw [ListBlank.nth_map]
      rfl
  | negSucc n =>
    change ((tape.left.map (scratchMap D ρ)).nth n) = (tape.left.nth n).1
    rw [ListBlank.nth_map]
    rfl

theorem scratch_write_move (tape : (machine D ρ).Tape) (b : D.Symbol) (dir : Dir) :
    scratch D ρ
      (@Tape.move _ (machine D ρ).tapeInhabited dir
        (@Tape.write _ (machine D ρ).tapeInhabited
          (b, (@Tape.head _ (machine D ρ).tapeInhabited tape).2) tape)) =
      @Tape.move _ D.tapeInhabited dir (@Tape.write _ D.tapeInhabited b (scratch D ρ tape)) := by
  simp only [scratch,
    @Tape.map_move _ _ (machine D ρ).tapeInhabited D.tapeInhabited,
    @Tape.map_write _ _ (machine D ρ).tapeInhabited D.tapeInhabited]
  rfl

/-- At offset `pos`, read the original protected tape and mark its origin. -/
@[expose] def FrameAt (tape : (machine D ρ).Tape) (saved : Tape ρ) (pos : Int) : Prop :=
  ∀ j : Int, (@Tape.nth _ (machine D ρ).tapeInhabited tape j).2 =
    (saved.nth (pos + j), decide (pos + j = 0))

theorem frameAt_head {tape : (machine D ρ).Tape} {saved : Tape ρ} {pos : Int}
    (h : FrameAt D ρ tape saved pos) :
    (@Tape.head _ (machine D ρ).tapeInhabited tape).2 =
      (saved.nth pos, decide (pos = 0)) := by
  simpa only [Tape.nth_zero, Int.add_zero] using h 0

/-- A physical move shifts the relative coordinate of every tape cell. -/
theorem move_nth_delta {Γ : Type} [Inhabited Γ]
    (tape : Tape Γ) (dir : Dir) (j : Int) :
    (tape.move dir).nth j = tape.nth (j + delta dir) := by
  cases dir with
  | left => simpa only [delta, Int.sub_eq_add_neg] using Tape.move_left_nth tape j
  | right => exact Tape.move_right_nth tape j

theorem frameAt_move {tape : (machine D ρ).Tape} {saved : Tape ρ} {pos : Int}
    (h : FrameAt D ρ tape saved pos) (dir : Dir) :
    FrameAt D ρ (@Tape.move _ (machine D ρ).tapeInhabited dir tape) saved
      (pos + delta dir) := by
  intro j
  rw [@move_nth_delta _ (machine D ρ).tapeInhabited tape dir, h (j + delta dir)]
  have hIndex : pos + (j + delta dir) = pos + delta dir + j := by omega
  rw [hIndex]

theorem frameAt_write_move {tape : (machine D ρ).Tape} {saved : Tape ρ} {pos : Int}
    (h : FrameAt D ρ tape saved pos) (b : D.Symbol) (dir : Dir) :
    FrameAt D ρ
      (@Tape.move _ (machine D ρ).tapeInhabited dir
        (@Tape.write _ (machine D ρ).tapeInhabited
          (b, (@Tape.head _ (machine D ρ).tapeInhabited tape).2) tape))
      saved (pos + delta dir) := by
  apply frameAt_move D ρ _ dir
  intro j
  by_cases hZero : j = 0
  · subst j
    exact h 0
  · simp only [@Tape.write_nth _ (machine D ρ).tapeInhabited, hZero, ite_false]
    exact h j

private def pairCells {Γ ρ : Type} [Inhabited Γ] [Inhabited ρ]
    (xs : List Γ) (ys : List ρ) : List (Γ × ρ × Bool) :=
  xs.zipWithAll (fun x y ↦ (x.getD default, y.getD default, false)) ys

private theorem nth_mk_pairCells {Γ ρ : Type} [Inhabited Γ] [Inhabited ρ]
    (xs : List Γ) (ys : List ρ) (n : Nat) :
    (ListBlank.mk (pairCells xs ys)).nth n = ((ListBlank.mk xs).nth n, (ListBlank.mk ys).nth n,
      false) := by
  simp only [pairCells, ListBlank.nth_mk, ← List.getD_default_eq_getI,
    List.getD_eq_getElem?_getD, List.getElem?_zipWithAll]
  cases xs[n]? <;> cases ys[n]? <;> rfl

/-- Pair half tapes coordinatewise, using blanks beyond either finite list. -/
private def pairTracks {Γ ρ : Type} [Inhabited Γ] [Inhabited ρ]
    (xs : ListBlank Γ) (ys : ListBlank ρ) : ListBlank (Γ × ρ × Bool) :=
  Quotient.liftOn₂ xs ys (fun xs ys ↦ ListBlank.mk (pairCells xs ys)) (by
    intro xs ys xs' ys' hX hY
    apply ListBlank.ext
    intro n
    have hx : ListBlank.mk xs = ListBlank.mk xs' := Quotient.sound hX
    have hy : ListBlank.mk ys = ListBlank.mk ys' := Quotient.sound hY
    rw [nth_mk_pairCells, nth_mk_pairCells, hx, hy])

private theorem nth_pairTracks {Γ ρ : Type} [Inhabited Γ] [Inhabited ρ]
    (xs : ListBlank Γ) (ys : ListBlank ρ) (n : Nat) :
    (pairTracks xs ys).nth n = (xs.nth n, ys.nth n, false) :=
  xs.induction_on fun xs ↦ ys.induction_on fun ys ↦ nth_mk_pairCells xs ys n

private theorem map_pairTracks_fst {Γ ρ : Type} [Inhabited Γ] [Inhabited ρ]
    (xs : ListBlank Γ) (ys : ListBlank ρ) :
    (pairTracks xs ys).map (⟨Prod.fst, rfl⟩ : PointedMap (Γ × ρ × Bool) Γ) = xs := by
  apply ListBlank.ext
  intro n
  rw [ListBlank.nth_map, nth_pairTracks]

/-- Lay the call input on the scratch track with both tapes centered at the origin. -/
def prepareTape (x : List α) (saved : Tape ρ) : (machine D ρ).Tape :=
  let work := (D.start x).tape
  letI := D.tapeInhabited
  ⟨(work.head, saved.head, true), pairTracks work.left saved.left,
    pairTracks work.right saved.right⟩

theorem scratch_prepareTape (x : List α) (saved : Tape ρ) :
    scratch D ρ (prepareTape D ρ x saved) = (D.start x).tape := by
  let work := (D.start x).tape
  let _ := D.tapeInhabited
  change (⟨work.head, (pairTracks work.left saved.left).map ⟨Prod.fst, rfl⟩,
    (pairTracks work.right saved.right).map ⟨Prod.fst, rfl⟩⟩ : D.Tape) = work
  rw [map_pairTracks_fst, map_pairTracks_fst]

theorem frameAt_prepareTape (x : List α) (saved : Tape ρ) :
    FrameAt D ρ (prepareTape D ρ x saved) saved 0 := by
  let work := (D.start x).tape
  let _ := D.tapeInhabited
  intro j
  simp only [Int.zero_add]
  cases j with
  | ofNat k =>
    cases k with
    | zero => rfl
    | succ k =>
      change ((pairTracks work.right saved.right).nth k).2 = (saved.right.nth k, false)
      exact congrArg Prod.snd (nth_pairTracks work.right saved.right k)
  | negSucc k =>
    change ((pairTracks work.left saved.left).nth k).2 = (saved.left.nth k, false)
    exact congrArg Prod.snd (nth_pairTracks work.left saved.left k)

end PvsNP.TrackCall
