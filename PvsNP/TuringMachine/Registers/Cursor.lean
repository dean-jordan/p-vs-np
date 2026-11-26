module

public import PvsNP.TuringMachine.Registers.Alphabet

/-! # Reading the input backwards using a marked cursor

The cursor marks the most recently read input bit. Advancing restores that
bit and moves the mark one cell left, or reports the input sentinel. Every
operation returns the head to the register boundary.
-/

@[expose] public section

namespace PvsNP.RegisterMachine

open Turing

variable {R Q : Type} [Finite R] [Finite Q]

/-- Read the first or next input bit from the register boundary, carrying the result in
finite control. `none` means that the input sentinel was reached. -/
structure CursorRules (delta : Q → Symbol R → (Q ⊕ Bool) × Symbol R × Dir) where
  first : Q
  advance : Q
  seek : Q
  pick : Q
  rewind : Option Bool → Q
  land : Option Bool → Q
  next : Option Bool → Q
  first_home : delta first .home = (.inl pick, .home, .left)
  advance_home : delta advance .home = (.inl seek, .home, .left)
  seek_bit : ∀ b, delta seek (.bit b) = (.inl seek, .bit b, .left)
  seek_mark : ∀ b, delta seek (.inputMark b) = (.inl pick, .bit b, .left)
  pick_bit : ∀ b, delta pick (.bit b) = (.inl (rewind (some b)), .inputMark b, .right)
  pick_start : delta pick .start = (.inl (rewind none), .start, .right)
  rewind_bit : ∀ result b, delta (rewind result) (.bit b) = (.inl (rewind result), .bit b, .right)
  rewind_home : ∀ result, delta (rewind result) .home = (.inl (land result), .home, .left)
  land_bit : ∀ result b, delta (land result) (.bit b) = (.inl (next result), .bit b, .right)
  land_mark : ∀ b, delta (land (some b)) (.inputMark b) =
    (.inl (next (some b)), .inputMark b, .right)
  land_start : delta (land none) .start = (.inl (next none), .start, .right)

variable {delta : Q → Symbol R → (Q ⊕ Bool) × Symbol R × Dir}
  (initial : Q) (rules : CursorRules delta)

local notation "M" => host initial delta

private abbrev cfg (q : Q) (left right : List (Symbol R)) : (M).Config :=
  ⟨.inl q, (M).tapeFromLists left right⟩

private theorem run_land (result : Option Bool) (left right : List (Symbol R)) (a : Symbol R)
    (ha : delta (rules.land result) a = (.inl (rules.next result), a, .right)) :
    (M).run 2 (cfg initial (rules.rewind result) (a :: left) (.home :: right)) =
      cfg initial (rules.next result) (a :: left) (.home :: right) := by
  rw [(M).run_succ, (M).tick_tapeFromLists_cons _ _ _ _ (rules.rewind_home result),
    (M).move_tapeFromLists_left_cons, (M).run_succ,
    (M).tick_tapeFromLists_cons _ _ _ _ ha, (M).move_tapeFromLists_right_cons, (M).run_zero]

private theorem run_pick (near : BinaryWord) (far right : List (Symbol R))
    (a marked : Symbol R) (result : Option Bool)
    (hPick : delta rules.pick a = (.inl (rules.rewind result), marked, .right))
    (hLand : delta (rules.land result) marked = (.inl (rules.next result), marked, .right)) :
    (M).run (near.length + 3)
      (cfg initial rules.pick far (a :: ((bits near).reverse ++ .home :: right))) =
      cfg initial (rules.next result) (bits near ++ marked :: far) (.home :: right) := by
  have sweepRule (s : Symbol R) (hs : s ∈ (bits near).reverse) :
      delta (rules.rewind result) s = (.inl (rules.rewind result), s, .right) := by
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hs)
    exact rules.rewind_bit result b
  have sweep := (M).run_sweep_right (rules.rewind result) (bits near).reverse
    (marked :: far) (.home :: right) sweepRule
  simp only [List.length_reverse, List.length_map, List.reverse_reverse] at sweep
  rw [show near.length + 3 = (near.length + 2) + 1 by omega, (M).run_succ,
    (M).tick_tapeFromLists_cons _ _ _ _ hPick, (M).move_tapeFromLists_right_cons,
    (M).run_add, sweep]
  cases near with
  | nil => exact run_land initial rules result far right marked hLand
  | cons b near =>
    exact run_land initial rules result (bits near ++ marked :: far) right
      (.bit b) (rules.land_bit result b)

/-- Reading the first bit from an unmarked input takes four moves. -/
theorem run_cursor_first_bit (near : BinaryWord) (b : Bool) (far right : List (Symbol R)) :
    (M).run 4
      ⟨.inl rules.first, (M).tapeFromLists (.bit b :: (bits near ++ far)) (.home :: right)⟩ =
      ⟨.inl (rules.next (some b)),
        (M).tapeFromLists (.inputMark b :: (bits near ++ far)) (.home :: right)⟩ := by
  rw [(M).run_succ, (M).tick_tapeFromLists_cons _ _ _ _ rules.first_home,
    (M).move_tapeFromLists_left_cons]
  exact run_pick initial rules [] (bits near ++ far) right (.bit b) (.inputMark b) (some b)
    (rules.pick_bit b) (rules.land_mark b)

/-- The same first-read instruction returns `none` for empty input. -/
theorem run_cursor_first_empty (far right : List (Symbol R)) :
    (M).run 4 ⟨.inl rules.first, (M).tapeFromLists (.start :: far) (.home :: right)⟩ =
      ⟨.inl (rules.next none), (M).tapeFromLists (.start :: far) (.home :: right)⟩ := by
  rw [(M).run_succ, (M).tick_tapeFromLists_cons _ _ _ _ rules.first_home,
    (M).move_tapeFromLists_left_cons]
  exact run_pick initial rules [] far right .start .start none rules.pick_start rules.land_start

private theorem run_advance (near : BinaryWord) (prior : Bool) (far right : List (Symbol R))
    (a marked : Symbol R) (result : Option Bool)
    (hPick : delta rules.pick a = (.inl (rules.rewind result), marked, .right))
    (hLand : delta (rules.land result) marked = (.inl (rules.next result), marked, .right)) :
    (M).run (2 * near.length + 6)
      (cfg initial rules.advance (bits near ++ .inputMark prior :: a :: far) (.home :: right)) =
      cfg initial (rules.next result) (bits near ++ .bit prior :: marked :: far)
        (.home :: right) := by
  have sweepRule (s : Symbol R) (hs : s ∈ bits near) :
      delta rules.seek s = (.inl rules.seek, s, .left) := by
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hs
    exact rules.seek_bit b
  have sweep := (M).run_sweep_left rules.seek (bits near) (.inputMark prior :: a :: far)
    (.home :: right) sweepRule
  simp only [List.length_map] at sweep
  have advance := run_pick initial rules (near ++ [prior]) far right a marked result hPick hLand
  simp only [List.length_append, List.length_singleton, List.map_append, List.map_cons,
    List.map_nil, List.reverse_append, List.reverse_singleton, List.singleton_append,
    List.append_assoc] at advance
  rw [show 2 * near.length + 6 = (near.length + (near.length + 1 + 3 + 1)) + 1 by omega,
    (M).run_succ, (M).tick_tapeFromLists_cons _ _ _ _ rules.advance_home,
    (M).run_add, sweep, (M).move_tapeFromLists_left_cons, (M).run_succ,
    (M).tick_tapeFromLists_cons _ _ _ _ (rules.seek_mark prior),
    (M).move_tapeFromLists_left_cons]
  exact advance

/-- Advance the input mark one bit left, preserving the underlying word. -/
theorem run_cursor_next_bit (near : BinaryWord) (prior b : Bool) (far right : List (Symbol R)) :
    (M).run (2 * near.length + 6)
      ⟨.inl rules.advance,
        (M).tapeFromLists (bits near ++ .inputMark prior :: .bit b :: far) (.home :: right)⟩ =
      ⟨.inl (rules.next (some b)),
        (M).tapeFromLists (bits near ++ .bit prior :: .inputMark b :: far) (.home :: right)⟩ :=
  run_advance initial rules near prior far right (.bit b) (.inputMark b) (some b)
    (rules.pick_bit b) (rules.land_mark b)

/-- Advancing past the final bit removes the mark and reports the sentinel. -/
theorem run_cursor_next_end (near : BinaryWord) (prior : Bool) (far right : List (Symbol R)) :
    (M).run (2 * near.length + 6)
      ⟨.inl rules.advance,
        (M).tapeFromLists (bits near ++ .inputMark prior :: .start :: far)
          (.home :: right)⟩ =
      ⟨.inl (rules.next none),
        (M).tapeFromLists (bits near ++ .bit prior :: .start :: far) (.home :: right)⟩ :=
  run_advance initial rules near prior far right .start .start none
    rules.pick_start rules.land_start

end PvsNP.RegisterMachine
