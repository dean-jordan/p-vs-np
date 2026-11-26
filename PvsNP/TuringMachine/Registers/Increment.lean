module

public import PvsNP.TuringMachine.Registers.Alphabet
public import PvsNP.TuringMachine.Sweeps

/-! # Counted unary register increment

Starting at the home sentinel, the machine scans the selected track across
its consecutive true cells, sets the first false cell, and returns to home.
The first false position may be the blank immediately after the current
register area. In that case the machine adds a cell with all other tracks
false. The return uses a two-transition bounce at home.
-/

@[expose] public section

namespace PvsNP.RegisterMachine

open Turing

variable {R Q : Type} [DecidableEq R]

/-- Transition rules for an increment instruction in a finite host program. -/
structure IncrementRules (delta : Q → Symbol R → (Q ⊕ Bool) × Symbol R × Dir)
    (lane : R) where
  entry : Q
  scan : Q
  rewind : Q
  land : Q
  next : Q
  enter_home : delta entry .home = (.inl scan, .home, .right)
  scan_true : ∀ cell, cell lane = true →
    delta scan (.track cell) = (.inl scan, .track cell, .right)
  scan_false : ∀ cell, cell lane = false →
    delta scan (.track cell) = (.inl rewind, .track (setTrack cell lane true), .left)
  scan_blank : delta scan .blank =
    (.inl rewind, .track (setTrack (fun _ ↦ false) lane true), .left)
  rewind_track : ∀ cell, delta rewind (.track cell) = (.inl rewind, .track cell, .left)
  rewind_home : delta rewind .home = (.inl land, .home, .right)
  land_track : ∀ cell, delta land (.track cell) = (.inl next, .track cell, .left)

variable [Finite R] [Finite Q]
variable (initial : Q) {delta : Q → Symbol R → (Q ⊕ Bool) × Symbol R × Dir} {lane : R}

local notation "M" => host initial delta

private abbrev cfg (q : Q) (left right : List (Symbol R)) : (M).Config :=
  ⟨.inl q, (M).tapeFromLists left right⟩

private abbrev leftOfCut (q : Q) (left right : List (Symbol R)) : (M).Config :=
  ⟨.inl q, @Tape.move _ (M).tapeInhabited .left ((M).tapeFromLists left right)⟩

omit [DecidableEq R] in
private theorem run_one (C : (M).Config) : (M).run 1 C = (M).tick C := rfl

private theorem run_land (rules : IncrementRules delta lane) (left : List (Symbol R))
    (tracks : List (R → Bool)) (nonempty : tracks ≠ []) :
    (M).run 2 (cfg initial rules.rewind left (.home :: trackTape tracks)) =
      cfg initial rules.next left (.home :: trackTape tracks) := by
  cases tracks with
  | nil => exact (nonempty rfl).elim
  | cons first rest =>
    have h := (M).tick_tapeFromLists_cons rules.rewind left
      (.track first :: trackTape rest) .home rules.rewind_home
    have hRight : (M).tick (cfg initial rules.rewind left (.home :: trackTape (first :: rest))) =
        cfg initial rules.land (.home :: left) (trackTape (first :: rest)) := by
      exact h.trans (congrArg (fun tape ↦ (⟨.inl rules.land, tape⟩ : (M).Config))
        ((M).move_tapeFromLists_right_cons left (.track first :: trackTape rest) .home))
    have hLeft : (M).tick (cfg initial rules.land (.home :: left) (trackTape (first :: rest))) =
        cfg initial rules.next left (.home :: trackTape (first :: rest)) := by
      have step := (M).tick_tapeFromLists_cons rules.land (.home :: left) (trackTape rest)
        (.track first) (rules.land_track first)
      exact step.trans (congrArg (fun tape ↦ (⟨.inl rules.next, tape⟩ : (M).Config))
        ((M).move_tapeFromLists_left_cons left (.track first :: trackTape rest) .home))
    rw [show (2 : Nat) = 1 + 1 by rfl, Machine.run_add,
      run_one initial (cfg initial rules.rewind left (.home :: trackTape (first :: rest))), hRight]
    exact (run_one initial _).trans hLeft

private theorem run_increment_split (rules : IncrementRules delta lane)
    (left suffix : List (Symbol R)) (before : List (R → Bool)) (written : R → Bool)
    (after : List (R → Bool)) (hBefore : ∀ cell ∈ before, cell lane = true)
    (hWrite : (M).tick (cfg initial rules.scan
        ((trackTape before).reverse ++ .home :: left) suffix) =
      leftOfCut initial rules.rewind ((trackTape before).reverse ++ .home :: left)
        (.track written :: trackTape after)) :
    (M).run (2 * before.length + 4)
        (cfg initial rules.entry left (.home :: (trackTape before ++ suffix))) =
      cfg initial rules.next left (.home :: trackTape (before ++ written :: after)) := by
  let crossed := trackTape before
  let rest := .track written :: trackTape after
  have rightRule : ∀ a ∈ crossed, delta rules.scan a = (.inl rules.scan, a, .right) := by
    intro a ha
    obtain ⟨cell, hCell, rfl⟩ := List.mem_map.mp ha
    exact rules.scan_true cell (hBefore cell hCell)
  have leftRule : ∀ a ∈ crossed.reverse,
      delta rules.rewind a = (.inl rules.rewind, a, .left) := by
    intro a ha
    obtain ⟨cell, _, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp ha)
    exact rules.rewind_track cell
  have hEnter : (M).tick (cfg initial rules.entry left (.home :: (crossed ++ suffix))) =
      cfg initial rules.scan (.home :: left) (crossed ++ suffix) := by
    have step := (M).tick_tapeFromLists_cons rules.entry left (crossed ++ suffix) .home
      rules.enter_home
    exact step.trans (congrArg (fun tape ↦ (⟨.inl rules.scan, tape⟩ : (M).Config))
      ((M).move_tapeFromLists_right_cons left (crossed ++ suffix) .home))
  have hRewind : (M).run crossed.length
      (leftOfCut initial rules.rewind (crossed.reverse ++ .home :: left) rest) =
      cfg initial rules.rewind left (.home :: trackTape (before ++ written :: after)) := by
    have h := (M).run_sweep_left rules.rewind crossed.reverse (.home :: left) rest leftRule
    rw [List.length_reverse, List.reverse_reverse, Machine.move_tapeFromLists_left_cons] at h
    simpa only [crossed, rest, trackTape, List.map_append, List.map_cons] using h
  have hLen : crossed.length = before.length := List.length_map ..
  have hTime : 2 * before.length + 4 = 1 + crossed.length + 1 + crossed.length + 2 := by omega
  rw [hTime, Machine.run_add, Machine.run_add, Machine.run_add, Machine.run_add]
  rw [run_one initial (cfg initial rules.entry left (.home :: (crossed ++ suffix))), hEnter,
    (M).run_sweep_right rules.scan crossed (.home :: left) suffix rightRule]
  rw [run_one, hWrite, hRewind]
  exact run_land initial rules left _ (by simp)

/-- Incrementing into an existing false cell preserves every other bit on the tape. -/
theorem run_increment_cell (rules : IncrementRules delta lane) (left : List (Symbol R))
    (before : List (R → Bool)) (cell : R → Bool) (after : List (R → Bool))
    (hBefore : ∀ c ∈ before, c lane = true) (hCell : cell lane = false) :
    (M).run (2 * before.length + 4)
      ⟨.inl rules.entry, (M).tapeFromLists left
        (.home :: trackTape (before ++ cell :: after))⟩ =
      ⟨.inl rules.next, (M).tapeFromLists left
        (.home :: trackTape (before ++ setTrack cell lane true :: after))⟩ := by
  have hWrite := (M).tick_tapeFromLists_cons rules.scan
    ((trackTape before).reverse ++ .home :: left) (trackTape after) (.track cell)
    (rules.scan_false cell hCell)
  simpa only [trackTape, List.map_append, List.map_cons] using
    run_increment_split initial rules left (.track cell :: trackTape after) before
      (setTrack cell lane true) after hBefore hWrite

/-- Incrementing at the first blank appends a fresh cell with only the selected track true. -/
theorem run_increment_blank (rules : IncrementRules delta lane) (left : List (Symbol R))
    (before : List (R → Bool)) (hBefore : ∀ c ∈ before, c lane = true) :
    (M).run (2 * before.length + 4)
      ⟨.inl rules.entry, (M).tapeFromLists left (.home :: trackTape before)⟩ =
      ⟨.inl rules.next, (M).tapeFromLists left
        (.home :: trackTape (before ++ [setTrack (fun _ ↦ false) lane true]))⟩ := by
  have hWrite := (M).tick_tapeFromLists_nil rules.scan ((trackTape before).reverse ++ .home :: left)
    rules.scan_blank
  simpa only [List.append_nil] using
    run_increment_split initial rules left [] before (setTrack (fun _ ↦ false) lane true) []
      hBefore hWrite

end PvsNP.RegisterMachine
