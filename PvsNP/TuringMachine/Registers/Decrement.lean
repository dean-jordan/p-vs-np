module

public import PvsNP.TuringMachine.Registers.Alphabet
public import PvsNP.TuringMachine.Sweeps

/-! # Counted unary register decrement

At home the machine checks the first cell to select the zero or positive
branch. On the positive branch it scans to the end of the true prefix,
steps back to clear its last cell, and returns to home.
-/

@[expose] public section

namespace PvsNP.RegisterMachine

open Turing

variable {R Q : Type} [DecidableEq R]

/-- Rules for decrementing a register with separate zero and positive successors. -/
structure DecrementRules (delta : Q → Symbol R → (Q ⊕ Bool) × Symbol R × Dir)
    (lane : R) where
  entry : Q
  inspect : Q
  scan : Q
  clear : Q
  rewind : Q
  land : Q
  zero : Q
  next : Q
  enter_home : delta entry .home = (.inl inspect, .home, .right)
  inspect_true : ∀ cell, cell lane = true →
    delta inspect (.track cell) = (.inl scan, .track cell, .right)
  inspect_false : ∀ cell, cell lane = false →
    delta inspect (.track cell) = (.inl zero, .track cell, .left)
  inspect_blank : delta inspect .blank = (.inl zero, .blank, .left)
  scan_true : ∀ cell, cell lane = true →
    delta scan (.track cell) = (.inl scan, .track cell, .right)
  scan_false : ∀ cell, cell lane = false →
    delta scan (.track cell) = (.inl clear, .track cell, .left)
  scan_blank : delta scan .blank = (.inl clear, .blank, .left)
  clear_track : ∀ cell,
    delta clear (.track cell) = (.inl rewind, .track (setTrack cell lane false), .left)
  rewind_track : ∀ cell, delta rewind (.track cell) = (.inl rewind, .track cell, .left)
  rewind_home : delta rewind .home = (.inl land, .home, .right)
  land_track : ∀ cell, delta land (.track cell) = (.inl next, .track cell, .left)

variable [Finite R] [Finite Q]
variable (initial : Q) {delta : Q → Symbol R → (Q ⊕ Bool) × Symbol R × Dir} {lane : R}

local notation "M" => host initial delta

private abbrev cfg (q : Q) (left right : List (Symbol R)) : (M).Config :=
  ⟨.inl q, (M).tapeFromLists left right⟩

omit [DecidableEq R] in
private theorem run_one (C : (M).Config) : (M).run 1 C = (M).tick C := rfl

omit [DecidableEq R] in
private theorem tick_right (q q' : Q) (left right : List (Symbol R)) (cell : Symbol R)
    (step : delta q cell = (.inl q', cell, .right)) :
    (M).tick (cfg initial q left (cell :: right)) = cfg initial q' (cell :: left) right := by
  exact ((M).tick_tapeFromLists_cons q left right cell step).trans
    (congrArg (fun tape ↦ (⟨.inl q', tape⟩ : (M).Config))
      ((M).move_tapeFromLists_right_cons left right cell))

omit [DecidableEq R] in
private theorem tick_left (q q' : Q) (left right : List (Symbol R))
    (adjacent cell : Symbol R) (step : delta q cell = (.inl q', cell, .left)) :
    (M).tick (cfg initial q (adjacent :: left) (cell :: right)) =
      cfg initial q' left (adjacent :: cell :: right) := by
  exact ((M).tick_tapeFromLists_cons q (adjacent :: left) right cell step).trans
    (congrArg (fun tape ↦ (⟨.inl q', tape⟩ : (M).Config))
      ((M).move_tapeFromLists_left_cons left (cell :: right) adjacent))

omit [DecidableEq R] in
private theorem tick_left_blank (q q' : Q) (left : List (Symbol R)) (adjacent : Symbol R)
    (step : delta q .blank = (.inl q', .blank, .left)) :
    (M).tick (cfg initial q (adjacent :: left) []) = cfg initial q' left [adjacent] := by
  exact ((M).tick_tapeFromLists_nil q (adjacent :: left) step).trans
    (congrArg (fun tape ↦ (⟨.inl q', tape⟩ : (M).Config))
      (((M).move_tapeFromLists_left_cons left [.blank] adjacent).trans
        ((M).tapeFromLists_append_blank left [adjacent])))

private theorem run_zero (rules : DecrementRules delta lane) (left right : List (Symbol R))
    (step : (M).tick (cfg initial rules.inspect (.home :: left) right) =
      cfg initial rules.zero left (.home :: right)) :
    (M).run 2 (cfg initial rules.entry left (.home :: right)) =
      cfg initial rules.zero left (.home :: right) := by
  rw [show (2 : Nat) = 1 + 1 by rfl, Machine.run_add,
    run_one initial (cfg initial rules.entry left (.home :: right)),
    tick_right initial rules.entry rules.inspect left right .home rules.enter_home]
  exact (run_one initial _).trans step

/-- A false first cell takes the zero branch and leaves the tape unchanged. -/
theorem run_decrement_zero_cell (rules : DecrementRules delta lane) (left : List (Symbol R))
    (first : R → Bool) (rest : List (R → Bool)) (hFirst : first lane = false) :
    (M).run 2 ⟨.inl rules.entry, (M).tapeFromLists left (.home :: trackTape (first :: rest))⟩ =
      ⟨.inl rules.zero, (M).tapeFromLists left (.home :: trackTape (first :: rest))⟩ :=
  run_zero initial rules left _
    (tick_left initial rules.inspect rules.zero left (trackTape rest) .home _
      (rules.inspect_false first hFirst))

/-- An empty register area takes the zero branch and leaves the tape unchanged. -/
theorem run_decrement_zero_blank (rules : DecrementRules delta lane) (left : List (Symbol R)) :
    (M).run 2 ⟨.inl rules.entry, (M).tapeFromLists left [.home]⟩ =
      ⟨.inl rules.zero, (M).tapeFromLists left [.home]⟩ :=
  run_zero initial rules left []
    (tick_left_blank initial rules.inspect rules.zero left .home rules.inspect_blank)

private theorem run_scan_positive (rules : DecrementRules delta lane)
    (left suffix : List (Symbol R)) (tracks : List (R → Bool)) (hNonempty : tracks ≠ [])
    (hTracks : ∀ cell ∈ tracks, cell lane = true) :
    (M).run tracks.length (cfg initial rules.inspect (.home :: left) (trackTape tracks ++ suffix)) =
      cfg initial rules.scan ((trackTape tracks).reverse ++ .home :: left) suffix := by
  cases tracks with
  | nil => exact (hNonempty rfl).elim
  | cons first rest =>
    have step := tick_right initial rules.inspect rules.scan (.home :: left)
      (trackTape rest ++ suffix) (.track first) (rules.inspect_true first (hTracks first (by simp)))
    have sweep : ∀ a ∈ trackTape rest, delta rules.scan a = (.inl rules.scan, a, .right) := by
      intro a ha
      obtain ⟨cell, hCell, rfl⟩ := List.mem_map.mp ha
      exact rules.scan_true cell (hTracks cell (List.mem_cons_of_mem _ hCell))
    have hTail := (M).run_sweep_right rules.scan (trackTape rest) (.track first :: .home :: left)
      suffix sweep
    simp only [trackTape, List.map_cons, List.cons_append] at step ⊢
    rw [List.length_cons, Nat.add_comm _ 1, Machine.run_add, run_one, step]
    simpa only [trackTape, List.length_map, List.reverse_cons, List.append_assoc,
      List.singleton_append] using hTail

private theorem run_land (rules : DecrementRules delta lane) (left right : List (Symbol R))
    (first : R → Bool) :
    (M).run 2 (cfg initial rules.rewind left (.home :: .track first :: right)) =
      cfg initial rules.next left (.home :: .track first :: right) := by
  rw [show (2 : Nat) = 1 + 1 by rfl, Machine.run_add,
    run_one initial (cfg initial rules.rewind left (.home :: .track first :: right)),
    tick_right initial rules.rewind rules.land left (.track first :: right) .home rules.rewind_home]
  exact (run_one initial _).trans
    (tick_left initial rules.land rules.next left right .home (.track first)
      (rules.land_track first))

private theorem run_positive (rules : DecrementRules delta lane) (left suffix : List (Symbol R))
    (before : List (R → Bool)) (last : R → Bool) (hBefore : ∀ c ∈ before, c lane = true)
    (hLast : last lane = true)
    (hStop : (M).tick (cfg initial rules.scan (.track last :: (trackTape before).reverse ++
        .home :: left) suffix) =
      cfg initial rules.clear ((trackTape before).reverse ++ .home :: left)
        (.track last :: suffix)) :
    (M).run (2 * before.length + 6)
        (cfg initial rules.entry left (.home :: (trackTape before ++ .track last :: suffix))) =
      cfg initial rules.next left
        (.home :: (trackTape before ++ .track (setTrack last lane false) :: suffix)) := by
  let crossed := trackTape before
  let cleared := .track (setTrack last lane false) :: suffix
  have hTrue : ∀ c ∈ before ++ [last], c lane = true := by
    intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact hBefore c h
    · simpa only [List.mem_singleton.mp h] using hLast
  have hScan : (M).run (before.length + 1)
      (cfg initial rules.inspect (.home :: left) (crossed ++ .track last :: suffix)) =
      cfg initial rules.scan (.track last :: crossed.reverse ++ .home :: left) suffix := by
    simpa only [crossed, trackTape, List.map_append, List.map_cons, List.map_nil,
      List.reverse_append, List.reverse_singleton, List.singleton_append, List.append_assoc,
      List.length_append, List.length_singleton, List.cons_append, List.nil_append] using
      run_scan_positive initial rules left suffix (before ++ [last]) (by simp) hTrue
  have leftRule : ∀ a ∈ crossed.reverse, delta rules.rewind a = (.inl rules.rewind, a, .left) := by
    intro a ha
    obtain ⟨cell, _, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp ha)
    exact rules.rewind_track cell
  have hClear := (M).tick_tapeFromLists_cons rules.clear (crossed.reverse ++ .home :: left)
    suffix (.track last) (rules.clear_track last)
  have hRewind := (M).run_sweep_left rules.rewind crossed.reverse (.home :: left) cleared leftRule
  rw [List.length_reverse, List.reverse_reverse, Machine.move_tapeFromLists_left_cons] at hRewind
  have hTime : 2 * before.length + 6 = 1 + (before.length + 1) + 1 + 1 + crossed.length + 2 := by
    have hLen : crossed.length = before.length := List.length_map ..
    omega
  rw [hTime, Machine.run_add, Machine.run_add, Machine.run_add, Machine.run_add, Machine.run_add,
    run_one initial (cfg initial rules.entry left (.home :: (crossed ++ .track last :: suffix))),
    tick_right initial rules.entry rules.inspect left (crossed ++ .track last :: suffix) .home
      rules.enter_home, hScan]
  rw [run_one initial (cfg initial rules.scan (.track last :: crossed.reverse ++ .home :: left)
        suffix), hStop, run_one, hClear, hRewind]
  cases before with
  | nil => exact run_land initial rules left suffix (setTrack last lane false)
  | cons first rest => exact run_land initial rules left (trackTape rest ++ cleared) first

/-- Decrement at an existing false boundary clears the preceding true cell. -/
theorem run_decrement_positive_cell (rules : DecrementRules delta lane) (left : List (Symbol R))
    (before : List (R → Bool)) (last firstFalse : R → Bool) (after : List (R → Bool))
    (hBefore : ∀ c ∈ before, c lane = true) (hLast : last lane = true)
    (hFalse : firstFalse lane = false) :
    (M).run (2 * before.length + 6)
      ⟨.inl rules.entry, (M).tapeFromLists left
        (.home :: trackTape (before ++ last :: firstFalse :: after))⟩ =
      ⟨.inl rules.next, (M).tapeFromLists left
        (.home :: trackTape (before ++ setTrack last lane false :: firstFalse :: after))⟩ := by
  simpa only [trackTape, List.map_append, List.map_cons] using
    run_positive initial rules left (.track firstFalse :: trackTape after) before last hBefore hLast
      (tick_left initial rules.scan rules.clear ((trackTape before).reverse ++ .home :: left)
        (trackTape after) (.track last) (.track firstFalse) (rules.scan_false firstFalse hFalse))

/-- Decrement at the right boundary clears the last stored cell. -/
theorem run_decrement_positive_blank (rules : DecrementRules delta lane) (left : List (Symbol R))
    (before : List (R → Bool)) (last : R → Bool)
    (hBefore : ∀ c ∈ before, c lane = true) (hLast : last lane = true) :
    (M).run (2 * before.length + 6)
      ⟨.inl rules.entry, (M).tapeFromLists left (.home :: trackTape (before ++ [last]))⟩ =
      ⟨.inl rules.next, (M).tapeFromLists left
        (.home :: trackTape (before ++ [setTrack last lane false]))⟩ := by
  simpa only [trackTape, List.map_append, List.map_cons, List.map_nil] using
    run_positive initial rules left [] before last hBefore hLast
      (tick_left_blank initial rules.scan rules.clear ((trackTape before).reverse ++ .home :: left)
        (.track last) rules.scan_blank)

end PvsNP.RegisterMachine
