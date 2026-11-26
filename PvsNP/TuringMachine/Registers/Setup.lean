module

public import PvsNP.TuringMachine.Registers.Alphabet

/-! # Frame the input for a register program

The setup places a left sentinel, sweeps the unmodified input, and writes
the register boundary in the first blank cell after it.
-/

@[expose] public section

namespace PvsNP.RegisterMachine

open Turing

variable {R Q : Type} [Finite R] [Finite Q]

/-- The transitions for the initial input sweep and the return to the register boundary. -/
structure SetupRules (delta : Q → Symbol R → (Q ⊕ Bool) × Symbol R × Dir) where
  entry : Q
  mark : Q
  scan : Q
  land : Q
  next : Q
  enter : ∀ a, delta entry a = (.inl mark, a, .left)
  mark_blank : delta mark .blank = (.inl scan, .start, .right)
  scan_bit : ∀ b, delta scan (.bit b) = (.inl scan, .bit b, .right)
  scan_blank : delta scan .blank = (.inl land, .home, .left)
  land_bit : ∀ b, delta land (.bit b) = (.inl next, .bit b, .right)
  land_start : delta land .start = (.inl next, .start, .right)

variable {delta : Q → Symbol R → (Q ⊕ Bool) × Symbol R × Dir} (rules : SetupRules delta)

local notation "M" => host rules.entry delta

private abbrev cfg (q : Q) (left right : List (Symbol R)) : (M).Config :=
  ⟨.inl q, (M).tapeFromLists left right⟩

private theorem tick_enter (x : BinaryWord) :
    (M).tick ((M).start x) = cfg rules rules.mark [] (.blank :: bits x) := by
  cases x with
  | nil =>
    change (M).tick (cfg rules rules.entry [] []) = _
    rw [(M).tick_tapeFromLists_nil rules.entry [] (rules.enter .blank),
      (M).tapeFromLists_right_blank [], (M).move_tapeFromLists_left_nil []]
    rfl
  | cons b x =>
    change (M).tick (cfg rules rules.entry [] (.bit b :: bits x)) = _
    rw [(M).tick_tapeFromLists_cons rules.entry [] (bits x) (.bit b) (rules.enter (.bit b)),
      (M).move_tapeFromLists_left_nil]
    rfl

private theorem run_mark_home (left : List (Symbol R)) (a : Symbol R)
    (hLand : delta rules.land a = (.inl rules.next, a, .right)) :
    (M).run 2 (cfg rules rules.scan (a :: left) []) =
      cfg rules rules.next (a :: left) [.home] := by
  rw [(M).run_succ, (M).tick_tapeFromLists_nil rules.scan (a :: left) rules.scan_blank,
    (M).move_tapeFromLists_left_cons, (M).run_succ,
    (M).tick_tapeFromLists_cons rules.land left [.home] a hLand,
    (M).move_tapeFromLists_right_cons, (M).run_zero]

/-- Input framing stops at the register boundary with the word unchanged and no register
cells or output on the tape. Each input symbol is crossed once. -/
theorem run_setup (x : BinaryWord) :
    (M).run (x.length + 4) ((M).start x) =
      ⟨.inl rules.next, (M).tapeFromLists ((bits x).reverse ++ [.start]) [.home]⟩ := by
  have sweepRule (a : Symbol R) (ha : a ∈ bits x) :
      delta rules.scan a = (.inl rules.scan, a, .right) := by
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    exact rules.scan_bit b
  have sweep : (M).run x.length (cfg rules rules.scan [.start] (bits x)) =
      cfg rules rules.scan ((bits x).reverse ++ [.start]) [] := by
    simpa only [List.length_map, List.append_nil] using
      (M).run_sweep_right rules.scan (bits x) [.start] [] sweepRule
  rw [show x.length + 4 = (x.length + 2) + 1 + 1 by omega,
    (M).run_succ, tick_enter rules, (M).run_succ,
    (M).tick_tapeFromLists_cons rules.mark [] (bits x) .blank rules.mark_blank,
    (M).move_tapeFromLists_right_cons, (M).run_add, sweep, ← List.map_reverse]
  cases x.reverse with
  | nil => exact run_mark_home rules [] .start rules.land_start
  | cons b tail => exact run_mark_home rules (bits tail ++ [.start]) (.bit b) (rules.land_bit b)

end PvsNP.RegisterMachine
