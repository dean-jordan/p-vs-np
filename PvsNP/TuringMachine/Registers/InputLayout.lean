module

public import PvsNP.TuringMachine.Registers.Cursor
public import PvsNP.TuringMachine.Registers.ResetInput

/-! # Relating a tape marker to an input index

The logical word is in nearest-first order, which is the reverse of the
original input when the head is at the register boundary.
-/

@[expose] public section

namespace PvsNP.RegisterMachine

open Turing

variable {R : Type}

/-- The machine keeps the input unchanged except for the marker at the indexed bit. -/
inductive InputLayout (word : BinaryWord) (suffix : List (Symbol R)) :
    Option Nat → List (Symbol R) → Prop
  | unmarked : InputLayout word suffix none (bits word ++ .start :: suffix)
  | marked (near tail : BinaryWord) (b : Bool) (h : word = near ++ b :: tail) :
      InputLayout word suffix (some near.length)
        (bits near ++ .inputMark b :: (bits tail ++ .start :: suffix))

theorem InputLayout.index_lt {word : BinaryWord} {suffix left : List (Symbol R)} {i : Nat}
    (h : InputLayout word suffix (some i) left) : i < word.length := by
  cases h with
  | marked near tail b hWord => simp [hWord]

variable {Q : Type} [Finite R] [Finite Q]
  {delta : Q → Symbol R → (Q ⊕ Bool) × Symbol R × Dir}
  (initial : Q) (rules : CursorRules delta)

local notation "M" => host initial delta

/-- Read at index zero and place the marker on that cell if it exists. -/
theorem run_cursor_first (word : BinaryWord) (suffix right : List (Symbol R)) :
    let result := word[0]?
    ∃ left, InputLayout word suffix (result.map fun _ ↦ 0) left ∧
      (M).run 4 ⟨.inl rules.first,
        (M).tapeFromLists (bits word ++ .start :: suffix) (.home :: right)⟩ =
        ⟨.inl (rules.next result), (M).tapeFromLists left (.home :: right)⟩ := by
  cases word with
  | nil =>
    exact ⟨_, .unmarked, run_cursor_first_empty initial rules suffix right⟩
  | cons b tail =>
    refine ⟨_, InputLayout.marked [] tail b rfl, ?_⟩
    simpa only [List.map_cons, List.cons_append, List.getElem?_cons_zero, List.map_nil,
      List.nil_append] using
      run_cursor_first_bit initial rules tail b (.start :: suffix) right

/-- The cursor read at the next index returns `none` exactly when it passes the last bit. -/
theorem InputLayout.run_next {word : BinaryWord} {suffix left : List (Symbol R)} {i : Nat}
    (h : InputLayout word suffix (some i) left) (right : List (Symbol R)) :
    let result := word[i + 1]?
    ∃ nextLeft, InputLayout word suffix (result.map fun _ ↦ i + 1) nextLeft ∧
      (M).run (2 * i + 6) ⟨.inl rules.advance, (M).tapeFromLists left (.home :: right)⟩ =
        ⟨.inl (rules.next result), (M).tapeFromLists nextLeft (.home :: right)⟩ := by
  dsimp only
  cases h with
  | marked near tail prior hWord =>
    have hRead : word[near.length + 1]? = tail[0]? := by
      rw [hWord, List.getElem?_append_right (by omega)]
      simp only [Nat.add_sub_cancel_left, List.getElem?_cons_succ]
    rw [hRead]
    cases tail with
    | nil =>
      refine ⟨_, InputLayout.unmarked, ?_⟩
      simpa only [hWord, List.getElem?_nil, List.map_append, List.map_cons, List.map_nil,
        List.nil_append, List.append_assoc, List.singleton_append] using
        run_cursor_next_end initial rules near prior suffix right
    | cons b tail =>
      have hMore : word = (near ++ [prior]) ++ b :: tail := by
        simp only [hWord, List.append_assoc, List.singleton_append]
      refine ⟨bits (near ++ [prior]) ++ .inputMark b :: (bits tail ++ .start :: suffix), ?_, ?_⟩
      · simpa only [List.length_append, List.length_singleton, List.getElem?_cons_zero,
          Option.map_some] using
          (InputLayout.marked (suffix := suffix) (near ++ [prior]) tail b hMore)
      · simpa only [List.map_append, List.map_cons, List.map_nil, List.cons_append,
          List.nil_append, List.append_assoc, List.singleton_append, List.getElem?_cons_zero] using
          run_cursor_next_bit initial rules near prior b (bits tail ++ .start :: suffix) right

/-- Resetting the cursor restores the unmarked representation of the original input. -/
theorem InputLayout.run_reset {word : BinaryWord} {suffix left : List (Symbol R)} {i : Nat}
    (h : InputLayout word suffix (some i) left) (right : List (Symbol R))
    (entry scanLeft scanRight bounce done : Q)
    (hEntry : delta entry .home = (.inl scanLeft, .home, .left))
    (hLeftBit : ∀ a, delta scanLeft (.bit a) = (.inl scanLeft, .bit a, .left))
    (hRestore : ∀ a, delta scanLeft (.inputMark a) = (.inl scanRight, .bit a, .right))
    (hRightBit : ∀ a, delta scanRight (.bit a) = (.inl scanRight, .bit a, .right))
    (hHome : delta scanRight .home = (.inl bounce, .home, .left))
    (hDoneBit : ∀ a, delta bounce (.bit a) = (.inl done, .bit a, .right)) :
    (M).run (2 * i + 4) ⟨.inl entry, (M).tapeFromLists left (.home :: right)⟩ =
      ⟨.inl done, (M).tapeFromLists (bits word ++ .start :: suffix) (.home :: right)⟩ := by
  cases h with
  | marked near tail b hWord =>
    simpa only [hWord, List.map_append, List.map_cons, List.append_assoc, List.cons_append] using
      run_resetInput initial delta entry scanLeft scanRight bounce done near b
        (bits tail ++ .start :: suffix) right hEntry hLeftBit (hRestore b) hRightBit hHome hDoneBit

end PvsNP.RegisterMachine
