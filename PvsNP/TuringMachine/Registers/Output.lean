module

public import PvsNP.TuringMachine.Registers.Alphabet
public import PvsNP.TuringMachine.Sweeps

/-! # Counted output on the register tape

An output instruction preserves the input and work cells. It writes a new
output bit just beyond the previously emitted bits, to the left of the input.
The return to the home cell includes two physical moves.
-/

@[expose] public section

namespace PvsNP.RegisterMachine

open Turing

private theorem run_emitSegment {α : Type} (M : Machine α)
    (entry scanLeft scanRight bounce done : M.State)
    (home written : M.Symbol) (crossed right : List M.Symbol)
    (hEntry : M.transition entry home = (.inl scanLeft, home, .left))
    (hLeft : ∀ a ∈ crossed, M.transition scanLeft a = (.inl scanLeft, a, .left))
    (hWrite : M.transition scanLeft M.blank = (.inl scanRight, written, .right))
    (hRight : ∀ a ∈ crossed, M.transition scanRight a = (.inl scanRight, a, .right))
    (hHome : M.transition scanRight home = (.inl bounce, home, .left))
    (hDone : ∀ a ∈ crossed ++ [written], M.transition bounce a = (.inl done, a, .right)) :
    M.run (1 + crossed.length + 1 + crossed.length + 2)
        ⟨.inl entry, M.tapeFromLists crossed (home :: right)⟩ =
      ⟨.inl done, M.tapeFromLists (crossed ++ [written]) (home :: right)⟩ := by
  let afterCrossing := crossed.reverse ++ home :: right
  have entryTick := M.tick_tapeFromLists_cons entry crossed right home hEntry
  have leftRun := M.run_sweep_left scanLeft crossed [] (home :: right) hLeft
  rw [List.append_nil] at leftRun
  have writeTick : M.tick ⟨.inl scanLeft,
        @Tape.move _ M.tapeInhabited .left (M.tapeFromLists [] afterCrossing)⟩ =
      ⟨.inl scanRight, M.tapeFromLists [written] afterCrossing⟩ := by
    rw [M.move_tapeFromLists_left_nil,
      M.tick_tapeFromLists_cons scanLeft [] afterCrossing M.blank hWrite,
      M.move_tapeFromLists_right_cons]
  have rightRun : M.run crossed.length ⟨.inl scanRight,
        M.tapeFromLists [written] afterCrossing⟩ =
      ⟨.inl scanRight, M.tapeFromLists (crossed ++ [written]) (home :: right)⟩ := by
    simpa only [List.length_reverse, List.reverse_reverse] using
      M.run_sweep_right scanRight crossed.reverse [written] (home :: right)
        (fun a ha ↦ hRight a (List.mem_reverse.mp ha))
  have returnRun : M.run 2
        ⟨.inl scanRight, M.tapeFromLists (crossed ++ [written]) (home :: right)⟩ =
      ⟨.inl done, M.tapeFromLists (crossed ++ [written]) (home :: right)⟩ := by
    change M.tick (M.tick ⟨.inl scanRight,
      M.tapeFromLists (crossed ++ [written]) (home :: right)⟩) = _
    rw [M.tick_tapeFromLists_cons scanRight (crossed ++ [written]) right home hHome]
    cases segment : crossed ++ [written] with
    | nil => simp at segment
    | cons a tail =>
      have ha : a ∈ crossed ++ [written] := by
        rw [segment]
        exact List.mem_cons_self
      rw [M.move_tapeFromLists_left_cons,
        M.tick_tapeFromLists_cons bounce tail (home :: right) a (hDone a ha),
        M.move_tapeFromLists_right_cons]
  rw [M.run_add, M.run_add, M.run_add, M.run_add]
  change M.run 2 (M.run crossed.length (M.tick (M.run crossed.length
    (M.tick ⟨.inl entry, M.tapeFromLists crossed (home :: right)⟩)))) = _
  rw [entryTick, leftRun, writeTick, rightRun, returnRun]

/-- Append one bit to the output while preserving the input and work cells.
The head starts and finishes on the home marker. -/
theorem run_emitBit {R Q : Type} [Finite R] [Finite Q] (initial : Q)
    (delta : Q → Symbol R → (Q ⊕ Bool) × Symbol R × Dir)
    (entry scanLeft scanRight bounce done : Q)
    (x emitted : List Bool) (b : Bool) (right : List (Symbol R))
    (hEntry : delta entry .home = (.inl scanLeft, .home, .left))
    (hLeftBit : ∀ a, delta scanLeft (.bit a) = (.inl scanLeft, .bit a, .left))
    (hLeftStart : delta scanLeft .start = (.inl scanLeft, .start, .left))
    (hWrite : delta scanLeft .blank = (.inl scanRight, .bit b, .right))
    (hRightBit : ∀ a, delta scanRight (.bit a) = (.inl scanRight, .bit a, .right))
    (hRightStart : delta scanRight .start = (.inl scanRight, .start, .right))
    (hHome : delta scanRight .home = (.inl bounce, .home, .left))
    (hDoneBit : ∀ a, delta bounce (.bit a) = (.inl done, .bit a, .right))
    (hDoneStart : delta bounce .start = (.inl done, .start, .right)) :
    let M := host initial delta
    M.run (2 * (x.length + emitted.length) + 6)
        ⟨.inl entry, M.tapeFromLists (bits x.reverse ++ .start :: bits emitted) (.home :: right)⟩ =
      ⟨.inl done, M.tapeFromLists (bits x.reverse ++ .start :: bits (emitted ++ [b]))
        (.home :: right)⟩ := by
  let M := host initial delta
  let crossed : List (Symbol R) := bits x.reverse ++ .start :: bits emitted
  have crossedType (a : Symbol R) (ha : a ∈ crossed) : a = .start ∨ ∃ bit, a = .bit bit := by
    simp only [crossed, List.mem_append, List.mem_cons] at ha
    rcases ha with h | h | h
    · obtain ⟨bit, _, rfl⟩ := List.mem_map.mp h
      exact Or.inr ⟨bit, rfl⟩
    · exact Or.inl h
    · obtain ⟨bit, _, rfl⟩ := List.mem_map.mp h
      exact Or.inr ⟨bit, rfl⟩
  have hl : ∀ a ∈ crossed, delta scanLeft a = (.inl scanLeft, a, .left) := by
    intro a ha
    rcases crossedType a ha with rfl | ⟨bit, rfl⟩
    · exact hLeftStart
    · exact hLeftBit bit
  have hr : ∀ a ∈ crossed, delta scanRight a = (.inl scanRight, a, .right) := by
    intro a ha
    rcases crossedType a ha with rfl | ⟨bit, rfl⟩
    · exact hRightStart
    · exact hRightBit bit
  have hd : ∀ a ∈ crossed ++ [.bit b], delta bounce a = (.inl done, a, .right) := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · rcases crossedType a ha with rfl | ⟨bit, rfl⟩
      · exact hDoneStart
      · exact hDoneBit bit
    · obtain rfl := List.mem_singleton.mp ha
      exact hDoneBit b
  have cost : 1 + crossed.length + 1 + crossed.length + 2 =
      2 * (x.length + emitted.length) + 6 := by
    simp only [crossed, bits, List.length_append, List.length_cons, List.length_map,
      List.length_reverse]
    omega
  have cells : crossed ++ [.bit b] = bits x.reverse ++ .start :: bits (emitted ++ [b]) := by
    simp [crossed, bits, List.append_assoc]
  simpa only [cost, cells] using
    run_emitSegment M entry scanLeft scanRight bounce done .home (.bit b) crossed right
      hEntry hl hWrite hr hHome hd

end PvsNP.RegisterMachine
