module

public import PvsNP.TuringMachine.Registers.Alphabet

/-! # Counted reset of a marked input cursor

The cursor marker carries the bit it replaced. Reset starts at the home
cell, restores that bit, and returns to the home cell.
-/

@[expose] public section

namespace PvsNP.RegisterMachine

open Turing

/-- Restore a marked input bit, leaving all other cells unchanged. The marked
bit is preceded by `near` in the nearest-first list to the left of home. -/
theorem run_resetInput {R Q : Type} [Finite R] [Finite Q] (initial : Q)
    (delta : Q → Symbol R → (Q ⊕ Bool) × Symbol R × Dir)
    (entry scanLeft scanRight bounce done : Q)
    (near : BinaryWord) (prior : Bool) (far right : List (Symbol R))
    (hEntry : delta entry .home = (.inl scanLeft, .home, .left))
    (hLeftBit : ∀ a, delta scanLeft (.bit a) = (.inl scanLeft, .bit a, .left))
    (hRestore : delta scanLeft (.inputMark prior) = (.inl scanRight, .bit prior, .right))
    (hRightBit : ∀ a, delta scanRight (.bit a) = (.inl scanRight, .bit a, .right))
    (hHome : delta scanRight .home = (.inl bounce, .home, .left))
    (hDoneBit : ∀ a, delta bounce (.bit a) = (.inl done, .bit a, .right)) :
    let M := host initial delta
    M.run (2 * near.length + 4)
        ⟨.inl entry, M.tapeFromLists (bits near ++ .inputMark prior :: far) (.home :: right)⟩ =
      ⟨.inl done, M.tapeFromLists (bits near ++ .bit prior :: far) (.home :: right)⟩ := by
  let M := host initial delta
  let crossed : List (Symbol R) := bits near
  let before := crossed ++ .inputMark prior :: far
  let restored := crossed ++ .bit prior :: far
  let behind := crossed.reverse ++ .home :: right
  have entryTick := M.tick_tapeFromLists_cons entry before right .home hEntry
  have leftRun := M.run_sweep_left scanLeft crossed (.inputMark prior :: far) (.home :: right)
    (fun _ ha ↦ by
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
      exact hLeftBit b)
  have restoreTick : M.tick ⟨.inl scanLeft, @Tape.move _ M.tapeInhabited .left
        (M.tapeFromLists (.inputMark prior :: far) behind)⟩ =
      ⟨.inl scanRight, M.tapeFromLists (.bit prior :: far) behind⟩ := by
    rw [M.move_tapeFromLists_left_cons,
      M.tick_tapeFromLists_cons scanLeft far behind (.inputMark prior) hRestore,
      M.move_tapeFromLists_right_cons]
  have rightRun : M.run crossed.length
        ⟨.inl scanRight, M.tapeFromLists (.bit prior :: far) behind⟩ =
      ⟨.inl scanRight, M.tapeFromLists restored (.home :: right)⟩ := by
    simpa only [List.length_reverse, List.reverse_reverse] using
      M.run_sweep_right scanRight crossed.reverse (.bit prior :: far) (.home :: right)
        (fun _ ha ↦ by
          obtain ⟨b, _, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp ha)
          exact hRightBit b)
  have returnRun : M.run 2 ⟨.inl scanRight, M.tapeFromLists restored (.home :: right)⟩ =
      ⟨.inl done, M.tapeFromLists restored (.home :: right)⟩ := by
    change M.tick (M.tick ⟨.inl scanRight, M.tapeFromLists restored (.home :: right)⟩) = _
    rw [M.tick_tapeFromLists_cons scanRight restored right .home hHome]
    have hBit : ∃ b tail, restored = .bit b :: tail := by
      cases near with
      | nil => exact ⟨prior, far, rfl⟩
      | cons b tail => exact ⟨b, bits tail ++ .bit prior :: far, rfl⟩
    obtain ⟨b, tail, hRestored⟩ := hBit
    rw [hRestored, M.move_tapeFromLists_left_cons,
      M.tick_tapeFromLists_cons bounce tail (.home :: right) (.bit b) (hDoneBit b),
      M.move_tapeFromLists_right_cons]
  have cost : 2 * near.length + 4 = 1 + crossed.length + 1 + crossed.length + 2 := by
    simp only [crossed, bits, List.length_map]
    omega
  change M.run (2 * near.length + 4) ⟨.inl entry, M.tapeFromLists before (.home :: right)⟩ = _
  rw [cost, M.run_add, M.run_add, M.run_add, M.run_add]
  change M.run 2 (M.run crossed.length (M.tick (M.run crossed.length
    (M.tick ⟨.inl entry, M.tapeFromLists before (.home :: right)⟩)))) = _
  rw [entryTick, leftRun, restoreTick, rightRun, returnRun]

end PvsNP.RegisterMachine
