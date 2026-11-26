module

public import PvsNP.TuringMachine.Registers.Alphabet
public import PvsNP.TuringMachine.Transducer

/-! # Canonical output from the register tape

The finishing instructions traverse the work area and erase it on the return
sweep. They erase both markers and the input before moving the head left
across the output and returning it to the first output bit.
-/

@[expose] public section

namespace PvsNP.RegisterMachine

open Turing

private theorem tapeFromLists_blanks {α : Type} (M : Machine α) (left : List M.Symbol) (n : Nat) :
    M.tapeFromLists left (List.replicate n M.blank) = M.tapeFromLists left [] := by
  have h : @ListBlank.mk _ M.tapeInhabited (List.replicate n M.blank) =
      @ListBlank.mk _ M.tapeInhabited [] := Quotient.sound (Or.inr ⟨n, rfl⟩)
  exact congrArg (@Tape.mk' _ M.tapeInhabited (@ListBlank.mk _ M.tapeInhabited left)) h

private theorem tapeFromLists_left_blank {α : Type} (M : Machine α) (right : List M.Symbol) :
    M.tapeFromLists [M.blank] right = M.tapeFromLists [] right := by
  have h : @ListBlank.mk _ M.tapeInhabited [M.blank] =
      @ListBlank.mk _ M.tapeInhabited [] := Quotient.sound (Or.inr ⟨1, rfl⟩)
  exact congrArg
    (fun left ↦ @Tape.mk' _ M.tapeInhabited left (@ListBlank.mk _ M.tapeInhabited right)) h

private theorem erase_left {α : Type} (M : Machine α) (q : M.State)
    (crossed left right : List M.Symbol)
    (h : ∀ a ∈ crossed, M.transition q a = (.inl q, M.blank, .left)) :
    M.run crossed.length
        ⟨.inl q, @Tape.move _ M.tapeInhabited .left (M.tapeFromLists (crossed ++ left) right)⟩ =
      ⟨.inl q, @Tape.move _ M.tapeInhabited .left
        (M.tapeFromLists left (List.replicate crossed.length M.blank ++ right))⟩ := by
  induction crossed generalizing right with
  | nil => rfl
  | cons a crossed ih =>
    simp only [List.length_cons, List.cons_append, Machine.run_succ, M.move_tapeFromLists_left_cons,
      M.tick_tapeFromLists_cons q (crossed ++ left) right a (h a List.mem_cons_self)]
    simpa only [List.replicate_succ', List.append_assoc, List.singleton_append] using
      ih (M.blank :: right) (fun s hs ↦ h s (List.mem_cons_of_mem _ hs))

private theorem run_finishSegments {α : Type} (M : Machine α)
    (entry scanRight eraseWork eraseInput scanOutput : M.State)
    (home start : M.Symbol) (input output work : List M.Symbol)
    (hEntry : M.transition entry home = (.inl scanRight, home, .right))
    (hRight : ∀ a ∈ work, M.transition scanRight a = (.inl scanRight, a, .right))
    (hReturn : M.transition scanRight M.blank = (.inl eraseWork, M.blank, .left))
    (hWork : ∀ a ∈ work, M.transition eraseWork a = (.inl eraseWork, M.blank, .left))
    (hHome : M.transition eraseWork home = (.inl eraseInput, M.blank, .left))
    (hInput : ∀ a ∈ input, M.transition eraseInput a = (.inl eraseInput, M.blank, .left))
    (hStart : M.transition eraseInput start = (.inl scanOutput, M.blank, .left))
    (hOutput : ∀ a ∈ output, M.transition scanOutput a = (.inl scanOutput, a, .left))
    (hHalt : M.transition scanOutput M.blank = (.inr true, M.blank, .right)) :
    M.run (1 + work.length + 1 + work.length + 1 + input.length + 1 + output.length + 1)
        ⟨.inl entry, M.tapeFromLists (input ++ start :: output) (home :: work)⟩ =
      ⟨.inr true, M.tapeFromLists [] output.reverse⟩ := by
  let before := input ++ start :: output
  let farLeft := work.reverse ++ home :: before
  have entryTick : M.tick ⟨.inl entry, M.tapeFromLists before (home :: work)⟩ =
      ⟨.inl scanRight, M.tapeFromLists (home :: before) work⟩ := by
    rw [M.tick_tapeFromLists_cons entry before work home hEntry, M.move_tapeFromLists_right_cons]
  have scanRun : M.run work.length ⟨.inl scanRight, M.tapeFromLists (home :: before) work⟩ =
      ⟨.inl scanRight, M.tapeFromLists farLeft []⟩ := by
    simpa only [List.append_nil] using M.run_sweep_right scanRight work (home :: before) [] hRight
  have returnTick : M.tick ⟨.inl scanRight, M.tapeFromLists farLeft []⟩ =
      ⟨.inl eraseWork, @Tape.move _ M.tapeInhabited .left (M.tapeFromLists farLeft [])⟩ := by
    rw [M.tick_tapeFromLists_nil scanRight farLeft hReturn, M.tapeFromLists_right_blank]
  have workRun : M.run work.length
        ⟨.inl eraseWork, @Tape.move _ M.tapeInhabited .left (M.tapeFromLists farLeft [])⟩ =
      ⟨.inl eraseWork, M.tapeFromLists before [home]⟩ := by
    simpa only [List.length_reverse, List.append_nil, tapeFromLists_blanks,
      M.move_tapeFromLists_left_cons] using
      erase_left M eraseWork work.reverse (home :: before) []
        (fun a ha ↦ hWork a (List.mem_reverse.mp ha))
  have homeTick : M.tick ⟨.inl eraseWork, M.tapeFromLists before [home]⟩ =
      ⟨.inl eraseInput, @Tape.move _ M.tapeInhabited .left (M.tapeFromLists before [])⟩ := by
    rw [M.tick_tapeFromLists_cons eraseWork before [] home hHome, M.tapeFromLists_right_blank]
  have inputRun : M.run input.length
        ⟨.inl eraseInput, @Tape.move _ M.tapeInhabited .left (M.tapeFromLists before [])⟩ =
      ⟨.inl eraseInput, M.tapeFromLists output [start]⟩ := by
    simpa only [List.append_nil, tapeFromLists_blanks, M.move_tapeFromLists_left_cons] using
      erase_left M eraseInput input (start :: output) [] hInput
  have startTick : M.tick ⟨.inl eraseInput, M.tapeFromLists output [start]⟩ =
      ⟨.inl scanOutput, @Tape.move _ M.tapeInhabited .left (M.tapeFromLists output [])⟩ := by
    rw [M.tick_tapeFromLists_cons eraseInput output [] start hStart, M.tapeFromLists_right_blank]
  have outputRun : M.run output.length
        ⟨.inl scanOutput, @Tape.move _ M.tapeInhabited .left (M.tapeFromLists output [])⟩ =
      ⟨.inl scanOutput, M.tapeFromLists [] (M.blank :: output.reverse)⟩ := by
    simpa only [List.append_nil, M.move_tapeFromLists_left_nil] using
      M.run_sweep_left scanOutput output [] [] hOutput
  have haltTick : M.tick ⟨.inl scanOutput, M.tapeFromLists [] (M.blank :: output.reverse)⟩ =
      ⟨.inr true, M.tapeFromLists [] output.reverse⟩ := by
    rw [M.tick_tapeFromLists_cons scanOutput [] output.reverse M.blank hHalt,
      M.move_tapeFromLists_right_cons, tapeFromLists_left_blank]
  rw [M.run_add, M.run_add, M.run_add, M.run_add, M.run_add, M.run_add, M.run_add, M.run_add]
  change M.tick (M.run output.length (M.tick (M.run input.length (M.tick (M.run work.length
    (M.tick (M.run work.length
      (M.tick ⟨.inl entry, M.tapeFromLists before (home :: work)⟩)))))))) = _
  rw [entryTick, scanRun, returnTick, workRun, homeTick, inputRun, startTick, outputRun, haltTick]

/-- Erase the work and input areas and halt with exactly the output word.
Output is in the reverse of emission order, because each emission grows to the left. -/
theorem run_finish {R Q : Type} [Finite R] [Finite Q] (initial : Q)
    (delta : Q → Symbol R → (Q ⊕ Bool) × Symbol R × Dir)
    (entry scanRight eraseWork eraseInput scanOutput : Q)
    (x emitted : BinaryWord) (cells : List (R → Bool))
    (hEntry : delta entry .home = (.inl scanRight, .home, .right))
    (hRight : ∀ a, delta scanRight (.track a) = (.inl scanRight, .track a, .right))
    (hReturn : delta scanRight .blank = (.inl eraseWork, .blank, .left))
    (hWork : ∀ a, delta eraseWork (.track a) = (.inl eraseWork, .blank, .left))
    (hHome : delta eraseWork .home = (.inl eraseInput, .blank, .left))
    (hInput : ∀ a, delta eraseInput (.bit a) = (.inl eraseInput, .blank, .left))
    (hStart : delta eraseInput .start = (.inl scanOutput, .blank, .left))
    (hOutput : ∀ a, delta scanOutput (.bit a) = (.inl scanOutput, .bit a, .left))
    (hHalt : delta scanOutput .blank = (.inr true, .blank, .right)) :
    let M := host initial delta
    M.run (2 * cells.length + x.length + emitted.length + 5)
        ⟨.inl entry, M.tapeFromLists (bits x.reverse ++ .start :: bits emitted)
          (.home :: trackTape cells)⟩ =
      ⟨.inr true, M.wordTape emitted.reverse⟩ := by
  let M := host initial delta
  have cost : 1 + (trackTape cells).length + 1 + (trackTape cells).length + 1 +
      (bits (R := R) x.reverse).length + 1 + (bits (R := R) emitted).length + 1 =
      2 * cells.length + x.length + emitted.length + 5 := by
    simp only [trackTape, bits, List.length_map, List.length_reverse]
    omega
  have tape : M.tapeFromLists [] (bits (R := R) emitted).reverse = M.wordTape emitted.reverse := by
    change M.tapeFromLists [] (emitted.map Symbol.bit).reverse =
      M.tapeFromLists [] (emitted.reverse.map Symbol.bit)
    rw [List.map_reverse]
  simpa only [cost, tape] using
    run_finishSegments M entry scanRight eraseWork eraseInput scanOutput .home .start
      (bits x.reverse) (bits emitted) (trackTape cells) hEntry
      (fun _ ha ↦ by
        obtain ⟨cell, _, rfl⟩ := List.mem_map.mp ha
        exact hRight cell) hReturn
      (fun _ ha ↦ by
        obtain ⟨cell, _, rfl⟩ := List.mem_map.mp ha
        exact hWork cell) hHome
      (fun _ ha ↦ by
        obtain ⟨bit, _, rfl⟩ := List.mem_map.mp ha
        exact hInput bit) hStart
      (fun _ ha ↦ by
        obtain ⟨bit, _, rfl⟩ := List.mem_map.mp ha
        exact hOutput bit) hHalt

end PvsNP.RegisterMachine
