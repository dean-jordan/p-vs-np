module

public import PvsNP.TuringMachine.Registers.Increment
public import PvsNP.TuringMachine.Registers.Values

/-! # Arithmetic instructions on represented register values -/

@[expose] public section

namespace PvsNP.RegisterMachine

open Turing

variable {R Q : Type} [Finite R] [Finite Q] [DecidableEq R]
  {delta : Q → Symbol R → (Q ⊕ Bool) × Symbol R × Dir}

/-- A physical increment takes two moves per true bit and four fixed moves. -/
theorem run_increment (initial : Q) {lane : R} (rules : IncrementRules delta lane)
    (left : List (Symbol R)) {cells : List (R → Bool)} {values : R → Nat}
    (h : Represents cells values) :
    let M := host initial delta
    M.run (2 * values lane + 4)
      ⟨.inl rules.entry, M.tapeFromLists left (.home :: trackTape cells)⟩ =
      ⟨.inl rules.next,
        M.tapeFromLists left (.home :: trackTape (incrementCells lane cells))⟩ := by
  dsimp only
  rcases incrementCells_split lane cells with
    ⟨before, cell, after, rfl, hp, hc, hi⟩ | ⟨hp, hi⟩
  · have hStop : readLane (cell :: after) 0 lane = false := hc
    have hValue := h.value_eq_prefix lane hp hStop
    rw [hValue, hi]
    exact run_increment_cell initial rules left before cell after hp hc
  · have hValue : values lane = cells.length := by
      apply Represents.value_eq_prefix (suffix := []) _ lane hp rfl
      simpa only [List.append_nil] using h
    rw [hValue, hi]
    exact run_increment_blank initial rules left cells hp

end PvsNP.RegisterMachine
