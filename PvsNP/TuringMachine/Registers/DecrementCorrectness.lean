module

public import PvsNP.TuringMachine.Registers.Decrement
public import PvsNP.TuringMachine.Registers.Program

/-! # Correctness of decrement on unary registers -/

@[expose] public section

namespace PvsNP.RegisterMachine

variable {R : Type} [DecidableEq R]

/-- Clear the last true bit in the selected lane's initial run of true bits. -/
def decrementCells (lane : R) : List (R → Bool) → List (R → Bool)
  | [] => []
  | cell :: cells =>
    if cell lane then
      if readLane cells 0 lane then cell :: decrementCells lane cells
      else setTrack cell lane false :: cells
    else cell :: cells

theorem length_decrementCells (lane : R) (cells : List (R → Bool)) :
    (decrementCells lane cells).length = cells.length := by
  induction cells with
  | nil => rfl
  | cons cell cells ih =>
    by_cases hFirst : cell lane <;> by_cases hNext : readLane cells 0 lane <;>
      simp [decrementCells, hFirst, hNext, ih]

private theorem decrementValues_unchanged (lane : R) (values : R → Nat) (hz : values lane = 0) :
    decrementValues lane values = values := by
  funext r
  by_cases hr : r = lane
  · subst r
    simp [decrementValues, hz]
  · simp [decrementValues, hr]

private theorem decrementValues_shift (lane : R) (values : R → Nat) :
    decrementValues lane (fun r ↦ values r - 1) = fun r ↦ decrementValues lane values r - 1 := by
  funext r
  by_cases hr : r = lane <;> simp [decrementValues, hr]

theorem decrementCells_of_value_zero (lane : R) {cells : List (R → Bool)} {values : R → Nat}
    (h : Represents cells values) (hz : values lane = 0) : decrementCells lane cells = cells := by
  cases cells with
  | nil => rfl
  | cons cell cells =>
    have hFirst := ((represents_cons_iff cell cells values).mp h).1 lane
    simp [hz] at hFirst
    simp [decrementCells, hFirst]

theorem Represents.decrement (lane : R) {cells : List (R → Bool)} {values : R → Nat}
    (h : Represents cells values) :
    Represents (decrementCells lane cells) (decrementValues lane values) := by
  induction cells generalizing values with
  | nil =>
    have hz := (represents_nil_iff values).mp h lane
    rw [decrementValues_unchanged lane values hz]
    exact h
  | cons cell cells ih =>
    obtain ⟨head, tail⟩ := (represents_cons_iff cell cells values).mp h
    cases hFirst : cell lane with
    | false =>
      have hz := Nat.eq_zero_of_not_pos (of_decide_eq_false ((head lane).symm.trans hFirst))
      rw [decrementCells_of_value_zero lane h hz, decrementValues_unchanged lane values hz]
      exact h
    | true =>
      cases hNext : readLane cells 0 lane with
      | false =>
        have hz := Nat.eq_zero_of_not_pos (of_decide_eq_false ((tail 0 lane).symm.trans hNext))
        simp only [decrementCells, hFirst, hNext, Bool.false_eq_true, ite_true, ite_false]
        refine (represents_cons_iff ..).mpr ⟨fun r ↦ ?_, ?_⟩
        · by_cases hr : r = lane
          · subst r
            simp [decrementValues, hz]
          · simpa only [setTrack_other _ _ _ _ hr, decrementValues, ite_eq_right hr] using head r
        · rw [← decrementValues_shift, decrementValues_unchanged lane (fun r ↦ values r - 1) hz]
          exact tail
      | true =>
        have hpos := of_decide_eq_true ((tail 0 lane).symm.trans hNext)
        simp only [decrementCells, hFirst, hNext, ite_true]
        refine (represents_cons_iff ..).mpr ⟨fun r ↦ ?_, ?_⟩
        · by_cases hr : r = lane
          · subst r
            simp [decrementValues, hFirst, hpos]
          · simpa only [decrementValues, ite_eq_right hr] using head r
        · rw [← decrementValues_shift]
          exact ih tail

private theorem decrementCells_at_boundary (lane : R) (before : List (R → Bool))
    (last : R → Bool) (suffix : List (R → Bool))
    (hBefore : ∀ c ∈ before, c lane = true) (hLast : last lane = true)
    (hStop : readLane suffix 0 lane = false) :
    decrementCells lane (before ++ last :: suffix) =
      before ++ setTrack last lane false :: suffix := by
  induction before with
  | nil => simp [decrementCells, hLast, hStop]
  | cons first before ih =>
    have hFirst := hBefore first (List.mem_cons_self ..)
    have hBefore' : ∀ c ∈ before, c lane = true :=
      fun c hc ↦ hBefore c (List.mem_cons_of_mem _ hc)
    have hNext : readLane (before ++ last :: suffix) 0 lane = true := by
      cases before with
      | nil => exact hLast
      | cons next rest => exact hBefore' next (List.mem_cons_self ..)
    simp [decrementCells, hFirst, hNext, ih hBefore']

omit [DecidableEq R] in
private theorem split_at_first_false (lane : R) (cells : List (R → Bool)) :
    ∃ crossed suffix, cells = crossed ++ suffix ∧
      (∀ c ∈ crossed, c lane = true) ∧ readLane suffix 0 lane = false := by
  classical
  rcases incrementCells_split lane cells with ⟨crossed, cell, suffix, hl, hp, hc, _⟩ | ⟨hp, _⟩
  · exact ⟨crossed, cell :: suffix, hl, hp, hc⟩
  · exact ⟨cells, [], (List.append_nil _).symm, hp, rfl⟩

open Turing

variable {Q : Type} [Finite R] [Finite Q]
  {delta : Q → Symbol R → (Q ⊕ Bool) × Symbol R × Dir}

/-- The physical decrement branches on zero and implements the saturated lane update. -/
theorem run_decrement (initial : Q) {lane : R} (rules : DecrementRules delta lane)
    (left : List (Symbol R)) {cells : List (R → Bool)} {values : R → Nat}
    (h : Represents cells values) :
    let M := host initial delta
    M.run (if values lane = 0 then 2 else 2 * values lane + 4)
        ⟨.inl rules.entry, M.tapeFromLists left (.home :: trackTape cells)⟩ =
      ⟨.inl (if values lane = 0 then rules.zero else rules.next),
        M.tapeFromLists left (.home :: trackTape (decrementCells lane cells))⟩ := by
  dsimp only
  obtain ⟨crossed, suffix, rfl, hCrossed, hStop⟩ := split_at_first_false lane cells
  have hValue := h.value_eq_prefix lane hCrossed hStop
  rcases List.eq_nil_or_concat' crossed with rfl | ⟨before, last, rfl⟩
  · simp only [List.nil_append] at h ⊢
    have hz : values lane = 0 := hValue
    rw [decrementCells_of_value_zero lane h hz, ite_eq_left hz, ite_eq_left hz]
    cases suffix with
    | nil => exact run_decrement_zero_blank initial rules left
    | cons first rest => exact run_decrement_zero_cell initial rules left first rest hStop
  · have hBefore : ∀ c ∈ before, c lane = true :=
      fun c hc ↦ hCrossed c (List.mem_append_left _ hc)
    have hLast : last lane = true := hCrossed last (by simp)
    simp only [List.length_append, List.length_singleton] at hValue
    have hpos : values lane ≠ 0 := by omega
    rw [ite_eq_right hpos, ite_eq_right hpos, hValue, show 2 * (before.length + 1) + 4 =
      2 * before.length + 6 by omega]
    simp only [List.append_assoc, List.singleton_append]
    rw [decrementCells_at_boundary lane before last suffix hBefore hLast hStop]
    cases suffix with
    | nil => exact run_decrement_positive_blank initial rules left before last hBefore hLast
    | cons first rest =>
      exact run_decrement_positive_cell initial rules left before last first rest hBefore hLast
        hStop

end PvsNP.RegisterMachine
