module

public import PvsNP.TuringMachine.Core

/-! # Counted tape sweeps

A tape zipper lists the cells to the left in nearest-first order and starts
the right list at the scanned cell. A sweep moves across a finite segment,
leaving each scanned symbol and the running state unchanged.
-/

@[expose] public section

namespace PvsNP.Machine

open Turing

variable {α : Type} (M : Machine α)

/-- The left list is nearest-first and the right list includes the head. -/
abbrev tapeFromLists (left right : List M.Symbol) : M.Tape :=
  @Tape.mk₂ M.Symbol M.tapeInhabited left right

theorem head_tapeFromLists_cons (left right : List M.Symbol) (a : M.Symbol) :
    @Tape.head _ M.tapeInhabited (M.tapeFromLists left (a :: right)) = a := rfl

theorem head_tapeFromLists_nil (left : List M.Symbol) :
    @Tape.head _ M.tapeInhabited (M.tapeFromLists left []) = M.blank := rfl

/-- An explicit blank at the right end represents the same infinite tape. -/
theorem tapeFromLists_append_blank (left right : List M.Symbol) :
    M.tapeFromLists left (right ++ [M.blank]) = M.tapeFromLists left right := by
  have h : @ListBlank.mk _ M.tapeInhabited (right ++ [M.blank]) =
      @ListBlank.mk _ M.tapeInhabited right := Quotient.sound (Or.inr ⟨1, rfl⟩)
  exact congrArg (@Tape.mk' _ M.tapeInhabited (@ListBlank.mk _ M.tapeInhabited left)) h

theorem tapeFromLists_right_blank (left : List M.Symbol) :
    M.tapeFromLists left [M.blank] = M.tapeFromLists left [] :=
  M.tapeFromLists_append_blank left []

theorem move_tapeFromLists_right_cons (left right : List M.Symbol) (a : M.Symbol) :
    @Tape.move _ M.tapeInhabited .right (M.tapeFromLists left (a :: right)) =
      M.tapeFromLists (a :: left) right := by
  simp [Tape.mk₂, ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk]

theorem move_tapeFromLists_right_nil (left : List M.Symbol) :
    @Tape.move _ M.tapeInhabited .right (M.tapeFromLists left []) =
      M.tapeFromLists (M.blank :: left) [] := by
  simp [Tape.mk₂, ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk]
  rfl

theorem move_tapeFromLists_left_cons (left right : List M.Symbol) (a : M.Symbol) :
    @Tape.move _ M.tapeInhabited .left (M.tapeFromLists (a :: left) right) =
      M.tapeFromLists left (a :: right) := by
  simp [Tape.mk₂, ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk]

theorem move_tapeFromLists_left_nil (right : List M.Symbol) :
    @Tape.move _ M.tapeInhabited .left (M.tapeFromLists [] right) =
      M.tapeFromLists [] (M.blank :: right) := by
  simp [Tape.mk₂, ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk]
  rfl

theorem write_tapeFromLists_cons (left right : List M.Symbol) (a b : M.Symbol) :
    @Tape.write _ M.tapeInhabited b (M.tapeFromLists left (a :: right)) =
      M.tapeFromLists left (b :: right) := by
  simp [Tape.mk₂, ListBlank.tail_mk, ListBlank.cons_mk]

theorem write_tapeFromLists_nil (left : List M.Symbol) (b : M.Symbol) :
    @Tape.write _ M.tapeInhabited b (M.tapeFromLists left []) =
      M.tapeFromLists left [b] := by
  simp [Tape.mk₂, ListBlank.tail_mk, ListBlank.cons_mk]

theorem tick_tapeFromLists_cons (q : M.State) (left right : List M.Symbol)
    (a : M.Symbol) {q' : M.State ⊕ Bool} {b : M.Symbol} {dir : Dir}
    (h : M.transition q a = (q', b, dir)) :
    M.tick ⟨.inl q, M.tapeFromLists left (a :: right)⟩ =
      ⟨q', @Tape.move _ M.tapeInhabited dir (M.tapeFromLists left (b :: right))⟩ := by
  simp only [tick, head_tapeFromLists_cons, h, write_tapeFromLists_cons]

theorem tick_tapeFromLists_nil (q : M.State) (left : List M.Symbol)
    {q' : M.State ⊕ Bool} {b : M.Symbol} {dir : Dir}
    (h : M.transition q M.blank = (q', b, dir)) :
    M.tick ⟨.inl q, M.tapeFromLists left []⟩ =
      ⟨q', @Tape.move _ M.tapeInhabited dir (M.tapeFromLists left [b])⟩ := by
  simp only [tick, head_tapeFromLists_nil, h, write_tapeFromLists_nil]

/-- A right sweep crosses the segment in one tick per symbol. -/
theorem run_sweep_right (q : M.State) (crossed left right : List M.Symbol)
    (hs : ∀ s ∈ crossed, M.transition q s = (.inl q, s, .right)) :
    M.run crossed.length ⟨.inl q, M.tapeFromLists left (crossed ++ right)⟩ =
      ⟨.inl q, M.tapeFromLists (crossed.reverse ++ left) right⟩ := by
  induction crossed generalizing left with
  | nil => rfl
  | cons a crossed ih =>
    simp only [List.length_cons, List.cons_append, run_succ,
      tick_tapeFromLists_cons M q left (crossed ++ right) a (hs a (List.mem_cons_self ..)),
      move_tapeFromLists_right_cons]
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
      ih (a :: left) (fun s h ↦ hs s (List.mem_cons_of_mem _ h))

/-- A left sweep starts just left of the given right context and crosses the
segment in nearest-first order, in one tick per symbol. -/
theorem run_sweep_left (q : M.State) (crossed left right : List M.Symbol)
    (hs : ∀ s ∈ crossed, M.transition q s = (.inl q, s, .left)) :
    M.run crossed.length
      ⟨.inl q, @Tape.move _ M.tapeInhabited .left (M.tapeFromLists (crossed ++ left) right)⟩ =
      ⟨.inl q, @Tape.move _ M.tapeInhabited .left
        (M.tapeFromLists left (crossed.reverse ++ right))⟩ := by
  induction crossed generalizing right with
  | nil => rfl
  | cons a crossed ih =>
    simp only [List.length_cons, List.cons_append, run_succ, move_tapeFromLists_left_cons,
      tick_tapeFromLists_cons M q (crossed ++ left) right a (hs a (List.mem_cons_self ..))]
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
      ih (a :: right) (fun s h ↦ hs s (List.mem_cons_of_mem _ h))

end PvsNP.Machine
