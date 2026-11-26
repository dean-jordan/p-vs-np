module

public import PvsNP.TuringMachine.Core

import PvsNP.TuringMachine.OutputBound

/-!
# Finite tape windows for bounded computations

A fixed window stores absolute tape coordinates, while the reference tape is
indexed relative to the current head. A window containing every position within
the time budget simulates the reference machine one tick at a time.
-/

@[expose] public section

namespace PvsNP.Machine

variable {α : Type} (M : Machine α)

/-- A finite row of the computation, indexed by absolute tape position. -/
structure WindowConfig (w : Nat) where
  state : M.State ⊕ Bool
  head : Fin w
  cells : Fin w → M.Symbol

/-- Move one cell, staying at the endpoint if the move would leave the window. -/
def windowMoveHead {w : Nat} (dir : Turing.Dir) (head : Fin w) : Fin w :=
  match dir with
  | .left => ⟨head.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le ..) head.isLt⟩
  | .right => if h : head.val + 1 < w then ⟨head.val + 1, h⟩ else head

/-- The next state, next head, and symbol to write at the old head position. -/
def windowAdvance (w : Nat) (state : M.State ⊕ Bool) (head : Fin w) (read : M.Symbol) :
    (M.State ⊕ Bool) × Fin w × M.Symbol :=
  match state with
  | .inr b => ⟨.inr b, head, read⟩
  | .inl q =>
    let ⟨next, written, dir⟩ := M.transition q read
    ⟨next, windowMoveHead dir head, written⟩

/-- Perform the local update, retaining every cell other than the old head. -/
def windowTick {w : Nat} (c : M.WindowConfig w) : M.WindowConfig w :=
  let next := M.windowAdvance w c.state c.head (c.cells c.head)
  ⟨next.1, next.2.1, fun i ↦ if i = c.head then next.2.2 else c.cells i⟩

/-- Iterate the update on a finite tape window. -/
def windowRun {w : Nat} : Nat → M.WindowConfig w → M.WindowConfig w
  | 0, c => c
  | t + 1, c => M.windowTick (windowRun t c)

@[simp] theorem windowRun_zero {w : Nat} (c : M.WindowConfig w) : M.windowRun 0 c = c := rfl

theorem windowRun_succ {w : Nat} (t : Nat) (c : M.WindowConfig w) :
    M.windowRun (t + 1) c = M.windowTick (M.windowRun t c) := rfl

theorem windowRun_succ_first {w : Nat} (t : Nat) (c : M.WindowConfig w) :
    M.windowRun (t + 1) c = M.windowRun t (M.windowTick c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [windowRun_succ, ih, windowRun_succ]

/-- Read the reference tape at the positions within the absolute window. -/
def windowProject {w : Nat} (head : Fin w) (c : M.Config) : M.WindowConfig w :=
  ⟨c.state, head, fun i ↦ @Turing.Tape.nth _ M.tapeInhabited c.tape ((i.val : Int) - head.val)⟩

theorem windowProject_cells {w : Nat} (head i : Fin w) (c : M.Config) :
    (M.windowProject head c).cells i =
      @Turing.Tape.nth _ M.tapeInhabited c.tape ((i.val : Int) - head.val) := rfl

/-- The restriction of the reference initial configuration to a window. -/
def windowStart {w : Nat} (head : Fin w) (x : List α) : M.WindowConfig w :=
  M.windowProject head (M.start x)

/-- The initial window contains the input to the right of the starting position and blanks
outside that interval. -/
theorem windowStart_cells_ofFn {w n : Nat} (head i : Fin w) (x : Fin n → α) :
    (M.windowStart head (List.ofFn x)).cells i =
      if h : head.val ≤ i.val ∧ i.val - head.val < n then
        M.input (x ⟨i.val - head.val, h.2⟩) else M.blank := by
  let _ := M.tapeInhabited
  change (Turing.Tape.mk₁ ((List.ofFn x).map M.input)).nth ((i.val : Int) - head.val) = _
  by_cases hLeft : head.val ≤ i.val
  · have hPos : (i.val : Int) - head.val = ((i.val - head.val : Nat) : Int) := by omega
    rw [hPos, mk₁_nth_nat]
    by_cases hInside : i.val - head.val < n
    · rw [dite_eq_left ⟨hLeft, hInside⟩, List.getI_eq_getElem _ (by simpa using hInside),
        List.getElem_map, List.getElem_ofFn]
    · rw [dite_eq_right (fun h ↦ hInside h.2), List.getI_eq_default _ (by simpa using hInside)]
      rfl
  · rw [dite_eq_right (fun h ↦ hLeft h.1)]
    cases hIndex : (i.val : Int) - head.val with
    | ofNat d =>
      change (i.val : Int) - (head.val : Int) = (d : Int) at hIndex
      omega
    | negSucc d =>
      simp [Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.nth, Turing.Tape.mk',
        Turing.ListBlank.nth_mk]
      rfl

/-- The initial head for a window with room for `T` moves in either direction. -/
def windowCenter (T : Nat) : Fin (2 * T + 1) := ⟨T, by omega⟩

private theorem moveHead_bounds {w : Nat} (dir : Turing.Dir) (head : Fin w) :
    head.val ≤ (windowMoveHead dir head).val + 1 ∧
      (windowMoveHead dir head).val ≤ head.val + 1 := by
  cases dir with
  | left =>
    simp only [windowMoveHead]
    omega
  | right =>
    by_cases h : head.val + 1 < w
    · simp only [windowMoveHead, dite_eq_left h]
      omega
    · simp only [windowMoveHead, dite_eq_right h]
      omega

/-- In one tick the head's absolute position changes by at most one. -/
theorem windowTick_head_bounds {w : Nat} (c : M.WindowConfig w) :
    c.head.val ≤ (M.windowTick c).head.val + 1 ∧
      (M.windowTick c).head.val ≤ c.head.val + 1 := by
  rcases hstate : c.state with q | b
  · rcases hstep : M.transition q (c.cells c.head) with ⟨q', s, dir⟩
    simpa only [windowTick, windowAdvance, hstate, hstep] using moveHead_bounds dir c.head
  · simp [windowTick, windowAdvance, hstate]

/-- After `t` steps the head can be at most `t` cells to the right of its start. -/
theorem windowRun_head_le {w : Nat} (t : Nat) (c : M.WindowConfig w) :
    (M.windowRun t c).head.val ≤ c.head.val + t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [windowRun_succ]
    have h := (M.windowTick_head_bounds (M.windowRun t c)).2
    omega

private theorem windowCell_write_move {w : Nat} (tape : M.Tape) (s : M.Symbol)
    (dir : Turing.Dir) (head i : Fin w) (hleft : 0 < head.val) (hright : head.val + 1 < w) :
    letI := M.tapeInhabited
    ((tape.write s).move dir).nth ((i.val : Int) - (windowMoveHead dir head).val) =
      if i = head then s else tape.nth ((i.val : Int) - head.val) := by
  have hzero : (i.val : Int) - head.val = 0 ↔ i = head := by
    constructor
    · intro h
      apply Fin.ext
      omega
    · rintro rfl
      exact Int.sub_self _
  cases dir with
  | left =>
    have hpos : (i.val : Int) - (windowMoveHead .left head).val - 1 =
        (i.val : Int) - head.val := by
      simp only [windowMoveHead]
      omega
    simp only [Turing.Tape.move_left_nth, hpos, Turing.Tape.write_nth, hzero]
  | right =>
    have hpos : (i.val : Int) - (windowMoveHead .right head).val + 1 =
        (i.val : Int) - head.val := by
      simp only [windowMoveHead, dite_eq_left hright]
      omega
    simp only [Turing.Tape.move_right_nth, hpos, Turing.Tape.write_nth, hzero]

/-- A tick agrees with the reference machine whenever both adjacent cells are present. -/
theorem windowTick_project {w : Nat} (head : Fin w) (c : M.Config)
    (hleft : 0 < head.val) (hright : head.val + 1 < w) :
    M.windowTick (M.windowProject head c) =
      M.windowProject (M.windowTick (M.windowProject head c)).head (M.tick c) := by
  rcases c with ⟨state, tape⟩
  cases state with
  | inl q =>
    rcases hstep : M.transition q (@Turing.Tape.head _ M.tapeInhabited tape) with ⟨q', s, dir⟩
    simp only [windowTick, windowAdvance, windowProject, tick, Int.sub_self, Turing.Tape.nth_zero,
      hstep, WindowConfig.mk.injEq, true_and]
    exact funext fun i ↦ (M.windowCell_write_move tape s dir head i hleft hright).symm
  | inr b =>
    simp only [windowTick, windowAdvance, windowProject, tick_halted, WindowConfig.mk.injEq,
      true_and]
    funext i
    by_cases h : i = head
    · subst i
      exact ite_eq_left rfl
    · exact ite_eq_right h

/-- With `t` cells of room on each side, `t` finite ticks reproduce the reference run. -/
theorem windowRun_project {w : Nat} (t : Nat) (head : Fin w) (c : M.Config)
    (hleft : t ≤ head.val) (hright : head.val + t < w) :
    ∃ h : Fin w, M.windowRun t (M.windowProject head c) = M.windowProject h (M.run t c) := by
  induction t generalizing head c with
  | zero => exact ⟨head, rfl⟩
  | succ t ih =>
    let next := M.windowTick (M.windowProject head c)
    have hstep : next = M.windowProject next.head (M.tick c) :=
      M.windowTick_project head c (by omega) (by omega)
    obtain ⟨hl, hr⟩ := M.windowTick_head_bounds (M.windowProject head c)
    change head.val ≤ next.head.val + 1 at hl
    change next.head.val ≤ head.val + 1 at hr
    rw [windowRun_succ_first, run_succ]
    change ∃ h, M.windowRun t next = M.windowProject h (M.run t (M.tick c))
    rw [hstep]
    exact ih next.head (M.tick c) (by omega) (by omega)

/-- A centered window with `2 * T + 1` cells preserves the state through time `T`. -/
theorem windowRun_start_state (T t : Nat) (h : t ≤ T) (x : List α) :
    (M.windowRun t (M.windowStart (windowCenter T) x)).state =
      (M.run t (M.start x)).state := by
  obtain ⟨head, hproject⟩ := M.windowRun_project t (windowCenter T) (M.start x)
    (by simpa only [windowCenter] using h) (by simp only [windowCenter]; omega)
  exact congrArg WindowConfig.state hproject

end PvsNP.Machine
