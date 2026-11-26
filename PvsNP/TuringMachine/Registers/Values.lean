module

public import PvsNP.TuringMachine.Registers.Alphabet

/-! # Unary register semantics for the packed tape

Each lane represents its value by an initial run of true bits. Omitted
cells read as false. Adding a cell for one lane leaves all other lanes
unchanged.
-/

@[expose] public section

namespace PvsNP.RegisterMachine

variable {R : Type}

/-- Read a lane at a tape position, with implicit false bits past the stored cells. -/
def readLane (cells : List (R → Bool)) (i : Nat) (lane : R) : Bool :=
  (cells[i]?.map fun cell ↦ cell lane).getD false

/-- Each register occupies a prefix of its lane. -/
def Represents (cells : List (R → Bool)) (values : R → Nat) : Prop :=
  ∀ i lane, readLane cells i lane = decide (i < values lane)

theorem represents_nil_iff (values : R → Nat) :
    Represents [] values ↔ ∀ r, values r = 0 := by
  constructor
  · intro h r
    have hzero : decide (0 < values r) = false := (h 0 r).symm
    exact Nat.eq_zero_of_not_pos (of_decide_eq_false hzero)
  · intro h i r
    simp [readLane, h r]

theorem represents_cons_iff (cell : R → Bool) (cells : List (R → Bool)) (values : R → Nat) :
    Represents (cell :: cells) values ↔
      (∀ r, cell r = decide (0 < values r)) ∧ Represents cells (fun r ↦ values r - 1) := by
  constructor
  · intro h
    refine ⟨fun r ↦ h 0 r, fun i r ↦ ?_⟩
    have shift : i + 1 < values r ↔ i < values r - 1 := by omega
    simpa only [readLane, List.getElem?_cons_succ, shift] using h (i + 1) r
  · rintro ⟨hHead, hTail⟩ i r
    cases i with
    | zero => exact hHead r
    | succ i =>
      have shift : i < values r - 1 ↔ i + 1 < values r := by omega
      simpa only [readLane, List.getElem?_cons_succ, shift] using hTail i r

theorem Represents.value_le_length {cells : List (R → Bool)} {values : R → Nat}
    (h : Represents cells values) (lane : R) : values lane ≤ cells.length := by
  have ht := h cells.length lane
  simp only [readLane, List.getElem?_eq_none (Nat.le_refl _), Option.map_none, Option.getD_none,
    Bool.false_eq] at ht
  exact Nat.le_of_not_gt (of_decide_eq_false ht)

/-- An all-true segment followed by a false bit has length equal to the register value. -/
theorem Represents.value_eq_prefix {crossed suffix : List (R → Bool)} {values : R → Nat}
    (h : Represents (crossed ++ suffix) values) (lane : R)
    (hCrossed : ∀ cell ∈ crossed, cell lane = true) (hStop : readLane suffix 0 lane = false) :
    values lane = crossed.length := by
  induction crossed generalizing values with
  | nil =>
    have hz : decide (0 < values lane) = false := (h 0 lane).symm.trans hStop
    exact Nat.eq_zero_of_not_pos (of_decide_eq_false hz)
  | cons cell crossed ih =>
    obtain ⟨head, tail⟩ := (represents_cons_iff cell (crossed ++ suffix) values).mp h
    have hpos : 0 < values lane := of_decide_eq_true
      ((head lane).symm.trans (hCrossed cell (List.mem_cons_self ..)))
    have hPrev := ih tail fun c hc ↦ hCrossed c (List.mem_cons_of_mem _ hc)
    simp only [List.length_cons] at *
    omega

/-- Increment one abstract register. -/
def incrementValues [DecidableEq R] (lane : R) (values : R → Nat) : R → Nat :=
  fun r ↦ if r = lane then values r + 1 else values r

/-- The cell update performed by scanning to the first false bit in the lane. -/
def incrementCells [DecidableEq R] (lane : R) : List (R → Bool) → List (R → Bool)
  | [] => [setTrack (fun _ ↦ false) lane true]
  | cell :: cells =>
    if cell lane then cell :: incrementCells lane cells else setTrack cell lane true :: cells

theorem length_incrementCells_le [DecidableEq R] (lane : R) (cells : List (R → Bool)) :
    (incrementCells lane cells).length ≤ cells.length + 1 := by
  induction cells with
  | nil => simp [incrementCells]
  | cons cell cells ih =>
    by_cases h : cell lane
    · simp [incrementCells, h, ih]
    · simp [incrementCells, h]

theorem Represents.increment [DecidableEq R] (lane : R)
    {cells : List (R → Bool)} {values : R → Nat} (h : Represents cells values) :
    Represents (incrementCells lane cells) (incrementValues lane values) := by
  induction cells generalizing values with
  | nil =>
    have zeros := (represents_nil_iff values).mp h
    unfold incrementCells
    apply (represents_cons_iff ..).mpr
    refine ⟨fun r ↦ ?_, (represents_nil_iff _).mpr fun r ↦ ?_⟩
    · by_cases hr : r = lane
      · subst r
        simp [incrementValues]
      · simp [setTrack_other _ _ _ _ hr, incrementValues, hr, zeros r]
    · by_cases hr : r = lane <;> simp [incrementValues, hr, zeros]
  | cons cell cells ih =>
    obtain ⟨head, tail⟩ := (represents_cons_iff cell cells values).mp h
    by_cases hbit : cell lane = true
    · have hpos : 0 < values lane := of_decide_eq_true ((head lane).symm.trans hbit)
      rw [incrementCells, ite_eq_left hbit]
      apply (represents_cons_iff ..).mpr
      refine ⟨fun r ↦ ?_, ?_⟩
      · by_cases hr : r = lane
        · subst r
          simp [incrementValues, hbit]
        · simpa only [incrementValues, ite_eq_right hr] using head r
      · have hValues : incrementValues lane (fun r ↦ values r - 1) =
            fun r ↦ incrementValues lane values r - 1 := by
          funext r
          by_cases hr : r = lane
          · subst r
            simp only [incrementValues, ite_true]
            omega
          · simp [incrementValues, hr]
        exact hValues ▸ ih tail
    · have hz : values lane = 0 := by
        have ht := head lane
        cases hc : cell lane with
        | false => exact Nat.eq_zero_of_not_pos (of_decide_eq_false (ht.symm.trans hc))
        | true => exact (hbit hc).elim
      rw [incrementCells, ite_eq_right hbit]
      apply (represents_cons_iff ..).mpr
      refine ⟨fun r ↦ ?_, ?_⟩
      · by_cases hr : r = lane
        · subst r
          simp [incrementValues, hz]
        · simpa only [setTrack_other _ _ _ _ hr, incrementValues, ite_eq_right hr] using head r
      · have hValues : (fun r ↦ values r - 1) =
            fun r ↦ incrementValues lane values r - 1 := by
          funext r
          by_cases hr : r = lane
          · subst r
            simp [incrementValues, hz]
          · simp [incrementValues, hr]
        exact hValues ▸ tail

/-- The scan reaches either a false bit in the stored cells or the implicit blank. -/
theorem incrementCells_split [DecidableEq R] (lane : R) (cells : List (R → Bool)) :
    (∃ crossed cell suffix, cells = crossed ++ cell :: suffix ∧
      (∀ a ∈ crossed, a lane = true) ∧ cell lane = false ∧
      incrementCells lane cells = crossed ++ setTrack cell lane true :: suffix) ∨
    ((∀ a ∈ cells, a lane = true) ∧
      incrementCells lane cells = cells ++ [setTrack (fun _ ↦ false) lane true]) := by
  induction cells with
  | nil => exact Or.inr ⟨by simp, rfl⟩
  | cons cell cells ih =>
    cases h : cell lane with
    | false => exact Or.inl ⟨[], cell, cells, rfl, by simp, h, by simp [incrementCells, h]⟩
    | true =>
      rcases ih with ⟨crossed, next, suffix, rfl, hp, hn, hi⟩ | ⟨hp, hi⟩
      · refine Or.inl ⟨cell :: crossed, next, suffix, rfl, ?_, hn, ?_⟩
        · intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · exact h
          · exact hp a ha
        · simp [incrementCells, h, hi]
      · refine Or.inr ⟨?_, ?_⟩
        · intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · exact h
          · exact hp a ha
        · simp [incrementCells, h, hi]

end PvsNP.RegisterMachine
