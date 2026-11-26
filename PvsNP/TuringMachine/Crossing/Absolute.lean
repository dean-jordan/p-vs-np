module

public import PvsNP.TuringMachine.OutputBound
public import PvsNP.TuringMachine.TrackCall.Tracks

/-! # Absolute tape coordinates for crossing sequences -/

@[expose] public section

namespace PvsNP.Machine

open Turing TrackCall

variable {α : Type} (M : Machine α)

/-- The state, absolute head coordinate, and absolute tape contents. -/
structure AbsoluteConfig where
  state : M.State ⊕ Bool
  position : Int
  tape : Int → M.Symbol

/-- Lift a relative Cook configuration at the given head coordinate. -/
def absoluteAt (pos : Int) (c : M.Config) : M.AbsoluteConfig :=
  ⟨c.state, pos, fun i ↦ @Tape.nth _ M.tapeInhabited c.tape (i - pos)⟩

def absoluteStart (word : List α) : M.AbsoluteConfig := M.absoluteAt 0 (M.start word)

def absoluteTick (c : M.AbsoluteConfig) : M.AbsoluteConfig :=
  match c.state with
  | .inr _ => c
  | .inl q =>
    let (next, written, dir) := M.transition q (c.tape c.position)
    ⟨next, c.position + delta dir, fun i ↦ if i = c.position then written else c.tape i⟩

def absoluteRun : Nat → M.AbsoluteConfig → M.AbsoluteConfig
  | 0, c => c
  | n + 1, c => absoluteRun n (M.absoluteTick c)

theorem absoluteRun_add (m n : Nat) (c : M.AbsoluteConfig) :
    M.absoluteRun (m + n) c = M.absoluteRun n (M.absoluteRun m c) := by
  induction m generalizing c with
  | zero => rw [Nat.zero_add]; rfl
  | succ m ih => rw [Nat.succ_add]; exact ih (M.absoluteTick c)

/-- A cut separates squares below `cut` from all other squares. A crossing
records the state entered by the move, including a transition into a halt. -/
def crossingTranscript (cut : Int) : Nat → M.AbsoluteConfig → List (M.State ⊕ Bool)
  | 0, _ => []
  | n + 1, c =>
    let next := M.absoluteTick c
    let rest := crossingTranscript cut n next
    if (c.position < cut ↔ next.position < cut) then rest else next.state :: rest

/-- Join the left contents of `a` to the right contents of `b`. Select the
head and state on the common side of the cut when both heads are on that side. -/
def spliceConfig (cut : Int) (a b : M.AbsoluteConfig) : M.AbsoluteConfig :=
  let active := if a.position < cut then a else b
  ⟨active.state, active.position, fun i ↦ if i < cut then a.tape i else b.tape i⟩

theorem absoluteTick_tape_of_ne (c : M.AbsoluteConfig) {i : Int} (h : i ≠ c.position) :
    (M.absoluteTick c).tape i = c.tape i := by
  cases hs : c.state with
  | inr b => simp [absoluteTick, hs]
  | inl q =>
    rcases ht : M.transition q (c.tape c.position) with ⟨next, written, dir⟩
    simp [absoluteTick, hs, ht, h]

theorem absoluteTick_position_le (c : M.AbsoluteConfig) :
    c.position - 1 ≤ (M.absoluteTick c).position ∧
      (M.absoluteTick c).position ≤ c.position + 1 := by
  cases hs : c.state with
  | inr b => simp only [absoluteTick, hs]; omega
  | inl q =>
    rcases ht : M.transition q (c.tape c.position) with ⟨next, written, dir⟩
    cases dir <;> simp only [absoluteTick, hs, ht, delta] <;> omega

theorem absoluteTick_absoluteAt (pos : Int) (c : M.Config) :
    M.absoluteTick (M.absoluteAt pos c) =
      M.absoluteAt (M.absoluteTick (M.absoluteAt pos c)).position (M.tick c) := by
  let _ := M.tapeInhabited
  rcases c with ⟨state, tape⟩
  cases state with
  | inr b => rfl
  | inl q =>
    rcases ht : M.transition q tape.head with ⟨next, written, dir⟩
    simp only [absoluteTick, absoluteAt, Int.sub_self, Tape.nth_zero, tick, ht]
    congr 1
    funext i
    rw [move_nth_delta, show i - (pos + delta dir) + delta dir = i - pos by omega,
      Tape.write_nth]
    by_cases h : i = pos
    · subst i; simp
    · rw [ite_eq_right h, ite_eq_right (by omega)]

theorem absoluteRun_absoluteAt (n : Nat) (pos : Int) (c : M.Config) :
    M.absoluteRun n (M.absoluteAt pos c) =
      M.absoluteAt (M.absoluteRun n (M.absoluteAt pos c)).position (M.run n c) := by
  induction n generalizing pos c with
  | zero => rfl
  | succ n ih =>
    change M.absoluteRun n (M.absoluteTick (M.absoluteAt pos c)) =
      M.absoluteAt (M.absoluteRun n (M.absoluteTick (M.absoluteAt pos c))).position
        (M.run n (M.tick c))
    rw [M.absoluteTick_absoluteAt pos c]
    exact ih _ _

theorem absoluteRun_start_state (n : Nat) (word : List α) :
    (M.absoluteRun n (M.absoluteStart word)).state = (M.run n (M.start word)).state :=
  congrArg AbsoluteConfig.state (M.absoluteRun_absoluteAt n 0 (M.start word))

theorem absoluteStart_tape (word : List α) (i : Int) :
    (M.absoluteStart word).tape i =
      if i < 0 then M.blank else ((word.map M.input)[i.toNat]?).getD M.blank := by
  let _ := M.tapeInhabited
  change (Tape.mk₁ (word.map M.input)).nth (i - 0) = _
  rw [Int.sub_zero]
  cases i with
  | ofNat i =>
    change (Tape.mk₁ (word.map M.input)).nth (i : Int) =
      if (i : Int) < 0 then M.blank else ((word.map M.input)[i]?).getD M.blank
    rw [ite_eq_right (Int.not_lt.mpr (Int.natCast_nonneg i)), mk₁_nth_nat,
      List.getI_eq_getElem?_getD]
    rfl
  | negSucc i =>
    rw [ite_eq_left (by omega)]
    simp [Tape.mk₁, Tape.mk₂, Tape.nth, Tape.mk']
    rfl

end PvsNP.Machine
