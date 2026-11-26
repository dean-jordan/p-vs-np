module

public import Mathlib.Basic.Finite.Defs
public import Mathlib.Computability.TuringMachine.Tape

/-!
# Cook's deterministic Turing machines

Each transition writes a symbol and moves the head one square on a single tape.
Accept and reject are distinct from the running states. Computations count physical
transitions until the first halt. For bounded simulation, a halted configuration
is held fixed on subsequent clock ticks.
-/

@[expose] public section

namespace PvsNP

/-- The machine in Cook's appendix, with the two halting states tagged separately. -/
structure Machine (α : Type) where
  State : Type
  Symbol : Type
  stateFinite : Finite State
  symbolFinite : Finite Symbol
  initial : State
  blank : Symbol
  input : α ↪ Symbol
  input_ne_blank : ∀ a, input a ≠ blank
  transition : State → Symbol → (State ⊕ Bool) × Symbol × Turing.Dir

namespace Machine

variable {α : Type} (M : Machine α)

/-- Mathlib uses the distinguished inhabitant as the tape blank. -/
abbrev tapeInhabited : Inhabited M.Symbol := ⟨M.blank⟩

/-- A two-way infinite tape with finite nonblank support. -/
abbrev Tape := @Turing.Tape M.Symbol M.tapeInhabited

/-- A running state is `Sum.inl q`. A halting state is `Sum.inr b`, with `true` for accept. -/
structure Config where
  state : M.State ⊕ Bool
  tape : M.Tape

/-- The unique initial configuration, including a blank at the head on empty input. -/
def start (x : List α) : M.Config :=
  ⟨.inl M.initial, @Turing.Tape.mk₁ _ M.tapeInhabited (x.map M.input)⟩

/-- Take a physical transition from a running state or retain the halted configuration. -/
def tick (c : M.Config) : M.Config :=
  letI := M.tapeInhabited
  match c.state with
  | .inr _ => c
  | .inl q =>
    let ⟨q', s, dir⟩ := M.transition q c.tape.head
    ⟨q', (c.tape.write s).move dir⟩

/-- Iterate `tick` for the specified number of ticks. -/
def run : Nat → M.Config → M.Config
  | 0, c => c
  | n + 1, c => run n (M.tick c)

@[simp] theorem run_zero (c : M.Config) : M.run 0 c = c := rfl

theorem run_succ (n : Nat) (c : M.Config) : M.run (n + 1) c = M.run n (M.tick c) := rfl

theorem run_add (m n : Nat) (c : M.Config) :
    M.run (m + n) c = M.run n (M.run m c) := by
  induction m generalizing c with
  | zero => rw [Nat.zero_add, run_zero]
  | succ m ih => rw [Nat.succ_add, run_succ, ih, run_succ]

@[simp] theorem tick_halted (b : Bool) (tape : M.Tape) :
    M.tick ⟨.inr b, tape⟩ = ⟨.inr b, tape⟩ := rfl

@[simp] theorem run_halted (n : Nat) (b : Bool) (tape : M.Tape) :
    M.run n ⟨.inr b, tape⟩ = ⟨.inr b, tape⟩ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [run_succ, tick_halted, ih]

theorem run_eq_of_halted (n : Nat) (c : M.Config) {b : Bool}
    (h : c.state = .inr b) : M.run n c = c := by
  obtain ⟨state, tape⟩ := c
  change state = .inr b at h
  subst state
  exact M.run_halted n b tape

theorem run_eq_of_halted_le (c : M.Config) {m n : Nat} {b : Bool}
    (hmn : m ≤ n) (h : (M.run m c).state = .inr b) : M.run n c = M.run m c := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [run_add, M.run_eq_of_halted k _ h]

theorem halt_result_unique (c : M.Config) {m n : Nat} {a b : Bool}
    (ha : (M.run m c).state = .inr a) (hb : (M.run n c).state = .inr b) : a = b := by
  rcases Nat.le_total m n with h | h
  · rw [M.run_eq_of_halted_le c h ha, ha] at hb
    exact Sum.inr.inj hb
  · rw [M.run_eq_of_halted_le c h hb, hb] at ha
    exact (Sum.inr.inj ha).symm

/-- Acceptance means a finite computation reaches the accepting state. -/
def Accepts (x : List α) : Prop := ∃ n, (M.run n (M.start x)).state = .inr true

/-- A bound on physical transitions to either halting state. -/
def HaltsWithin (x : List α) (bound : Nat) : Prop :=
  ∃ n ≤ bound, ∃ b, (M.run n (M.start x)).state = .inr b

theorem haltsWithin_iff (x : List α) (bound : Nat) :
    M.HaltsWithin x bound ↔ ∃ b, (M.run bound (M.start x)).state = .inr b := by
  refine ⟨?_, fun ⟨b, hb⟩ ↦ ⟨bound, Nat.le_refl _, b, hb⟩⟩
  rintro ⟨n, hn, b, hb⟩
  exact ⟨b, (congrArg Config.state (M.run_eq_of_halted_le _ hn hb)).trans hb⟩

/-- A bounded halt has a first halting time, with a running state at every earlier tick. -/
theorem haltsWithin_iff_firstHalt (x : List α) (bound : Nat) :
    M.HaltsWithin x bound ↔ ∃ n ≤ bound, ∃ b,
      (M.run n (M.start x)).state = .inr b ∧
      ∀ m < n, ∃ q, (M.run m (M.start x)).state = .inl q := by
  refine ⟨?_, fun ⟨n, hn, b, hb, _⟩ ↦ ⟨n, hn, b, hb⟩⟩
  induction bound with
  | zero =>
    rintro ⟨n, hn, b, hb⟩
    rw [Nat.eq_zero_of_le_zero hn] at hb
    cases hb
  | succ bound ih =>
    intro h
    by_cases earlier : M.HaltsWithin x bound
    · obtain ⟨n, hn, b, hb, hrun⟩ := ih earlier
      exact ⟨n, Nat.le_trans hn (Nat.le_succ bound), b, hb, hrun⟩
    · obtain ⟨b, hb⟩ := (M.haltsWithin_iff x (bound + 1)).mp h
      refine ⟨bound + 1, Nat.le_refl _, b, hb, fun m hm ↦ ?_⟩
      cases stateEq : (M.run m (M.start x)).state with
      | inl q => exact ⟨q, rfl⟩
      | inr b => exact (earlier ⟨m, Nat.le_of_lt_succ hm, b, stateEq⟩).elim

theorem accepts_iff_at_bound (x : List α) {bound : Nat} (h : M.HaltsWithin x bound) :
    M.Accepts x ↔ (M.run bound (M.start x)).state = .inr true := by
  obtain ⟨b, hb⟩ := (M.haltsWithin_iff x bound).mp h
  refine ⟨?_, fun ht ↦ ⟨bound, ht⟩⟩
  rintro ⟨n, hn⟩
  rw [hb, M.halt_result_unique _ hb hn]

/-- Cook's worst-case bound, with a single exponent for all input strings and all lengths. -/
def PolyTime : Prop := ∃ k : Nat, ∀ x, M.HaltsWithin x (x.length ^ k + k)

/-- The accepted language is exactly `L`. Totality is expressed separately by `PolyTime`. -/
def Decides (L : Set (List α)) : Prop := ∀ x, x ∈ L ↔ M.Accepts x

/-- The finite string `u q a v` in Cook's appendix, with `a` the scanned symbol. -/
structure AppendixConfig where
  left : List M.Symbol
  state : M.State ⊕ Bool
  scanned : M.Symbol
  suffix : List M.Symbol

/-- The two initial configurations in Cook's appendix, for nonempty and empty input. -/
def appendixStart (x : List α) : M.AppendixConfig :=
  ⟨[], .inl M.initial, (x.map M.input).headD M.blank, (x.map M.input).tail⟩

/-- Cook's four transition cases. If a represented end is crossed, read a new blank cell. -/
def appendixTick (c : M.AppendixConfig) : M.AppendixConfig :=
  match c.state with
  | .inr _ => c
  | .inl q =>
    let ⟨q', s, dir⟩ := M.transition q c.scanned
    match dir with
    | .left => ⟨c.left.dropLast, q', c.left.getLastD M.blank, s :: c.suffix⟩
    | .right => ⟨c.left ++ [s], q', c.suffix.headD M.blank, c.suffix.tail⟩

/-- Represent the finite configuration on Mathlib's tape. -/
def AppendixConfig.toConfig (c : M.AppendixConfig) : M.Config :=
  ⟨c.state, @Turing.Tape.mk₂ _ M.tapeInhabited c.left.reverse (c.scanned :: c.suffix)⟩

theorem appendixStart_toConfig (x : List α) :
    (M.appendixStart x).toConfig M = M.start x := by
  cases x with
  | nil => rfl
  | cons a x => rfl

theorem appendixTick_toConfig (c : M.AppendixConfig) :
    (M.appendixTick c).toConfig M = M.tick (c.toConfig M) := by
  obtain ⟨left, state, scanned, suffix⟩ := c
  cases state with
  | inr b => rfl
  | inl q =>
    rcases value : M.transition q scanned with ⟨q', s, dir⟩
    cases dir
    · cases reversed : left.reverse with
      | nil =>
        have h : left = [] := by simpa using congrArg List.reverse reversed
        subst left
        simp [appendixTick, AppendixConfig.toConfig, tick, value, Turing.Tape.mk₂,
          Turing.Tape.mk', Turing.Tape.move]
        rfl
      | cons a rest =>
        have h : left = rest.reverse ++ [a] := by
          simpa only [List.reverse_reverse, List.reverse_cons] using congrArg List.reverse reversed
        subst left
        simp [appendixTick, AppendixConfig.toConfig, tick, value, Turing.Tape.mk₂,
          Turing.Tape.mk', Turing.Tape.move, List.reverse_append]
    · cases suffix <;> simp [appendixTick, AppendixConfig.toConfig, tick, value, Turing.Tape.mk₂,
        Turing.Tape.mk', Turing.Tape.move, List.reverse_append]
      rfl

/-- Iterate the transition rule written on Cook's finite configuration strings. -/
def appendixRun : Nat → M.AppendixConfig → M.AppendixConfig
  | 0, c => c
  | n + 1, c => appendixRun n (M.appendixTick c)

/-- The simulation preserves the exact number of ticks and the entire projected configuration. -/
theorem appendixRun_toConfig (n : Nat) (c : M.AppendixConfig) :
    (M.appendixRun n c).toConfig M = M.run n (c.toConfig M) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => rw [appendixRun, ih, appendixTick_toConfig, run_succ]

theorem appendixRun_start_state (n : Nat) (x : List α) :
    (M.appendixRun n (M.appendixStart x)).state = (M.run n (M.start x)).state := by
  have h := congrArg Config.state (M.appendixRun_toConfig n (M.appendixStart x))
  rw [appendixStart_toConfig] at h
  exact h

theorem accepts_iff_appendix (x : List α) :
    M.Accepts x ↔ ∃ n, (M.appendixRun n (M.appendixStart x)).state = .inr true := by
  simp only [Accepts, appendixRun_start_state]

theorem haltsWithin_iff_appendix (x : List α) (bound : Nat) :
    M.HaltsWithin x bound ↔
      ∃ n ≤ bound, ∃ b, (M.appendixRun n (M.appendixStart x)).state = .inr b := by
  simp only [HaltsWithin, appendixRun_start_state]

end Machine

end PvsNP
