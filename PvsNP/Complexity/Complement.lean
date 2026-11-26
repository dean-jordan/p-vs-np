module

public import PvsNP.Complexity.Classes

/-! # Complementing a total Cook decider -/

public section

namespace PvsNP

namespace Machine

variable {α : Type}

/-- Flip the answer of a machine at its halting transition. -/
@[expose] def flipAnswer (M : Machine α) : Machine α :=
  { M with transition := fun q a ↦
      let (state, write, dir) := M.transition q a
      (state.map id Bool.not, write, dir) }

/-- Identify configurations across machines that use the same states and tape. -/
@[expose] def flipConfig (M : Machine α) (c : M.Config) : M.flipAnswer.Config :=
  ⟨c.state.map id Bool.not, c.tape⟩

theorem tick_flipConfig (M : Machine α) (c : M.Config) :
    M.flipAnswer.tick (M.flipConfig c) = M.flipConfig (M.tick c) := by
  rcases c with ⟨state, tape⟩
  cases state with
  | inr b => rfl
  | inl q =>
    rcases h : M.transition q (@Turing.Tape.head _ M.tapeInhabited tape) with ⟨state, write, dir⟩
    simp only [flipConfig, flipAnswer, tick, Sum.map_inl, id_eq, h]
    rfl

/-- Complementing an answer preserves every clocked configuration up to the answer tag. -/
theorem run_flipConfig (M : Machine α) (n : Nat) (c : M.Config) :
    M.flipAnswer.run n (M.flipConfig c) = M.flipConfig (M.run n c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => rw [run_succ, tick_flipConfig, ih, run_succ]

theorem run_flipAnswer_state (M : Machine α) (n : Nat) (x : List α) :
    (M.flipAnswer.run n (M.flipAnswer.start x)).state =
      (M.run n (M.start x)).state.map id Bool.not :=
  congrArg Config.state (M.run_flipConfig n (M.start x))

theorem haltsWithin_flipAnswer_iff (M : Machine α) (x : List α) (n : Nat) :
    M.flipAnswer.HaltsWithin x n ↔ M.HaltsWithin x n := by
  simp only [Machine.haltsWithin_iff, run_flipAnswer_state]
  cases (M.run n (M.start x)).state with
  | inl => simp
  | inr b => exact ⟨fun _ ↦ ⟨b, rfl⟩, fun _ ↦ ⟨!b, rfl⟩⟩

theorem accepts_flipAnswer_iff (M : Machine α) (x : List α) {n : Nat}
    (h : M.HaltsWithin x n) : M.flipAnswer.Accepts x ↔ ¬ M.Accepts x := by
  have hFlip := (M.haltsWithin_flipAnswer_iff x n).mpr h
  obtain ⟨b, hb⟩ := (M.haltsWithin_iff x n).mp h
  rw [M.flipAnswer.accepts_iff_at_bound x hFlip, M.accepts_iff_at_bound x h,
    M.run_flipAnswer_state, hb]
  cases b
  · exact ⟨fun _ hFalse ↦ Bool.noConfusion (Sum.inr.inj hFalse), fun _ ↦ rfl⟩
  · exact ⟨fun hFalse ↦ Bool.noConfusion (Sum.inr.inj hFalse), fun hNot ↦ (hNot rfl).elim⟩

end Machine

theorem mem_POver_compl {α : Type} {L : Set (List α)} (h : L ∈ POver α) : Lᶜ ∈ POver α := by
  obtain ⟨M, ⟨k, hTime⟩, hDecides⟩ := h
  refine ⟨M.flipAnswer, ⟨k, fun x ↦ (M.haltsWithin_flipAnswer_iff x _).mpr (hTime x)⟩, ?_⟩
  intro x
  exact (not_congr (hDecides x)).trans (M.accepts_flipAnswer_iff x (hTime x)).symm

/-- Under `P = NP`, one bounded universal certificate check gives a language in `P`,
provided a Cook verifier for the corresponding violations is available. -/
theorem mem_P_of_bounded_universal_of_p_eq_np (hCollapse : P = NP) (A : CheckingAlphabet)
    (V : Machine A.Symbol) (k : Nat) (hTime : V.PolyTime)
    (hEncoding : ∀ z, V.Accepts z → ∃ x y, z = A.encode x y) :
    {x : BinaryWord | ∀ y : List A.Certificate, y.length ≤ x.length ^ k →
      ¬ V.Accepts (A.encode x y)} ∈ P := by
  let bad : BinaryLanguage := {x | ∃ y, y.length ≤ x.length ^ k ∧ V.Accepts (A.encode x y)}
  have hBad : bad ∈ NP := (mem_NP_iff_exists_verifier bad).mpr
    ⟨A, V, k, hTime, hEncoding, fun _ ↦ Iff.rfl⟩
  rw [← hCollapse] at hBad
  have hComplement : badᶜ ∈ P := mem_POver_compl hBad
  have hLanguage : badᶜ = {x : BinaryWord | ∀ y : List A.Certificate, y.length ≤ x.length ^ k →
      ¬ V.Accepts (A.encode x y)} := by
    ext x
    change (¬ ∃ y, y.length ≤ x.length ^ k ∧ V.Accepts (A.encode x y)) ↔ _
    constructor
    · exact fun h y hLen hAccept ↦ h ⟨y, hLen, hAccept⟩
    · rintro h ⟨y, hLen, hAccept⟩
      exact h y hLen hAccept
  exact hLanguage ▸ hComplement

end PvsNP
