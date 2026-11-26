module

public import PvsNP.TuringMachine.SharedAlphabet
public import PvsNP.TuringMachine.Transducer

import Mathlib.Basic.Finite.Sum
import PvsNP.TuringMachine.OutputBound
import PvsNP.Complexity.Containment

/-! # Running a transducer before a decider

Both machines use the same representations of blank and of each bit. The
first machine's accepting transition enters the second machine's initial
state, so handing off the canonical output tape takes no additional steps.
-/

public section

namespace PvsNP.Machine

open Turing

variable (M D : Machine Bool)

private def prefixState : M.State ⊕ Bool → (M.State ⊕ D.State) ⊕ Bool
  | .inl q => .inl (.inl q)
  | .inr true => .inl (.inr D.initial)
  | .inr false => .inr false

/-- Run `M` first, and start `D` at its successful halt. -/
@[reducible] noncomputable def prepend : Machine Bool := by
  letI : Finite M.State := M.stateFinite
  letI : Finite D.State := D.stateFinite
  exact {
    State := M.State ⊕ D.State
    Symbol := SharedAlphabet M D
    stateFinite := inferInstance
    symbolFinite := SharedAlphabet.finite M D
    initial := .inl M.initial
    blank := SharedAlphabet.blank M D
    input := SharedAlphabet.input M D
    input_ne_blank := SharedAlphabet.input_ne_blank M D
    transition := fun q a ↦ match q with
      | .inl q => match SharedAlphabet.readLeft M D a with
        | none => ⟨.inr false, a, .right⟩
        | some s =>
          let ⟨q', b, dir⟩ := M.transition q s
          ⟨prefixState M D q', SharedAlphabet.left M D b, dir⟩
      | .inr q => match SharedAlphabet.readRight M D a with
        | none => ⟨.inr false, a, .right⟩
        | some s =>
          let ⟨q', b, dir⟩ := D.transition q s
          ⟨q'.map Sum.inr id, SharedAlphabet.right M D b, dir⟩ }

private noncomputable def prefixConfig (c : M.Config) : (M.prepend D).Config :=
  ⟨prefixState M D c.state, @Tape.map _ _ M.tapeInhabited (M.prepend D).tapeInhabited
    (SharedAlphabet.leftPointed M D) c.tape⟩

private noncomputable def suffixConfig (c : D.Config) : (M.prepend D).Config :=
  ⟨c.state.map Sum.inr id, @Tape.map _ _ D.tapeInhabited (M.prepend D).tapeInhabited
    (SharedAlphabet.rightPointed M D) c.tape⟩

private theorem prefix_wordTape (x : BinaryWord) :
    @Tape.map _ _ M.tapeInhabited (M.prepend D).tapeInhabited
      (SharedAlphabet.leftPointed M D) (M.wordTape x) = (M.prepend D).wordTape x :=
  SharedAlphabet.leftPointed_map_start M D x

private theorem suffix_wordTape (x : BinaryWord) :
    @Tape.map _ _ D.tapeInhabited (M.prepend D).tapeInhabited
      (SharedAlphabet.rightPointed M D) (D.wordTape x) = (M.prepend D).wordTape x :=
  SharedAlphabet.rightPointed_map_start M D x

private theorem tick_prefix_running (q : M.State) (tape : M.Tape) :
    (M.prepend D).tick (prefixConfig M D ⟨.inl q, tape⟩) =
      prefixConfig M D (M.tick ⟨.inl q, tape⟩) := by
  rcases h : M.transition q (@Tape.head _ M.tapeInhabited tape) with ⟨q', b, dir⟩
  simp [Machine.tick, prefixConfig, prefixState, prepend, h, Tape.map_move,
    SharedAlphabet.leftPointed]

private theorem tick_prefix (c : M.Config) (h : ∃ q, c.state = .inl q) :
    (M.prepend D).tick (prefixConfig M D c) = prefixConfig M D (M.tick c) := by
  obtain ⟨state, tape⟩ := c
  obtain ⟨q, hq⟩ := h
  change state = .inl q at hq
  subst state
  exact tick_prefix_running M D q tape

private theorem run_prefix (c : M.Config) (n : Nat)
    (running : ∀ j < n, ∃ q, (M.run j c).state = .inl q) :
    (M.prepend D).run n (prefixConfig M D c) = prefixConfig M D (M.run n c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [Machine.run_succ, tick_prefix M D c (running 0 (Nat.zero_lt_succ _)), Machine.run_succ]
    exact ih _ (fun j hj ↦ running (j + 1) (Nat.succ_lt_succ hj))

private theorem tick_suffix (c : D.Config) :
    (M.prepend D).tick (suffixConfig M D c) = suffixConfig M D (D.tick c) := by
  obtain ⟨state, tape⟩ := c
  cases state with
  | inr b => rfl
  | inl q =>
    rcases h : D.transition q (@Tape.head _ D.tapeInhabited tape) with ⟨q', b, dir⟩
    simp [Machine.tick, suffixConfig, prepend, h, Tape.map_move, SharedAlphabet.rightPointed]

private theorem run_suffix (c : D.Config) (n : Nat) :
    (M.prepend D).run n (suffixConfig M D c) = suffixConfig M D (D.run n c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp only [Machine.run_succ, tick_suffix, ih]

private theorem start_prefix (x : BinaryWord) :
    (M.prepend D).start x = prefixConfig M D (M.start x) :=
  congrArg (fun tape ↦ (⟨.inl (.inl M.initial), tape⟩ : (M.prepend D).Config))
    (prefix_wordTape M D x).symm

private theorem handoff (x y : BinaryWord) (t : Nat) (h : M.OutputsAt x y t) :
    prefixConfig M D (M.run t (M.start x)) = suffixConfig M D (D.start y) := by
  have hOut := h.2
  have hState := h.1
  unfold prefixConfig suffixConfig
  rw [hOut, hState]
  change (⟨.inl (.inr D.initial), _⟩ : (M.prepend D).Config) = ⟨.inl (.inr D.initial), _⟩
  congr 1
  exact (prefix_wordTape M D y).trans (suffix_wordTape M D y).symm

private theorem run_prepend (x y : BinaryWord) (t u : Nat) (h : M.OutputsAt x y t)
    (running : ∀ j < t, ∃ q, (M.run j (M.start x)).state = .inl q) :
    (M.prepend D).run (t + u) ((M.prepend D).start x) = suffixConfig M D (D.run u (D.start y)) := by
  rw [Machine.run_add, start_prefix, run_prefix M D _ _ running, handoff M D x y t h, run_suffix]

/-- At the combined cost, the two-phase machine has the second machine's result. -/
theorem prepend_halt (x y : BinaryWord) (t u : Nat) {b : Bool}
    (h : M.OutputsAt x y t) (running : ∀ j < t, ∃ q, (M.run j (M.start x)).state = .inl q)
    (hD : (D.run u (D.start y)).state = .inr b) :
    ((M.prepend D).run (t + u) ((M.prepend D).start x)).state = .inr b := by
  rw [run_prepend M D x y t u h running]
  change ((D.run u (D.start y)).state.map Sum.inr id) = .inr b
  rw [hD]
  rfl

/-- When the second machine is a transducer, the composition preserves its output word. -/
theorem prepend_output (x y z : BinaryWord) (t u : Nat)
    (h : M.OutputsAt x y t) (running : ∀ j < t, ∃ q, (M.run j (M.start x)).state = .inl q)
    (hD : D.OutputsAt y z u) : (M.prepend D).OutputsAt x z (t + u) := by
  refine ⟨prepend_halt M D x y t u h running hD.1, ?_⟩
  rw [run_prepend M D x y t u h running]
  change @Tape.map _ _ D.tapeInhabited (M.prepend D).tapeInhabited
    (SharedAlphabet.rightPointed M D) (D.run u (D.start y)).tape = (M.prepend D).wordTape z
  rw [hD.2, suffix_wordTape]

private theorem compute_at_first_halt {f : BinaryWord → BinaryWord} (hf : M.Computes f)
    (x : BinaryWord) {bound : Nat} (hBound : M.HaltsWithin x bound) :
    ∃ t ≤ bound, M.OutputsAt x (f x) t ∧
      ∀ j < t, ∃ q, (M.run j (M.start x)).state = .inl q := by
  obtain ⟨u, h⟩ := hf x
  exact M.outputsAt_firstHalt hBound h

/-- Combining a polynomial transducer with a polynomial-time second phase remains polynomial. -/
theorem prepend_polyTime {f : BinaryWord → BinaryWord} (hM : M.PolyTime) (hf : M.Computes f)
    (hD : D.PolyTime) : (M.prepend D).PolyTime := by
  obtain ⟨a, ha⟩ := hM
  obtain ⟨d, hd⟩ := hD
  let overhead n := n ^ a + a
  let outputSize n := n + 2 * overhead n
  let time n := overhead n + (outputSize n ^ d + d)
  have overheadPoly : PolynomiallyBounded overhead :=
    (PolynomiallyBounded.id.pow a).add (PolynomiallyBounded.const a)
  have sizePoly : PolynomiallyBounded outputSize :=
    PolynomiallyBounded.id.add ((PolynomiallyBounded.const 2).mul overheadPoly)
  have timePoly : PolynomiallyBounded time :=
    overheadPoly.add ((sizePoly.pow d).add (PolynomiallyBounded.const d))
  refine ((M.prepend D).polyTime_iff_polynomiallyBounded).mpr ⟨time, timePoly, fun x ↦ ?_⟩
  obtain ⟨t, ht, hf', hRun⟩ := compute_at_first_halt M hf x (ha x)
  obtain ⟨u, hu, b, hb⟩ := hd (f x)
  have hSize : (f x).length ≤ outputSize x.length := by
    exact Nat.le_trans (M.output_length_le x (f x) t hf'.2)
      (Nat.add_le_add_left (Nat.mul_le_mul_left 2 ht) _)
  have hTime : u ≤ outputSize x.length ^ d + d :=
    Nat.le_trans hu (Nat.add_le_add_right (Nat.pow_le_pow_left hSize d) d)
  exact ⟨t + u, Nat.add_le_add ht hTime, b, prepend_halt M D x (f x) t u hf' hRun hb⟩

theorem prepend_accepts_iff {f : BinaryWord → BinaryWord} (hM : M.PolyTime) (hf : M.Computes f)
    (hD : D.PolyTime) (x : BinaryWord) : (M.prepend D).Accepts x ↔ D.Accepts (f x) := by
  obtain ⟨a, ha⟩ := hM
  obtain ⟨d, hd⟩ := hD
  obtain ⟨t, _, hf', hRun⟩ := compute_at_first_halt M hf x (ha x)
  obtain ⟨u, _, b, hb⟩ := hd (f x)
  have hc := prepend_halt M D x (f x) t u hf' hRun hb
  constructor
  · rintro ⟨v, hv⟩
    have heq := (M.prepend D).halt_result_unique _ hc hv
    exact ⟨u, heq ▸ hb⟩
  · rintro ⟨v, hv⟩
    have heq := D.halt_result_unique _ hb hv
    exact ⟨t + u, heq ▸ hc⟩

theorem prepend_computes {f g : BinaryWord → BinaryWord} (hM : M.PolyTime) (hf : M.Computes f)
    (hg : D.Computes g) : (M.prepend D).Computes (g ∘ f) := by
  obtain ⟨a, ha⟩ := hM
  intro x
  obtain ⟨t, _, hf', hRun⟩ := compute_at_first_halt M hf x (ha x)
  obtain ⟨u, hg'⟩ := hg (f x)
  exact ⟨t + u, prepend_output M D x (f x) (g (f x)) t u hf' hRun hg'⟩

end PvsNP.Machine

namespace PvsNP

theorem PolynomialTimeMap.comp {f g : BinaryWord → BinaryWord}
    (hg : PolynomialTimeMap g) (hf : PolynomialTimeMap f) : PolynomialTimeMap (g ∘ f) := by
  obtain ⟨M, hpM, hM⟩ := hf
  obtain ⟨D, hpD, hD⟩ := hg
  exact ⟨M.prepend D, M.prepend_polyTime D hpM hM hpD, M.prepend_computes D hpM hM hD⟩

theorem PolynomialTimeMap.outputLengthBound {f : BinaryWord → BinaryWord}
    (h : PolynomialTimeMap f) :
    ∃ bound : Nat → Nat, PolynomiallyBounded bound ∧ ∀ x, (f x).length ≤ bound x.length := by
  obtain ⟨M, ⟨a, ha⟩, hf⟩ := h
  have hp := (PolynomiallyBounded.id.pow a).add (PolynomiallyBounded.const a)
  refine ⟨fun n ↦ n + 2 * (n ^ a + a),
    PolynomiallyBounded.id.add ((PolynomiallyBounded.const 2).mul hp), fun x ↦ ?_⟩
  obtain ⟨t, ht, hOutput, _⟩ := Machine.compute_at_first_halt M hf x (ha x)
  exact Nat.le_trans (M.output_length_le x (f x) t hOutput.2)
    (Nat.add_le_add_left (Nat.mul_le_mul_left 2 ht) _)

/-- Cook's Proposition 1(a) for the binary output convention. -/
theorem PolynomiallyReducesTo.mem_P {L K : BinaryLanguage}
    (h : PolynomiallyReducesTo L K) (hK : K ∈ P) : L ∈ P := by
  obtain ⟨f, ⟨M, hpM, hf⟩, hmem⟩ := h
  obtain ⟨D, hpD, hD⟩ := hK
  refine ⟨M.prepend D, M.prepend_polyTime D hpM hf hpD, fun x ↦ ?_⟩
  exact (hmem x).trans ((hD (f x)).trans (M.prepend_accepts_iff D hpM hf hpD x).symm)

theorem PolynomiallyReducesTo.trans {L K J : BinaryLanguage}
    (hLK : PolynomiallyReducesTo L K) (hKJ : PolynomiallyReducesTo K J) :
    PolynomiallyReducesTo L J := by
  obtain ⟨f, hf, hmemLK⟩ := hLK
  obtain ⟨g, hg, hmemKJ⟩ := hKJ
  exact ⟨g ∘ f, hg.comp hf, fun x ↦ (hmemLK x).trans (hmemKJ (f x))⟩

/-- Cook's Definition 4 for binary languages and canonical-output reductions. -/
@[expose] def NPComplete (K : BinaryLanguage) : Prop :=
  K ∈ NP ∧ ∀ L ∈ NP, PolynomiallyReducesTo L K

/-- Cook's Proposition 1(b). -/
theorem NPComplete.of_reduction {L K : BinaryLanguage}
    (hL : NPComplete L) (hK : K ∈ NP) (h : PolynomiallyReducesTo L K) : NPComplete K :=
  ⟨hK, fun J hJ ↦ (hL.2 J hJ).trans h⟩

/-- For an NP-complete language, its membership in `P` is equivalent to `P = NP`. -/
theorem NPComplete.p_eq_np_iff_mem_P {K : BinaryLanguage} (h : NPComplete K) :
    P = NP ↔ K ∈ P := by
  constructor
  · intro hEq
    rw [hEq]
    exact h.1
  · intro hK
    exact p_eq_np_iff_np_subset_p.mpr fun L hL ↦ (h.2 L hL).mem_P hK

end PvsNP
