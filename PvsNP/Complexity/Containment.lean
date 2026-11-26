module

public import PvsNP.Complexity.Classes

import Mathlib.Basic.Finite.Prod
import Mathlib.Basic.Finite.Sum

/-! # Turning a decider into an empty-certificate verifier -/

namespace PvsNP

open Turing

private abbrev PrepState := Bool × Bool

private abbrev scan : PrepState := (false, false)
private abbrev confirm : PrepState := (false, true)
private abbrev skipBlank : PrepState := (true, false)
private abbrev rewind : PrepState := (true, true)

private def verifierInput (M : Machine Bool) : Option Bool ↪ M.Symbol ⊕ Unit where
  toFun
    | none => .inr ()
    | some b => .inl (M.input b)
  inj' := by
    intro x y h
    cases x <;> cases y <;> simp_all [M.input.injective.eq_iff]

@[simp] private theorem input_none (M : Machine Bool) : verifierInput M none = .inr () := rfl

@[simp] private theorem input_some (M : Machine Bool) (b : Bool) :
    verifierInput M (some b) = .inl (M.input b) := rfl

private noncomputable abbrev verifier (M : Machine Bool) : Machine (Option Bool) := by
  classical
  letI : Finite M.State := M.stateFinite
  letI : Finite M.Symbol := M.symbolFinite
  exact {
    State := PrepState ⊕ M.State
    Symbol := M.Symbol ⊕ Unit
    stateFinite := inferInstance
    symbolFinite := inferInstance
    initial := .inl scan
    blank := .inl M.blank
    input := verifierInput M
    input_ne_blank := by
      intro a
      cases a with
      | none => simp
      | some b => exact fun h => M.input_ne_blank b (Sum.inl.inj h)
    transition := fun
      | .inl (false, false), .inr _ => ⟨.inl (.inl confirm), .inl M.blank, .right⟩
      | .inl (false, false), .inl a =>
        if a = M.blank then ⟨.inr false, .inl a, .right⟩
        else ⟨.inl (.inl scan), .inl a, .right⟩
      | .inl (false, true), a =>
        if a = .inl M.blank then ⟨.inl (.inl skipBlank), a, .left⟩
        else ⟨.inr false, a, .right⟩
      | .inl (true, false), a => ⟨.inl (.inl rewind), a, .left⟩
      | .inl (true, true), a =>
        if a = .inl M.blank then ⟨.inl (.inr M.initial), a, .right⟩
        else ⟨.inl (.inl rewind), a, .left⟩
      | .inr q, .inl a =>
        let ⟨p, b, d⟩ := M.transition q a
        ⟨p.map Sum.inr id, .inl b, d⟩
      | .inr _, .inr b => ⟨.inr false, .inr b, .right⟩ }

private theorem moveRight_cons {Γ : Type} [Inhabited Γ] (l r : List Γ) (a : Γ) :
    (Tape.mk₂ l (a :: r)).move .right = Tape.mk₂ (a :: l) r := by
  simp [Tape.mk₂, ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk]

private theorem moveLeft_cons {Γ : Type} [Inhabited Γ] (l r : List Γ) (a : Γ) :
    (Tape.mk₂ (a :: l) r).move .left = Tape.mk₂ l (a :: r) := by
  simp [Tape.mk₂, ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk]

private theorem moveLeft_nil {Γ : Type} [Inhabited Γ] (r : List Γ) :
    (Tape.mk₂ [] r).move .left = Tape.mk₂ [] (default :: r) := by
  simp [Tape.mk₂, ListBlank.head_mk, ListBlank.tail_mk, ListBlank.cons_mk]

private theorem write_cons {Γ : Type} [Inhabited Γ] (l r : List Γ) (a b : Γ) :
    (Tape.mk₂ l (a :: r)).write b = Tape.mk₂ l (b :: r) := by
  simp [Tape.mk₂, ListBlank.tail_mk, ListBlank.cons_mk]

private theorem tape_nil_blank {Γ : Type} [Inhabited Γ] (l : List Γ) :
    Tape.mk₂ l [default] = Tape.mk₂ l [] := by
  have h : ListBlank.mk ([default] : List Γ) = ListBlank.mk [] :=
    Quotient.sound (Or.inr ⟨1, rfl⟩)
  simp [Tape.mk₂, h]

private abbrev liftedBit (M : Machine Bool) (b : Bool) : M.Symbol ⊕ Unit :=
  .inl (M.input b)

private abbrev liftedBlank (M : Machine Bool) : M.Symbol ⊕ Unit := .inl M.blank

private noncomputable abbrev cursor (M : Machine Bool) (left right : List (M.Symbol ⊕ Unit)) :
    (verifier M).Tape :=
  @Tape.mk₂ _ (verifier M).tapeInhabited left right

private noncomputable abbrev shift (M : Machine Bool) (d : Dir) (t : (verifier M).Tape) :
    (verifier M).Tape := @Tape.move _ (verifier M).tapeInhabited d t

private noncomputable abbrev overwrite (M : Machine Bool) (a : M.Symbol ⊕ Unit)
    (t : (verifier M).Tape) : (verifier M).Tape := @Tape.write _ (verifier M).tapeInhabited a t

private noncomputable abbrev read (M : Machine Bool) (t : (verifier M).Tape) :
    M.Symbol ⊕ Unit := @Tape.head _ (verifier M).tapeInhabited t

@[simp] private theorem cursor_head_cons (M : Machine Bool) (l r : List (M.Symbol ⊕ Unit))
    (a : M.Symbol ⊕ Unit) : read M (cursor M l (a :: r)) = a := rfl

@[simp] private theorem cursor_head_nil (M : Machine Bool) (l : List (M.Symbol ⊕ Unit)) :
    read M (cursor M l []) = liftedBlank M := rfl

private theorem tick_scan_bit (M : Machine Bool) (b : Bool) (l r : List (M.Symbol ⊕ Unit)) :
    (verifier M).tick ⟨.inl (.inl scan), cursor M l (liftedBit M b :: r)⟩ =
      ⟨.inl (.inl scan), cursor M (liftedBit M b :: l) r⟩ := by
  simp only [Machine.tick, verifier, scan, cursor_head_cons, M.input_ne_blank, ↓reduceIte]
  change (⟨.inl (.inl scan), shift M .right (overwrite M (liftedBit M b)
    (cursor M l (liftedBit M b :: r)))⟩ : (verifier M).Config) = _
  have h := @write_cons _ (verifier M).tapeInhabited l r (liftedBit M b) (liftedBit M b)
  exact congrArg (fun t ↦ (⟨.inl (.inl scan), t⟩ : (verifier M).Config))
    ((congrArg (shift M .right) h).trans
      (@moveRight_cons _ (verifier M).tapeInhabited l r (liftedBit M b)))

private theorem scan_prefix (M : Machine Bool) (x : List Bool) (l r : List (M.Symbol ⊕ Unit)) :
    (verifier M).run x.length
      ⟨.inl (.inl scan), cursor M l (x.map (liftedBit M) ++ r)⟩ =
      ⟨.inl (.inl scan), cursor M ((x.map (liftedBit M)).reverse ++ l) r⟩ := by
  induction x generalizing l with
  | nil => simp
  | cons b x ih =>
    simp only [List.length_cons, List.map_cons, List.cons_append, Machine.run_succ]
    have h := congrArg ((verifier M).run x.length)
      (tick_scan_bit M b l (x.map (liftedBit M) ++ r))
    exact h.trans ((ih (liftedBit M b :: l)).trans (by simp [List.reverse_cons, List.append_assoc]))

private theorem tick_rewind_bit (M : Machine Bool) (b : Bool) (l r : List (M.Symbol ⊕ Unit)) :
    (verifier M).tick ⟨.inl (.inl rewind), cursor M l (liftedBit M b :: r)⟩ =
      ⟨.inl (.inl rewind), shift M .left (cursor M l (liftedBit M b :: r))⟩ := by
  simp [Machine.tick, verifier, rewind, M.input_ne_blank]
  rfl

private theorem rewind_prefix (M : Machine Bool) (x : List Bool) (l r : List (M.Symbol ⊕ Unit)) :
    (verifier M).run x.length
      ⟨.inl (.inl rewind), shift M .left (cursor M (x.map (liftedBit M) ++ l) r)⟩ =
      ⟨.inl (.inl rewind), shift M .left (cursor M l ((x.map (liftedBit M)).reverse ++ r))⟩ := by
  induction x generalizing r with
  | nil => simp
  | cons b x ih =>
    simp only [List.length_cons, List.map_cons, List.cons_append, Machine.run_succ, moveLeft_cons]
    have h := congrArg ((verifier M).run x.length)
      (tick_rewind_bit M b (x.map (liftedBit M) ++ l) r)
    exact h.trans ((ih (liftedBit M b :: r)).trans (by simp [List.reverse_cons, List.append_assoc]))

private theorem tick_scan_blank (M : Machine Bool) (l : List (M.Symbol ⊕ Unit)) :
    ((verifier M).tick ⟨.inl (.inl scan), cursor M l []⟩).state = .inr false := by
  simp [Machine.tick, verifier, scan]

private theorem tick_scan_separator (M : Machine Bool) (l r : List (M.Symbol ⊕ Unit)) :
    (verifier M).tick ⟨.inl (.inl scan), cursor M l (.inr () :: r)⟩ =
      ⟨.inl (.inl confirm), cursor M (liftedBlank M :: l) r⟩ := by
  change (⟨.inl (.inl confirm), shift M .right (overwrite M (liftedBlank M)
    (cursor M l (.inr () :: r)))⟩ : (verifier M).Config) = _
  have h := @write_cons _ (verifier M).tapeInhabited l r (.inr ()) (liftedBlank M)
  exact congrArg (fun t => (⟨.inl (.inl confirm), t⟩ : (verifier M).Config))
    ((congrArg (shift M .right) h).trans
      (@moveRight_cons _ (verifier M).tapeInhabited l r (liftedBlank M)))

private theorem tick_confirm_empty (M : Machine Bool) (l : List (M.Symbol ⊕ Unit)) :
    (verifier M).tick ⟨.inl (.inl confirm), cursor M (liftedBlank M :: l) []⟩ =
      ⟨.inl (.inl skipBlank), cursor M l []⟩ := by
  simp only [Machine.tick, confirm, verifier, cursor_head_nil, ↓reduceIte]
  change (⟨.inl (.inl skipBlank), shift M .left (overwrite M (liftedBlank M)
    (cursor M (liftedBlank M :: l) []))⟩ :
    (verifier M).Config) = _
  exact congrArg (fun t => (⟨.inl (.inl skipBlank), t⟩ : (verifier M).Config))
    ((@moveLeft_cons _ (verifier M).tapeInhabited l [] (liftedBlank M)).trans
      (@tape_nil_blank _ (verifier M).tapeInhabited l))

private theorem tick_skip_blank (M : Machine Bool) (l : List (M.Symbol ⊕ Unit)) :
    (verifier M).tick ⟨.inl (.inl skipBlank), cursor M l []⟩ =
      ⟨.inl (.inl rewind), shift M .left (cursor M l [])⟩ := by
  rfl

private theorem tick_rewind_end (M : Machine Bool) (r : List (M.Symbol ⊕ Unit)) :
    (verifier M).tick ⟨.inl (.inl rewind), shift M .left (cursor M [] r)⟩ =
      ⟨.inl (.inr M.initial), cursor M [] r⟩ := by
  have h : shift M .left (cursor M [] r) = cursor M [] (liftedBlank M :: r) :=
    @moveLeft_nil _ (verifier M).tapeInhabited r
  rw [h]
  simp only [Machine.tick, rewind, verifier, cursor_head_cons, ↓reduceIte]
  change (⟨.inl (.inr M.initial), shift M .right (overwrite M (liftedBlank M)
    (cursor M [] (liftedBlank M :: r)))⟩ :
    (verifier M).Config) = _
  exact congrArg (fun t => (⟨.inl (.inr M.initial), t⟩ : (verifier M).Config))
    ((congrArg (shift M .right) h.symm).trans
      (@Tape.move_left_right _ (verifier M).tapeInhabited (cursor M [] r)))

private theorem verifier_start_prefix (M : Machine Bool) (x : List Bool) (r : List (Option Bool)) :
    (verifier M).start (x.map some ++ r) =
      ⟨.inl (.inl scan), cursor M [] (x.map (liftedBit M) ++ r.map (verifierInput M))⟩ := by
  simp [Machine.start, Tape.mk₁, List.map_append, List.map_map, verifier]
  rfl

private theorem valid_preparation (M : Machine Bool) (x : List Bool) :
    (verifier M).run (x.length + 3 + x.reverse.length + 1)
      ((verifier M).start (x.map some ++ [none])) =
      ⟨.inl (.inr M.initial), cursor M [] (x.map (liftedBit M))⟩ := by
  rw [verifier_start_prefix, Machine.run_add, Machine.run_add, Machine.run_add, scan_prefix]
  simp only [List.map_cons, List.map_nil, input_none, List.append_nil, Machine.run]
  let l := (x.map (liftedBit M)).reverse
  have hSeparator := tick_scan_separator M l []
  have hConfirm := tick_confirm_empty M l
  have hSkip := tick_skip_blank M l
  have h := congrArg ((verifier M).tick ∘ (verifier M).run x.reverse.length)
    ((congrArg ((verifier M).tick ∘ (verifier M).tick) hSeparator).trans
      ((congrArg (verifier M).tick hConfirm).trans hSkip))
  have hRewind := rewind_prefix M x.reverse [] []
  simp only [List.map_reverse, List.reverse_reverse, List.append_nil] at hRewind
  exact h.trans ((congrArg (verifier M).tick hRewind).trans (tick_rewind_end M _))

private noncomputable def liftSymbol (M : Machine Bool) :
    @PointedMap M.Symbol (verifier M).Symbol M.tapeInhabited (verifier M).tapeInhabited :=
  @PointedMap.mk _ _ M.tapeInhabited (verifier M).tapeInhabited Sum.inl rfl

private noncomputable def liftConfig (M : Machine Bool) (c : M.Config) : (verifier M).Config :=
  ⟨c.state.map Sum.inr id, @Tape.map _ _ M.tapeInhabited (verifier M).tapeInhabited
    (liftSymbol M) c.tape⟩

private theorem lift_tick (M : Machine Bool) (c : M.Config) :
    (verifier M).tick (liftConfig M c) = liftConfig M (M.tick c) := by
  obtain ⟨q, tape⟩ := c
  cases q with
  | inr b => rfl
  | inl q =>
    rcases hM : M.transition q (@Tape.head _ M.tapeInhabited tape) with ⟨state, symbol, dir⟩
    simp [Machine.tick, liftConfig, verifier, hM, Tape.map_move, Tape.map_write, liftSymbol]

private theorem lift_run (M : Machine Bool) (n : Nat) (c : M.Config) :
    (verifier M).run n (liftConfig M c) = liftConfig M (M.run n c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp only [Machine.run_succ, lift_tick, ih]

private theorem lift_start (M : Machine Bool) (x : List Bool) :
    liftConfig M (M.start x) = ⟨.inl (.inr M.initial), cursor M [] (x.map (liftedBit M))⟩ := by
  have h := @Tape.map_mk₁ _ _ M.tapeInhabited (verifier M).tapeInhabited
    (liftSymbol M) (x.map M.input)
  rw [List.map_map] at h
  exact congrArg (fun t => (⟨.inl (.inr M.initial), t⟩ : (verifier M).Config)) h

private theorem run_valid_verifier (M : Machine Bool) (x : List Bool) (n : Nat) :
    (verifier M).run (x.length + 3 + x.reverse.length + 1 + n)
      ((verifier M).start (x.map some ++ [none])) = liftConfig M (M.run n (M.start x)) := by
  rw [Machine.run_add, valid_preparation, ← lift_start, lift_run]

private theorem tick_confirm_nonempty (M : Machine Bool) (l : List (M.Symbol ⊕ Unit))
    (z : Option Bool) (r : List (M.Symbol ⊕ Unit)) :
    ((verifier M).tick ⟨.inl (.inl confirm), cursor M l (verifierInput M z :: r)⟩).state =
      .inr false := by
  cases z <;> simp [Machine.tick, verifier, confirm, M.input_ne_blank]

private theorem run_missing_separator (M : Machine Bool) (x : List Bool) :
    ((verifier M).run (x.length + 1) ((verifier M).start (x.map some))).state = .inr false := by
  rw [← List.append_nil (x.map some), verifier_start_prefix, Machine.run_add, scan_prefix]
  exact tick_scan_blank M (x.map (liftedBit M)).reverse

private theorem run_nonempty_certificate (M : Machine Bool) (x : List Bool) (z : Option Bool)
    (r : List (Option Bool)) :
    ((verifier M).run (x.length + 2) ((verifier M).start (x.map some ++ none :: z :: r))).state =
      .inr false := by
  rw [verifier_start_prefix, Machine.run_add, scan_prefix]
  simp only [List.map_cons, input_none, Machine.run]
  exact tick_confirm_nonempty M _ z _

private theorem split_input (w : List (Option Bool)) :
    ∃ x : List Bool, w = x.map some ∨ ∃ r, w = x.map some ++ none :: r := by
  induction w with
  | nil => exact ⟨[], Or.inl rfl⟩
  | cons a w ih =>
    cases a with
    | none => exact ⟨[], Or.inr ⟨w, rfl⟩⟩
    | some b =>
      obtain ⟨x, h | ⟨r, h⟩⟩ := ih
      · exact ⟨b :: x, Or.inl (congrArg (List.cons (some b)) h)⟩
      · exact ⟨b :: x, Or.inr ⟨r, congrArg (List.cons (some b)) h⟩⟩

private theorem verifier_valid_halted (M : Machine Bool) (x : List Bool) (n : Nat) {b : Bool}
    (h : (M.run n (M.start x)).state = .inr b) :
    ((verifier M).run (x.length + 3 + x.reverse.length + 1 + n)
      ((verifier M).start (x.map some ++ [none]))).state = .inr b := by
  rw [run_valid_verifier]
  simp [liftConfig, h, Sum.map]

private theorem verifier_polyTime (M : Machine Bool) (hp : M.PolyTime) : (verifier M).PolyTime := by
  obtain ⟨k, hk⟩ := hp
  have hCook : PolynomiallyBounded (fun n => n ^ k + k) :=
    (polynomiallyBounded_iff_cook _).mpr ⟨k, fun _ => Nat.le_refl _⟩
  have hPrep : PolynomiallyBounded (fun n => (n + n) + 4) :=
    (PolynomiallyBounded.id.add PolynomiallyBounded.id).add (PolynomiallyBounded.const 4)
  refine ((verifier M).polyTime_iff_polynomiallyBounded).mpr
    ⟨fun n => n ^ k + k + (n + n + 4), hCook.add hPrep, fun w => ?_⟩
  obtain ⟨x, rfl | ⟨r, rfl⟩⟩ := split_input w
  · refine ⟨x.length + 1, ?_, false, run_missing_separator M x⟩
    simp only [List.length_map]
    omega
  · cases r with
    | nil =>
      obtain ⟨n, hn, b, hb⟩ := hk x
      refine ⟨x.length + 3 + x.reverse.length + 1 + n, ?_, b, verifier_valid_halted M x n hb⟩
      have hPow : x.length ^ k ≤ (x.map some ++ [none]).length ^ k :=
        Nat.pow_le_pow_left (by simp) k
      simp only [List.length_reverse, List.length_append, List.length_map, List.length_cons,
        List.length_nil] at hPow ⊢
      omega
    | cons z r =>
      refine ⟨x.length + 2, ?_, false, run_nonempty_certificate M x z r⟩
      simp only [List.length_append, List.length_map, List.length_cons]
      omega

private theorem verifier_accepts (M : Machine Bool) (hp : M.PolyTime) (x : List Bool) :
    (verifier M).Accepts (x.map some ++ [none]) ↔ M.Accepts x := by
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨k, hk⟩ := hp
    obtain ⟨n, _, b, hb⟩ := hk x
    have h := (verifier M).halt_result_unique _ (verifier_valid_halted M x n hb) hm
    exact ⟨n, by simpa [h] using hb⟩
  · rintro ⟨n, hn⟩
    exact ⟨_, verifier_valid_halted M x n hn⟩

private def emptyCertificate (L : BinaryLanguage) (x : BinaryWord)
    (y : List binaryCheckingAlphabet.Certificate) : Prop :=
  y = [] ∧ x ∈ L

private theorem verifier_decides (M : Machine Bool) (hp : M.PolyTime) {L : BinaryLanguage}
    (hd : M.Decides L) :
    (verifier M).Decides (binaryCheckingAlphabet.checkingLanguage (emptyCertificate L)) := by
  intro w
  constructor
  · rintro ⟨x, y, hEnc, rfl, hx⟩
    rw [hEnc]
    exact (verifier_accepts M hp x).mpr ((hd x).mp hx)
  · intro hw
    obtain ⟨x, rfl | ⟨r, rfl⟩⟩ := split_input w
    · obtain ⟨m, hm⟩ := hw
      exact Bool.false_ne_true
        ((verifier M).halt_result_unique _ (run_missing_separator M x) hm) |>.elim
    · cases r with
      | nil =>
        have hx := (hd x).mpr ((verifier_accepts M hp x).mp hw)
        exact ⟨x, [], rfl, rfl, hx⟩
      | cons z r =>
        obtain ⟨m, hm⟩ := hw
        exact Bool.false_ne_true
          ((verifier M).halt_result_unique _ (run_nonempty_certificate M x z r) hm) |>.elim

/-- Every deterministic polynomial-time language admits an empty-certificate verifier.
The verifier decides the entire checking language, rejecting every input that is not `x#`. -/
public theorem p_subset_np : P ⊆ NP := by
  intro L hL
  obtain ⟨M, hp, hd⟩ := hL
  refine ⟨binaryCheckingAlphabet, emptyCertificate L, ⟨verifier M, verifier_polyTime M hp,
    verifier_decides M hp hd⟩, 0, fun x => ?_⟩
  constructor
  · intro hx
    exact ⟨[], Nat.zero_le _, rfl, hx⟩
  · rintro ⟨_, _, _, hx⟩
    exact hx

/-- The reverse class inclusion is sufficient for equality. -/
public theorem p_eq_np_iff_np_subset_p : P = NP ↔ NP ⊆ P := by
  constructor
  · intro h L hL
    rwa [h]
  · exact fun h ↦ Set.Subset.antisymm p_subset_np h

/-- Separation is equivalent to an NP language with no polynomial-time decider. -/
public theorem p_ne_np_iff_exists_language : P ≠ NP ↔ ∃ L ∈ NP, L ∉ P :=
  (not_congr p_eq_np_iff_np_subset_p).trans Set.not_subset

end PvsNP
