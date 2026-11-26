module

public import PvsNP.Circuits.Layered
public import PvsNP.CookLevin.TapeWindow

/-! # Formula layers for one bounded Cook machine step -/

public section

namespace PvsNP.Circuits

/-- The state, head, and tape symbol indicators for a finite window. -/
abbrev WindowWire (Q S : Type) (w : Nat) := Q ⊕ (Fin w ⊕ (Fin w × S))

variable {α : Type} (M : Machine α) {w : Nat}
variable [DecidableEq M.State] [DecidableEq M.Symbol]

/-- A window configuration sets exactly one state bit, one head bit,
and one symbol bit at each position. -/
@[expose] def encodeWindow (c : M.WindowConfig w) : WindowWire (M.State ⊕ Bool) M.Symbol w → Bool
  | .inl q => decide (q = c.state)
  | .inr (.inl i) => decide (i = c.head)
  | .inr (.inr (i, s)) => decide (s = c.cells i)

private abbrev StepKey (w : Nat) := (M.State ⊕ Bool) × Fin w × M.Symbol

private def stepKeys (qs : List (M.State ⊕ Bool)) (symbols : List M.Symbol) :
    List (StepKey M w) :=
  qs.flatMap fun q ↦ (List.finRange w).flatMap fun i ↦ symbols.map fun s ↦ (q, i, s)

omit [DecidableEq M.State] [DecidableEq M.Symbol] in
private theorem length_stepKeys (qs : List (M.State ⊕ Bool)) (symbols : List M.Symbol) :
    (stepKeys (w := w) M qs symbols).length = qs.length * w * symbols.length := by
  simp only [stepKeys, List.length_flatMap, List.length_map, List.map_const',
    List.sum_replicate_nat, List.length_finRange, Nat.mul_assoc]

private def activeKey (c : M.WindowConfig w) : StepKey M w :=
  (c.state, c.head, c.cells c.head)

omit [DecidableEq M.State] [DecidableEq M.Symbol] in
private theorem activeKey_mem (qs : List (M.State ⊕ Bool)) (symbols : List M.Symbol)
    (hqs : ∀ q, q ∈ qs) (hsymbols : ∀ s, s ∈ symbols) (c : M.WindowConfig w) :
    activeKey M c ∈ stepKeys M qs symbols :=
  List.mem_flatMap.mpr ⟨c.state, hqs _, List.mem_flatMap.mpr ⟨c.head, List.mem_finRange _,
    List.mem_map_of_mem (hsymbols (c.cells c.head))⟩⟩

private def event (k : StepKey M w) : Expr (WindowWire (M.State ⊕ Bool) M.Symbol w) :=
  .and (.input (.inl k.1))
    (.and (.input (.inr (.inl k.2.1))) (.input (.inr (.inr k.2))))

private theorem event_eval_eq_true (c : M.WindowConfig w) (k : StepKey M w) :
    (event M k).eval (encodeWindow M c) = true ↔ k = activeKey M c := by
  obtain ⟨q, i, s⟩ := k
  simp only [event, Expr.eval, encodeWindow, Bool.and_eq_true, decide_eq_true_eq,
    activeKey, Prod.mk.injEq]
  constructor
  · rintro ⟨rfl, rfl, h⟩
    exact ⟨rfl, rfl, h⟩
  · rintro ⟨rfl, rfl, h⟩
    exact ⟨rfl, rfl, h⟩

private def selectEvents (qs : List (M.State ⊕ Bool)) (symbols : List M.Symbol)
    (chosen : StepKey M w → Bool) : Expr (WindowWire (M.State ⊕ Bool) M.Symbol w) :=
  .any (((stepKeys M qs symbols).filter chosen).map (event M))

private theorem selectEvents_eval (qs : List (M.State ⊕ Bool)) (symbols : List M.Symbol)
    (hqs : ∀ q, q ∈ qs) (hsymbols : ∀ s, s ∈ symbols) (c : M.WindowConfig w)
    (chosen : StepKey M w → Bool) :
    (selectEvents M qs symbols chosen).eval (encodeWindow M c) = chosen (activeKey M c) := by
  apply Bool.eq_iff_iff.mpr
  rw [selectEvents, Expr.eval_any_eq_true]
  constructor
  · rintro ⟨e, he, htrue⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp he
    obtain rfl := (event_eval_eq_true M c k).mp htrue
    exact (List.mem_filter.mp hk).2
  · intro hchosen
    refine ⟨event M (activeKey M c), List.mem_map_of_mem (List.mem_filter.mpr ⟨?_, hchosen⟩), ?_⟩
    · exact activeKey_mem M qs symbols hqs hsymbols c
    · exact (event_eval_eq_true M c _).mpr rfl

omit [DecidableEq M.State] [DecidableEq M.Symbol] in
private theorem selectEvents_size_le (qs : List (M.State ⊕ Bool)) (symbols : List M.Symbol)
    (chosen : StepKey M w → Bool) :
    (selectEvents M qs symbols chosen).size ≤ 6 * (qs.length * w * symbols.length) + 1 := by
  unfold selectEvents
  refine (Expr.size_any_le _ 5 ?_).trans ?_
  · intro e he
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp he
    exact Nat.le_refl 5
  rw [List.length_map, Nat.mul_comm 6, ← length_stepKeys M qs symbols]
  exact Nat.add_le_add_right (Nat.mul_le_mul_right 6 (List.length_filter_le ..)) 1

private def advances (k : StepKey M w) : StepKey M w :=
  M.windowAdvance w k.1 k.2.1 k.2.2

private def writes (wire : WindowWire (M.State ⊕ Bool) M.Symbol w) (k : StepKey M w) : Bool :=
  match wire with
  | .inl q => decide (q = (advances M k).1)
  | .inr (.inl i) => decide (i = (advances M k).2.1)
  | .inr (.inr (i, s)) => decide (i = k.2.1 ∧ s = (advances M k).2.2)

/-- The formula for an output wire chooses a transition matching the old
state, head, and scanned symbol. Tape positions outside the old head keep
their symbol. -/
def windowStep (qs : List (M.State ⊕ Bool)) (symbols : List M.Symbol)
    (wire : WindowWire (M.State ⊕ Bool) M.Symbol w) :
    Expr (WindowWire (M.State ⊕ Bool) M.Symbol w) :=
  let written := selectEvents M qs symbols (writes M wire)
  match wire with
  | .inl _ | .inr (.inl _) => written
  | .inr (.inr (i, _)) => .or (.and (.not (.input (.inr (.inl i)))) (.input wire)) written

/-- Every output of the layer agrees with the corresponding indicator of one
bounded machine step. -/
theorem windowStep_eval (qs : List (M.State ⊕ Bool)) (symbols : List M.Symbol)
    (hqs : ∀ q, q ∈ qs) (hsymbols : ∀ s, s ∈ symbols) (c : M.WindowConfig w)
    (wire : WindowWire (M.State ⊕ Bool) M.Symbol w) :
    (windowStep M qs symbols wire).eval (encodeWindow M c) =
      encodeWindow M (M.windowTick c) wire := by
  have selected := selectEvents_eval M qs symbols hqs hsymbols c
  cases wire with
  | inl q =>
    rw [windowStep, selected]
    rfl
  | inr rest =>
    cases rest with
    | inl i =>
      rw [windowStep, selected]
      rfl
    | inr cell =>
      obtain ⟨i, s⟩ := cell
      by_cases hi : i = c.head <;>
        simp [windowStep, selected, Expr.eval, writes, advances, activeKey, encodeWindow,
          Machine.windowTick, hi]

/-- A transition formula has constant size per candidate key, plus constant
size for retaining the old cell. -/
theorem windowStep_size_le (qs : List (M.State ⊕ Bool)) (symbols : List M.Symbol)
    (wire : WindowWire (M.State ⊕ Bool) M.Symbol w) :
    (windowStep M qs symbols wire).size ≤ 6 * (qs.length * w * symbols.length) + 6 := by
  have bound := selectEvents_size_le M qs symbols (writes M wire)
  cases wire with
  | inl q => exact bound.trans (by omega)
  | inr rest =>
    cases rest with
    | inl i => exact bound.trans (by omega)
    | inr cell =>
      obtain ⟨i, s⟩ := cell
      simp only [windowStep, Expr.size]
      omega

end PvsNP.Circuits
