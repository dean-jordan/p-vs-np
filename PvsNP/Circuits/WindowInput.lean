module

public import PvsNP.Circuits.WindowStep

/-! # Input formulas for a Cook machine's finite tape window -/

public section

namespace PvsNP.Circuits

section Mapped

variable {α : Type} (M : Machine α) [DecidableEq M.Symbol]

private def inputSymbolExpr (bit : Bool → α) {n : Nat} (j : Fin n) (s : M.Symbol) :
    Expr (Fin n) :=
  .or (.and (.input j) (.const (decide (s = M.input (bit true)))))
    (.and (.not (.input j)) (.const (decide (s = M.input (bit false)))))

private theorem inputSymbolExpr_eval (bit : Bool → α) {n : Nat} (j : Fin n) (s : M.Symbol)
    (x : Fin n → Bool) :
    (inputSymbolExpr M bit j s).eval x = decide (s = M.input (bit (x j))) := by
  cases h : x j <;> simp [inputSymbolExpr, Expr.eval, h]

omit [DecidableEq M.Symbol] in
private theorem windowStart_cells_getElem? {w : Nat} (start i : Fin w) (word : List α) :
    (M.windowStart start word).cells i = if start.val ≤ i.val then
      (word[i.val - start.val]?.map M.input).getD M.blank else M.blank := by
  have hStart := M.windowStart_cells_ofFn start i (fun j : Fin word.length ↦ word[j.val])
  simp only [List.ofFn_getElem] at hStart
  rw [hStart]
  by_cases hLeft : start.val ≤ i.val
  · by_cases hIndex : i.val - start.val < word.length <;> simp [hLeft, hIndex]
  · simp [hLeft]

variable [DecidableEq M.State]

/-- Compute one initial wire from mapped input bits followed by a fixed suffix. -/
def windowMappedStartExpr (bit : Bool → α) (suffix : List α) {w : Nat} (n : Nat) (start : Fin w) :
    WindowWire (M.State ⊕ Bool) M.Symbol w → Expr (Fin n)
  | .inl q => .const (decide (q = (.inl M.initial : M.State ⊕ Bool)))
  | .inr (.inl i) => .const (decide (i = start))
  | .inr (.inr (i, s)) =>
    if h : start.val ≤ i.val ∧ i.val - start.val < n then
      inputSymbolExpr M bit ⟨i.val - start.val, h.2⟩ s
    else
      let symbol := if start.val ≤ i.val then
        (suffix[i.val - start.val - n]?.map M.input).getD M.blank else M.blank
      .const (decide (s = symbol))

/-- The input and suffix formulas give the one-hot bits of the real initial window. -/
theorem windowMappedStartExpr_eval (bit : Bool → α) (suffix : List α) {w n : Nat}
    (start : Fin w) (x : Fin n → Bool)
    (wire : WindowWire (M.State ⊕ Bool) M.Symbol w) :
    (windowMappedStartExpr M bit suffix n start wire).eval x =
      encodeWindow M (M.windowStart start ((List.ofFn x).map bit ++ suffix)) wire := by
  rcases wire with q | (i | ⟨i, s⟩)
  · rfl
  · rfl
  · change (windowMappedStartExpr M bit suffix n start (.inr (.inr (i, s)))).eval x =
      decide (s = (M.windowStart start ((List.ofFn x).map bit ++ suffix)).cells i)
    rw [windowStart_cells_getElem? M start i]
    by_cases hLeft : start.val ≤ i.val
    · have hLength : ((List.ofFn x).map bit).length = n := by
        simp only [List.length_map, List.length_ofFn]
      by_cases hBit : i.val - start.val < n
      · have hHere : start.val ≤ i.val ∧ i.val - start.val < n := ⟨hLeft, hBit⟩
        have hInside : i.val - start.val < ((List.ofFn x).map bit).length := by
          simpa only [hLength] using hBit
        rw [ite_eq_left hLeft, List.getElem?_append_left hInside]
        simp only [windowMappedStartExpr, dite_eq_left hHere, inputSymbolExpr_eval,
          List.getElem?_map, List.getElem?_ofFn, dite_eq_left hBit, Option.map_some,
          Option.getD_some]
      · have hNotHere : ¬ (start.val ≤ i.val ∧ i.val - start.val < n) := fun h ↦ hBit h.2
        have hAfter : ((List.ofFn x).map bit).length ≤ i.val - start.val := by
          simpa only [hLength] using Nat.le_of_not_gt hBit
        rw [ite_eq_left hLeft, List.getElem?_append_right hAfter, hLength]
        simp only [windowMappedStartExpr, dite_eq_right hNotHere, ite_eq_left hLeft,
          Expr.eval]
    · have hNotHere : ¬ (start.val ≤ i.val ∧ i.val - start.val < n) := fun h ↦ hLeft h.1
      simp only [windowMappedStartExpr, dite_eq_right hNotHere, ite_eq_right hLeft,
        Expr.eval]

theorem windowMappedStartExpr_size_le (bit : Bool → α) (suffix : List α)
    {w : Nat} (n : Nat) (start : Fin w)
    (wire : WindowWire (M.State ⊕ Bool) M.Symbol w) :
    (windowMappedStartExpr M bit suffix n start wire).size ≤ 8 := by
  rcases wire with q | (i | ⟨i, s⟩)
  · change 1 ≤ 8
    decide
  · change 1 ≤ 8
    decide
  · by_cases h : start.val ≤ i.val ∧ i.val - start.val < n
    · simp only [windowMappedStartExpr, dite_eq_left h, inputSymbolExpr, Expr.size]
      decide
    · simp only [windowMappedStartExpr, dite_eq_right h, Expr.size]
      decide

end Mapped

variable (M : Machine Bool) [DecidableEq M.Symbol] [DecidableEq M.State]

/-- Compute one initial configuration wire directly from the input bits. -/
def windowStartExpr {w : Nat} (n : Nat) (start : Fin w) :
    WindowWire (M.State ⊕ Bool) M.Symbol w → Expr (Fin n) :=
  windowMappedStartExpr M id [] n start

/-- All initial wires have the exact one-hot values of the real initial window. -/
theorem windowStartExpr_eval {w n : Nat} (start : Fin w) (x : Fin n → Bool)
    (wire : WindowWire (M.State ⊕ Bool) M.Symbol w) :
    (windowStartExpr M n start wire).eval x =
      encodeWindow M (M.windowStart start (List.ofFn x)) wire := by
  simpa only [windowStartExpr, List.map_id, List.append_nil] using
    windowMappedStartExpr_eval M id [] start x wire

theorem windowStartExpr_size_le {w : Nat} (n : Nat) (start : Fin w)
    (wire : WindowWire (M.State ⊕ Bool) M.Symbol w) :
    (windowStartExpr M n start wire).size ≤ 8 :=
  windowMappedStartExpr_size_le M id [] n start wire

end PvsNP.Circuits
