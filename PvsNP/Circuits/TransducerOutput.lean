module

public import PvsNP.Circuits.WindowSimulation
public import PvsNP.Circuits.WordBuffer
public import PvsNP.TuringMachine.Transducer

/-! # Output buffers for bounded runs of Cook transducers -/

public section

namespace PvsNP.Circuits

variable (M : Machine Bool)

private def outputWidth (T B : Nat) : Nat := 2 * T + B + 1

private def outputStart (T B : Nat) : Fin (outputWidth T B) :=
  ⟨T, by simp only [outputWidth]; omega⟩

private def readTerm {w : Nat} (offset : Nat) (s : M.Symbol) (head : Fin w) :
    Expr (WindowWire (M.State ⊕ Bool) M.Symbol w) :=
  if h : head.val + offset < w then
    .and (.input (.inr (.inl head))) (.input (.inr (.inr (⟨head.val + offset, h⟩, s))))
  else .const false

private def readRelative (w offset : Nat) (s : M.Symbol) :
    Expr (WindowWire (M.State ⊕ Bool) M.Symbol w) :=
  .any ((List.finRange w).map (readTerm M offset s))

private theorem readRelative_size_le (w offset : Nat) (s : M.Symbol) :
    (readRelative M w offset s).size ≤ 4 * w + 1 := by
  have hSize : ∀ e ∈ (List.finRange w).map (readTerm M offset s), e.size ≤ 3 := by
    intro e he
    obtain ⟨head, _, rfl⟩ := List.mem_map.mp he
    unfold readTerm
    split <;> simp [Expr.size]
  unfold readRelative
  simpa only [List.length_map, List.length_finRange, Nat.mul_comm 4] using
    Expr.size_any_le _ 3 hSize

private theorem readRelative_eval [DecidableEq M.State] [DecidableEq M.Symbol] {w : Nat}
    (cfg : M.WindowConfig w) (offset : Nat) (s : M.Symbol) (hFits : cfg.head.val + offset < w) :
    (readRelative M w offset s).eval (encodeWindow M cfg) =
      decide (s = cfg.cells ⟨cfg.head.val + offset, hFits⟩) := by
  apply Bool.eq_iff_iff.mpr
  rw [readRelative, Expr.eval_any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨e, he, hEval⟩
    obtain ⟨head, _, rfl⟩ := List.mem_map.mp he
    by_cases h : head.val + offset < w
    · simp only [readTerm, dite_eq_left h, Expr.eval, encodeWindow, Bool.and_eq_true,
        decide_eq_true_eq] at hEval
      obtain ⟨rfl, hRead⟩ := hEval
      exact hRead
    · simp only [readTerm, dite_eq_right h, Expr.eval, Bool.false_eq_true] at hEval
  · intro hRead
    refine ⟨readTerm M offset s cfg.head, List.mem_map_of_mem (List.mem_finRange _), ?_⟩
    simp [readTerm, hFits, Expr.eval, encodeWindow, hRead]

variable [Fintype M.State] [Fintype M.Symbol]

private noncomputable def outputLayer (w B : Nat) : Layer (windowBitCount M w) (B + B) :=
  fun i ↦ (bufferByHalves
    (fun j : Fin B ↦ readRelative M w j.val (M.input true))
    (fun j : Fin B ↦ .not (readRelative M w j.val M.blank)) i).rename (windowIndex M w)

private theorem outputLayer_size_le (w B : Nat) :
    (outputLayer M w B).size ≤ (B + B) * (4 * w + 2) := by
  apply Layer.size_le_of_forall
  intro i
  simp only [outputLayer, Expr.size_rename, bufferByHalves]
  split
  · exact (readRelative_size_le M w i.val (M.input true)).trans (Nat.le_succ _)
  · simp only [Expr.size]
    exact Nat.add_le_add_right (readRelative_size_le M w (i.val - B) M.blank) 1

variable [DecidableEq M.State] [DecidableEq M.Symbol]

/-- Run the machine and read `B` data wires and `B` presence wires at the final head. -/
noncomputable def machineOutputLayered (n T B : Nat) : Layered n (B + B) :=
  (windowRunLayered M n (outputStart T B) T).append
    (.cons (outputLayer M (outputWidth T B) B) (.id (B + B)))

/-- A canonical output tape yields the data and presence bits of its word buffer. -/
theorem machineOutputLayered_eval (n T B : Nat) (x : Fin n → Bool) (y : BinaryWord)
    (hOutput : M.OutputsAt (List.ofFn x) y T) :
    (machineOutputLayered M n T B).eval x = wordBuffer B y := by
  let w := outputWidth T B
  let cfg := M.windowRun T (M.windowStart (outputStart T B) (List.ofFn x))
  rw [machineOutputLayered, Layered.eval_append, windowRunLayered_eval]
  change (outputLayer M w B).eval (encodeWindow M cfg ∘ (windowIndex M w).symm) = wordBuffer B y
  have hNames :
      (encodeWindow M cfg ∘ (windowIndex M w).symm) ∘ windowIndex M w = encodeWindow M cfg := by
    funext wire
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
  have hHeadBound : cfg.head.val ≤ 2 * T := by
    have h := M.windowRun_head_le T (M.windowStart (outputStart T B) (List.ofFn x))
    change cfg.head.val ≤ T + T at h
    omega
  have hFits (j : Fin B) : cfg.head.val + j.val < w := by
    have hj := j.isLt
    dsimp [w, outputWidth]
    omega
  obtain ⟨head, hProjected⟩ := M.windowRun_project T (outputStart T B) (M.start (List.ofFn x))
    (Nat.le_refl _) (by change T + T < 2 * T + B + 1; omega)
  change cfg = M.windowProject head (M.run T (M.start (List.ofFn x))) at hProjected
  have hCell (j : Fin B) : cfg.cells ⟨cfg.head.val + j.val, hFits j⟩ =
      (y[j.val]?.map M.input).getD M.blank := by
    let idx : Fin w := ⟨cfg.head.val + j.val, hFits j⟩
    have hHead : cfg.head.val = head.val :=
      congrArg (fun c : M.WindowConfig w ↦ c.head.val) hProjected
    have hOffset : (idx.val : Int) - (head.val : Int) = (j.val : Int) := by
      change ((cfg.head.val + j.val : Nat) : Int) - (head.val : Int) = (j.val : Int)
      omega
    calc
      cfg.cells idx = (M.windowProject head (M.run T (M.start (List.ofFn x)))).cells idx :=
        congrArg (fun c : M.WindowConfig w ↦ c.cells idx) hProjected
      _ = @Turing.Tape.nth _ M.tapeInhabited (M.run T (M.start (List.ofFn x))).tape
          ((idx.val : Int) - head.val) := M.windowProject_cells head idx _
      _ = (y[j.val]?.map M.input).getD M.blank := by
        rw [hOffset, hOutput.2, M.wordTape_nth_nat]
  apply buffer_ext
  · intro j
    simp only [Layer.eval, outputLayer, bufferByHalves_data, Expr.eval_rename, hNames,
      wordBuffer_data]
    rw [readRelative_eval M cfg j.val (M.input true) (hFits j), hCell]
    have hDistinct : M.input true ≠ M.input false := fun h ↦ Bool.noConfusion (M.input.injective h)
    cases hGet : y[j.val]? with
    | none => simp [M.input_ne_blank true]
    | some bit => cases bit <;> simp [hDistinct]
  · intro j
    simp only [Layer.eval, outputLayer, bufferByHalves_present, Expr.eval_rename, hNames,
      Expr.eval, wordBuffer_present]
    rw [readRelative_eval M cfg j.val M.blank (hFits j), hCell]
    cases hGet : y[j.val]? with
    | none =>
      have hOutside := Nat.not_lt.mpr (List.getElem?_eq_none_iff.mp hGet)
      simp [hOutside]
    | some bit =>
      have hInside := (List.getElem?_eq_some_iff.mp hGet).choose
      have hNonblank : M.blank ≠ M.input bit := (M.input_ne_blank bit).symm
      simp [hInside, hNonblank]

/-- Polynomial clocks and output limits give polynomial size for the output circuit. -/
theorem machineOutputLayered_size_polynomiallyBounded {clock bound : Nat → Nat}
    (hClock : PolynomiallyBounded clock) (hBound : PolynomiallyBounded bound) :
    PolynomiallyBounded (fun n ↦ (machineOutputLayered M n (clock n) (bound n)).size) := by
  let c := PolynomiallyBounded.const
  have hWidth : PolynomiallyBounded (fun n ↦ outputWidth (clock n) (bound n)) :=
    (((c 2).mul hClock).add hBound).add (c 1)
  have hRun := windowRunLayered_size_polynomiallyBounded M
    (fun n ↦ outputStart (clock n) (bound n)) hWidth hClock
  have hOutput := (hBound.add hBound).mul (((c 4).mul hWidth).add (c 2))
  refine (hRun.add hOutput).mono fun n ↦ ?_
  simp only [machineOutputLayered, Layered.size_append, Layered.size, Nat.add_zero]
  exact Nat.add_le_add_left (outputLayer_size_le M (outputWidth (clock n) (bound n)) (bound n)) _

end PvsNP.Circuits
