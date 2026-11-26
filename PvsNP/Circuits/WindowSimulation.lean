module

public import PvsNP.Circuits.WindowInput
public import PvsNP.Complexity.TimeBounds
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum

import Mathlib.Data.Fintype.EquivFin

/-! # Layered circuits for bounded runs of Cook machines -/

public section

namespace PvsNP.Circuits

section Generic

variable {α : Type} (M : Machine α) [Fintype M.State] [Fintype M.Symbol]

/-- The number of state, head, and tape symbol bits for a window. -/
abbrev windowBitCount (w : Nat) : Nat :=
  Fintype.card (WindowWire (M.State ⊕ Bool) M.Symbol w)

theorem windowBitCount_eq (w : Nat) :
    windowBitCount M w = Fintype.card (M.State ⊕ Bool) + (w + w * Fintype.card M.Symbol) := by
  simp only [windowBitCount, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]

/-- Number the one-hot wires of a window. -/
noncomputable def windowIndex (w : Nat) :
    WindowWire (M.State ⊕ Bool) M.Symbol w ≃ Fin (windowBitCount M w) :=
  Fintype.equivFin _

theorem windowBitCount_polynomiallyBounded {width : Nat → Nat}
    (hWidth : PolynomiallyBounded width) :
    PolynomiallyBounded (fun n ↦ windowBitCount M (width n)) := by
  let c := PolynomiallyBounded.const
  simpa only [windowBitCount_eq] using
    (c (Fintype.card (M.State ⊕ Bool))).add (hWidth.add (hWidth.mul (c (Fintype.card M.Symbol))))

private def stepGateBound (w : Nat) : Nat :=
  windowBitCount M w * (6 * (Fintype.card (M.State ⊕ Bool) * w * Fintype.card M.Symbol) + 6)

private theorem stepGateBound_polynomiallyBounded {width : Nat → Nat}
    (hWidth : PolynomiallyBounded width) :
    PolynomiallyBounded (fun n ↦ stepGateBound M (width n)) := by
  let c := PolynomiallyBounded.const
  let q := Fintype.card (M.State ⊕ Bool)
  let s := Fintype.card M.Symbol
  have hBits := windowBitCount_polynomiallyBounded M hWidth
  have hExpr := ((c 6).mul (((c q).mul hWidth).mul (c s))).add (c 6)
  exact hBits.mul hExpr

/-- Upper bound for the transition and acceptance gates, after initialization. -/
def machineWindowGateOverhead (T : Nat) : Nat := T * stepGateBound M (2 * T + 1) + 1

theorem machineWindowGateOverhead_polynomiallyBounded {clock : Nat → Nat}
    (hClock : PolynomiallyBounded clock) :
    PolynomiallyBounded (fun n ↦ machineWindowGateOverhead M (clock n)) := by
  let c := PolynomiallyBounded.const
  have hWidth := ((c 2).mul hClock).add (c 1)
  exact (hClock.mul (stepGateBound_polynomiallyBounded M hWidth)).add (c 1)

private noncomputable def enumerate (α : Type) [Fintype α] : List α :=
  List.ofFn (Fintype.equivFin α).symm

private theorem mem_enumerate {α : Type} [Fintype α] (a : α) : a ∈ enumerate α :=
  List.mem_ofFn.mpr ⟨Fintype.equivFin α a, (Fintype.equivFin α).symm_apply_apply a⟩

variable [DecidableEq M.State] [DecidableEq M.Symbol]

private noncomputable def stepLayer (w : Nat) :
    Layer (windowBitCount M w) (windowBitCount M w) :=
  fun i ↦ (windowStep M (enumerate (M.State ⊕ Bool)) (enumerate M.Symbol)
    ((windowIndex M w).symm i)).rename (windowIndex M w)

private noncomputable def acceptLayer (w : Nat) : Layer (windowBitCount M w) 1 :=
  fun _ ↦ .input (windowIndex M w (.inl (.inr true)))

private theorem stepLayer_eval {w : Nat} (c : M.WindowConfig w) :
    (stepLayer M w).eval (encodeWindow M c ∘ (windowIndex M w).symm) =
      encodeWindow M (M.windowTick c) ∘ (windowIndex M w).symm := by
  funext i
  have hNames :
      (encodeWindow M c ∘ (windowIndex M w).symm) ∘ windowIndex M w = encodeWindow M c := by
    funext wire
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
  simp only [Layer.eval, stepLayer, Expr.eval_rename, hNames, Function.comp_apply]
  exact windowStep_eval M _ _ mem_enumerate mem_enumerate c _

private theorem repeat_stepLayer_eval {w : Nat} (t : Nat) (c : M.WindowConfig w) :
    (Layered.repeatLayer (stepLayer M w) t).eval
      (encodeWindow M c ∘ (windowIndex M w).symm) =
      encodeWindow M (M.windowRun t c) ∘ (windowIndex M w).symm := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Layered.eval_repeatLayer_succ, ih, stepLayer_eval, Machine.windowRun_succ]

/-- Run the machine from the window values supplied by an initialization layer. -/
noncomputable def windowRunFromLayered {n w : Nat} (T : Nat)
    (first : Layer n (windowBitCount M w)) : Layered n (windowBitCount M w) :=
  .cons first (Layered.repeatLayer (stepLayer M w) T)

theorem windowRunFromLayered_eval {n w : Nat} (T : Nat)
    (first : Layer n (windowBitCount M w)) (x : Fin n → Bool) (cfg : M.WindowConfig w)
    (hInit : first.eval x = encodeWindow M cfg ∘ (windowIndex M w).symm) :
    (windowRunFromLayered M T first).eval x =
      encodeWindow M (M.windowRun T cfg) ∘ (windowIndex M w).symm := by
  simp only [windowRunFromLayered, Layered.eval, hInit, repeat_stepLayer_eval]

private theorem stepLayer_size_le (w : Nat) : (stepLayer M w).size ≤ stepGateBound M w := by
  unfold stepGateBound
  apply Layer.size_le_of_forall
  intro i
  simp only [stepLayer, Expr.size_rename]
  simpa only [enumerate, List.length_ofFn] using
    windowStep_size_le M (enumerate (M.State ⊕ Bool)) (enumerate M.Symbol)
      ((windowIndex M w).symm i)

private theorem windowRunFromLayered_size_le {n w : Nat} (T : Nat)
    (first : Layer n (windowBitCount M w)) :
    (windowRunFromLayered M T first).size ≤ first.size + T * stepGateBound M w := by
  simp only [windowRunFromLayered, Layered.size, Layered.size_repeatLayer]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left T (stepLayer_size_le M w)) first.size

private theorem windowRunFromLayered_size_polynomiallyBounded {width clock : Nat → Nat}
    (first : ∀ n, Layer n (windowBitCount M (width n)))
    (hFirst : PolynomiallyBounded (fun n ↦ (first n).size))
    (hWidth : PolynomiallyBounded width) (hClock : PolynomiallyBounded clock) :
    PolynomiallyBounded (fun n ↦ (windowRunFromLayered M (clock n) (first n)).size) :=
  (hFirst.add (hClock.mul (stepGateBound_polynomiallyBounded M hWidth))).mono
    (fun n ↦ windowRunFromLayered_size_le M (clock n) (first n))

omit [DecidableEq M.State] [DecidableEq M.Symbol] in
private theorem acceptLayer_size_le (w : Nat) : (acceptLayer M w).size ≤ 1 := by
  simpa only [Nat.one_mul] using Layer.size_le_of_forall (acceptLayer M w) 1 (fun _ ↦ Nat.le_refl _)

/-- Run for `T` ticks from the supplied initialization layer and read the accept wire. -/
noncomputable def machineFromWindowLayered {n : Nat} (T : Nat)
    (first : Layer n (windowBitCount M (2 * T + 1))) : Layered n 1 :=
  (windowRunFromLayered M T first).append (.cons (acceptLayer M (2 * T + 1)) (.id 1))

theorem machineFromWindowLayered_eval {n : Nat} (T : Nat)
    (first : Layer n (windowBitCount M (2 * T + 1))) (x : Fin n → Bool)
    (cfg : M.WindowConfig (2 * T + 1))
    (hInit : first.eval x = encodeWindow M cfg ∘ (windowIndex M (2 * T + 1)).symm) :
    (machineFromWindowLayered M T first).eval x 0 = true ↔
      (M.windowRun T cfg).state = .inr true := by
  rw [machineFromWindowLayered, Layered.eval_append,
    windowRunFromLayered_eval M T first x cfg hInit]
  simp only [Layered.eval, Layer.eval, acceptLayer, Expr.eval, Function.comp_apply,
    Equiv.symm_apply_apply, encodeWindow, decide_eq_true_eq]
  exact eq_comm

theorem machineFromWindowLayered_size_le {n : Nat} (T : Nat)
    (first : Layer n (windowBitCount M (2 * T + 1))) :
    (machineFromWindowLayered M T first).size ≤ first.size + machineWindowGateOverhead M T := by
  have hRun := windowRunFromLayered_size_le M T first
  have hAccept := acceptLayer_size_le M (2 * T + 1)
  simp only [machineFromWindowLayered, Layered.size_append, Layered.size, Nat.add_zero,
    machineWindowGateOverhead, ← Nat.add_assoc]
  exact Nat.add_le_add hRun hAccept

theorem machineFromWindowLayered_size_polynomiallyBounded {clock : Nat → Nat}
    (first : ∀ n, Layer n (windowBitCount M (2 * clock n + 1)))
    (hFirst : PolynomiallyBounded (fun n ↦ (first n).size))
    (hClock : PolynomiallyBounded clock) :
    PolynomiallyBounded (fun n ↦ (machineFromWindowLayered M (clock n) (first n)).size) :=
  (hFirst.add (machineWindowGateOverhead_polynomiallyBounded M hClock)).mono
    (fun n ↦ machineFromWindowLayered_size_le M (clock n) (first n))

end Generic

section Binary

variable (M : Machine Bool) [Fintype M.State] [Fintype M.Symbol]
variable [DecidableEq M.State] [DecidableEq M.Symbol]

private noncomputable def startLayer {w : Nat} (n : Nat) (start : Fin w) :
    Layer n (windowBitCount M w) :=
  fun i ↦ windowStartExpr M n start ((windowIndex M w).symm i)

private theorem startLayer_eval {w n : Nat} (start : Fin w) (x : Fin n → Bool) :
    (startLayer M n start).eval x =
      encodeWindow M (M.windowStart start (List.ofFn x)) ∘ (windowIndex M w).symm := by
  funext i
  exact windowStartExpr_eval M start x _

private theorem startLayer_size_le {w : Nat} (n : Nat) (start : Fin w) :
    (startLayer M n start).size ≤ windowBitCount M w * 8 :=
  Layer.size_le_of_forall _ 8 (fun _ ↦ windowStartExpr_size_le M n start _)

private theorem startLayer_size_polynomiallyBounded {width : Nat → Nat}
    (start : ∀ n, Fin (width n)) (hWidth : PolynomiallyBounded width) :
    PolynomiallyBounded (fun n ↦ (startLayer M n (start n)).size) :=
  ((windowBitCount_polynomiallyBounded M hWidth).mul (PolynomiallyBounded.const 8)).mono
    (fun n ↦ startLayer_size_le M n (start n))

/-- Load a finite window and perform exactly the allotted ticks from the given head. -/
noncomputable def windowRunLayered (n : Nat) {w : Nat} (start : Fin w) (T : Nat) :
    Layered n (windowBitCount M w) :=
  windowRunFromLayered M T (startLayer M n start)

theorem windowRunLayered_eval {n w : Nat} (start : Fin w) (T : Nat) (x : Fin n → Bool) :
    (windowRunLayered M n start T).eval x =
      encodeWindow M (M.windowRun T (M.windowStart start (List.ofFn x))) ∘
        (windowIndex M w).symm :=
  windowRunFromLayered_eval M T (startLayer M n start) x _ (startLayer_eval M start x)

theorem windowRunLayered_size_le (n : Nat) {w : Nat} (start : Fin w) (T : Nat) :
    (windowRunLayered M n start T).size ≤ windowBitCount M w * 8 + T * (windowBitCount M w *
      (6 * (Fintype.card (M.State ⊕ Bool) * w * Fintype.card M.Symbol) + 6)) :=
  (windowRunFromLayered_size_le M T (startLayer M n start)).trans
    (Nat.add_le_add_right (startLayer_size_le M n start) _)

/-- A family of runs with polynomial window width and clock has polynomial size. -/
theorem windowRunLayered_size_polynomiallyBounded {width clock : Nat → Nat}
    (start : ∀ n, Fin (width n)) (hWidth : PolynomiallyBounded width)
    (hClock : PolynomiallyBounded clock) :
    PolynomiallyBounded (fun n ↦ (windowRunLayered M n (start n) (clock n)).size) :=
  windowRunFromLayered_size_polynomiallyBounded M
    (fun n ↦ startLayer M n (start n)) (startLayer_size_polynomiallyBounded M start hWidth)
    hWidth hClock

/-- Load the finite window, perform exactly the allotted ticks, and read the accept wire. -/
noncomputable def machineLayered (n T : Nat) : Layered n 1 :=
  machineFromWindowLayered M T (startLayer M n (Machine.windowCenter T))

/-- The circuit reads the actual machine state after the allotted physical ticks. -/
theorem machineLayered_eval (n T : Nat) (x : Fin n → Bool) :
    (machineLayered M n T).eval x 0 = true ↔
      (M.run T (M.start (List.ofFn x))).state = .inr true := by
  rw [machineLayered, machineFromWindowLayered_eval M T _ x _
    (startLayer_eval M (Machine.windowCenter T) x)]
  rw [M.windowRun_start_state T T (Nat.le_refl _) (List.ofFn x)]

/-- Explicit count for initialization, the repeated transition layer, and the accept output. -/
theorem machineLayered_size_le (n T : Nat) :
    let w := 2 * T + 1
    (machineLayered M n T).size ≤ windowBitCount M w * 8 + T * (windowBitCount M w *
      (6 * (Fintype.card (M.State ⊕ Bool) * w * Fintype.card M.Symbol) + 6)) + 1 := by
  have hRun := machineFromWindowLayered_size_le M T (startLayer M n (Machine.windowCenter T))
  have hStart := startLayer_size_le M n (Machine.windowCenter T)
  simp only [machineLayered]
  exact hRun.trans (Nat.add_le_add_right hStart (machineWindowGateOverhead M T))

/-- Any polynomial number of Cook ticks yields layered circuits of polynomial size. -/
theorem machineLayered_size_polynomiallyBounded {clock : Nat → Nat}
    (hClock : PolynomiallyBounded clock) :
    PolynomiallyBounded (fun n ↦ (machineLayered M n (clock n)).size) := by
  let c := PolynomiallyBounded.const
  have hWidth := ((c 2).mul hClock).add (c 1)
  let start (n : Nat) := Machine.windowCenter (clock n)
  exact machineFromWindowLayered_size_polynomiallyBounded M
    (fun n ↦ startLayer M n (start n)) (startLayer_size_polynomiallyBounded M start hWidth) hClock

end Binary

end PvsNP.Circuits
