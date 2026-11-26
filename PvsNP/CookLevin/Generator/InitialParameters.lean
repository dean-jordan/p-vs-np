module

public import PvsNP.TuringMachine.Registers.OutputRuns

/-! # Boundary registers for the initial tape section -/

@[expose] public section

namespace PvsNP.CookLevin

open RegisterMachine Fragment

/-- Registers used to calculate the two certificate boundaries and the cell name base. -/
inductive InitialParameterLane where
  | length | offset | capacity | width | lower | upper | base | scratch
  deriving DecidableEq

variable {R : Type} (lanes : InitialParameterLane ↪ R)

local notation "N" => lanes InitialParameterLane.length
local notation "T" => lanes InitialParameterLane.offset
local notation "C" => lanes InitialParameterLane.capacity
local notation "W" => lanes InitialParameterLane.width
local notation "Lo" => lanes InitialParameterLane.lower
local notation "Hi" => lanes InitialParameterLane.upper
local notation "B" => lanes InitialParameterLane.base
local notation "S" => lanes InitialParameterLane.scratch

/-- Work lanes begin at zero. -/
structure InitialParametersReady (v : R → Nat) : Prop where
  lower : v Lo = 0
  upper : v Hi = 0
  base : v B = 0
  scratch : v S = 0

/-- Initialize the certificate interval and the base of the cell names at time zero. -/
abbrev initialParametersFragment (states : Nat) : Fragment R :=
  let lower := ((add T Lo S).seq (add N Lo S)).seq (incrementBy Lo 1)
  let upper := (add Lo Hi S).seq (add C Hi S)
  let base := (add W B S).seq (incrementBy B states)
  (lower.seq upper).seq base

/-- Exact count, grouped as the lower bound, upper bound and name base. -/
def initialParametersTime (length offset capacity width states : Nat) : Nat :=
  ((5 * offset + 2) + (5 * length + 2) + 1) +
    ((5 * (offset + length + 1) + 2) + (5 * capacity + 2)) + ((5 * width + 2) + states)

theorem initialParametersTime_polynomiallyBounded (states : Nat)
    {length offset capacity width : Nat → Nat} (hn : PolynomiallyBounded length)
    (ht : PolynomiallyBounded offset) (hc : PolynomiallyBounded capacity)
    (hw : PolynomiallyBounded width) :
    PolynomiallyBounded (fun n ↦ initialParametersTime (length n) (offset n)
      (capacity n) (width n) states) := by
  let lit := PolynomiallyBounded.const
  have copy {f : Nat → Nat} (h : PolynomiallyBounded f) :
      PolynomiallyBounded (fun n ↦ 5 * f n + 2) := ((lit 5).mul h).add (lit 2)
  exact (((copy ht).add (copy hn)).add (lit 1)).add
    ((copy ((ht.add hn).add (lit 1))).add (copy hc)) |>.add ((copy hw).add (lit states))

variable [DecidableEq R]

/-- The lower, upper, and base registers are the only registers changed. -/
def initialParametersValues (states : Nat) (v : R → Nat) : R → Nat :=
  let lower := v T + v N + 1
  setValue B (v W + states) (setValue Hi (lower + v C) (setValue Lo lower v))

/-- The finite initial-parameter program computes its declared valuation. -/
theorem run_initialParametersFragment (states : Nat) (x : BinaryWord) (v : R → Nat)
    (h : InitialParametersReady lanes v) :
    (initialParametersFragment lanes states).RunsValues x
      (initialParametersTime (v N) (v T) (v C) (v W) states) v
      (initialParametersValues lanes states v) := by
  let w₁ := setValue Lo (v T) v
  let w₂ := setValue Lo (v T + v N) v
  let a := v T + v N + 1
  let w₃ := setValue Lo a v
  let w₄ := setValue Hi a w₃
  let w₅ := setValue Hi (a + v C) w₃
  let w₆ := setValue B (v W) w₅
  have h₁ := runsValues_add T Lo S x v (by simp) (by simp) (by simp) h.scratch
  rw [h.lower, Nat.zero_add] at h₁
  have h₂ : (add N Lo S).RunsValues x (5 * v N + 2) w₁ w₂ := by
    have hn : w₁ N = v N := by simp [w₁, setValue]
    have hRun := runsValues_add N Lo S x w₁ (by simp) (by simp) (by simp)
      (by simpa [w₁, setValue] using h.scratch)
    simpa only [hn, w₁, w₂, setValue_same, setValue_replace] using hRun
  have h₃ : (incrementBy Lo 1).RunsValues x 1 w₂ w₃ := by
    simpa only [w₂, w₃, a, setValue_same, setValue_replace] using
      runsValues_incrementBy Lo 1 x w₂
  have h₄ : (add Lo Hi S).RunsValues x (5 * a + 2) w₃ w₄ := by
    have hUp : w₃ Hi = 0 := by simpa [w₃, setValue] using h.upper
    have hRun := runsValues_add Lo Hi S x w₃ (by simp) (by simp) (by simp)
      (by simpa [w₃, setValue] using h.scratch)
    simpa only [hUp, w₃, w₄, setValue_same, Nat.zero_add] using hRun
  have h₅ : (add C Hi S).RunsValues x (5 * v C + 2) w₄ w₅ := by
    have hCap : w₄ C = v C := by simp [w₄, w₃, setValue]
    have hRun := runsValues_add C Hi S x w₄ (by simp) (by simp) (by simp)
      (by simpa [w₄, w₃, setValue] using h.scratch)
    simpa only [hCap, w₄, w₅, setValue_same, setValue_replace] using hRun
  have h₆ : (add W B S).RunsValues x (5 * v W + 2) w₅ w₆ := by
    have hWidth : w₅ W = v W := by simp [w₅, w₃, setValue]
    have hBase : w₅ B = 0 := by simpa [w₅, w₃, setValue] using h.base
    have hRun := runsValues_add W B S x w₅ (by simp) (by simp) (by simp)
      (by simpa [w₅, w₃, setValue] using h.scratch)
    simpa only [hWidth, hBase, w₆, Nat.zero_add] using hRun
  have h₇ : (incrementBy B states).RunsValues x states w₆
      (initialParametersValues lanes states v) := by
    simpa only [w₆, w₅, w₃, initialParametersValues, a, setValue_same, setValue_replace] using
      runsValues_incrementBy B states x w₆
  exact (((h₁.seq h₂).seq h₃).seq (h₄.seq h₅)).seq (h₆.seq h₇)

end PvsNP.CookLevin
