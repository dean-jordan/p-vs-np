module

public import PvsNP.CookLevin.VariableNames
public import PvsNP.TuringMachine.Registers.ValueRuns

/-! # Computing the dense atom name stride -/

@[expose] public section

namespace PvsNP.CookLevin

open RegisterMachine

variable {R : Type}

/-- Count head and symbol slots by multiplication, then add the state slots. -/
def strideParameter (width stride work scratch : R) (states symbols : Nat) : Fragment R :=
  let factor := Fragment.incrementBy work (symbols + 1)
  let slots := Fragment.multiply work width stride scratch
  let stateSlots := Fragment.incrementBy stride states
  (factor.seq slots).seq stateSlots

/-- Exact instruction count given the width already stored in its register. -/
def strideParameterTime (widthValue states symbols : Nat) : Nat :=
  symbols + 1 + ((symbols + 1) * (5 * widthValue + 3) + 1) + states

theorem strideParameterTime_polynomiallyBounded {width : Nat → Nat}
    (hWidth : PolynomiallyBounded width) (states symbols : Nat) :
    PolynomiallyBounded (fun n ↦ strideParameterTime (width n) states symbols) := by
  let lit := PolynomiallyBounded.const
  have slots := ((lit (symbols + 1)).mul (((lit 5).mul hWidth).add (lit 3))).add (lit 1)
  exact ((lit (symbols + 1)).add slots).add (lit states)

variable [DecidableEq R]

/-- The stride calculation restores the work registers and preserves every other value. -/
theorem runsValues_strideParameter (width stride work scratch : R) (states symbols : Nat)
    (x : BinaryWord) (before : R → Nat)
    (hWorkWidth : work ≠ width) (hWorkStride : work ≠ stride) (hWorkScratch : work ≠ scratch)
    (hWidthStride : width ≠ stride) (hWidthScratch : width ≠ scratch)
    (hStrideScratch : stride ≠ scratch)
    (hWork : before work = 0) (hStride : before stride = 0) (hScratch : before scratch = 0) :
    (strideParameter width stride work scratch states symbols).RunsValues x
      (strideParameterTime (before width) states symbols) before
      (setValue stride (Tableau.atomStride states (before width) symbols) before) := by
  let withFactor := setValue work (symbols + 1) before
  let product := (symbols + 1) * before width
  have hFactor : (Fragment.incrementBy work (symbols + 1)).RunsValues x (symbols + 1)
      before withFactor := by
    simpa only [hWork, Nat.zero_add] using Fragment.runsValues_incrementBy work (symbols + 1)
      x before
  have hWithWork : withFactor work = symbols + 1 := setValue_same ..
  have hWithWidth : withFactor width = before width := setValue_other hWorkWidth.symm ..
  have hWithScratch : withFactor scratch = 0 :=
    (setValue_other hWorkScratch.symm ..).trans hScratch
  have hWithStride : withFactor stride = 0 :=
    (setValue_other hWorkStride.symm ..).trans hStride
  have hRestore : setValue work 0 withFactor = before := by
    funext r
    by_cases h : r = work <;> simp [setValue, withFactor, h, hWork]
  have hSlots := Fragment.runsValues_multiply work width stride scratch x withFactor
    hWorkWidth hWorkStride hWorkScratch hWidthStride hWidthScratch hStrideScratch hWithScratch
  rw [hWithWork, hWithWidth, hWithStride, Nat.zero_add, hRestore] at hSlots
  have hStates := Fragment.runsValues_incrementBy stride states x
    (setValue stride product before)
  rw [setValue_same] at hStates
  have hFinal : setValue stride (product + states) (setValue stride product before) =
      setValue stride (Tableau.atomStride states (before width) symbols) before := by
    have hProduct : product + states = Tableau.atomStride states (before width) symbols := by
      simp only [product, Tableau.atomStride, Nat.add_mul, Nat.one_mul]
      rw [Nat.mul_comm symbols (before width)]
      omega
    rw [hProduct]
    funext r
    by_cases h : r = stride <;> simp [setValue, h]
  rw [hFinal] at hStates
  exact (hFactor.seq hSlots).seq hStates

end PvsNP.CookLevin
