module

public import PvsNP.TuringMachine.Registers.OutputRuns

/-! # Accumulating a fixed affine expression in a register -/

@[expose] public section

namespace PvsNP.RegisterMachine.Fragment

variable {R : Type}

/-- Add a fixed multiple of `source` and a fixed constant to `target`. -/
abbrev accumulateAffine (source target multiplier scratch : R) (coefficient constant : Nat) :
    Fragment R :=
  ((incrementBy multiplier coefficient).seq (multiply multiplier source target scratch)).seq
    (incrementBy target constant)

/-- The coefficient and offset are fixed at compile time. -/
def affineTime (coefficient constant value : Nat) : Nat :=
  coefficient + (coefficient * (5 * value + 3) + 1) + constant

theorem affineTime_mono (coefficient constant : Nat) {a b : Nat} (h : a ≤ b) :
    affineTime coefficient constant a ≤ affineTime coefficient constant b := by
  have hMul := Nat.mul_le_mul_left coefficient (show 5 * a + 3 ≤ 5 * b + 3 by omega)
  unfold affineTime
  omega

theorem affineTime_polynomiallyBounded (coefficient constant : Nat) {value : Nat → Nat}
    (h : PolynomiallyBounded value) :
    PolynomiallyBounded (fun n ↦ affineTime coefficient constant (value n)) := by
  let lit := PolynomiallyBounded.const
  exact (((lit coefficient).add (((lit coefficient).mul (((lit 5).mul h).add (lit 3))).add
    (lit 1))).add (lit constant))

variable [DecidableEq R]

/-- Restore both work registers while accumulating the affine expression. -/
theorem runsValues_accumulateAffine (source target multiplier scratch : R)
    (coefficient constant : Nat) (x : BinaryWord) (v : R → Nat)
    (hLanes : [source, target, multiplier, scratch].Nodup)
    (hMultiplier : v multiplier = 0) (hScratch : v scratch = 0) :
    (accumulateAffine source target multiplier scratch coefficient constant).RunsValues x
      (affineTime coefficient constant (v source)) v
      (setValue target (v target + coefficient * v source + constant) v) := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or,
    not_false_eq_true, List.nodup_nil, and_true] at hLanes
  obtain ⟨⟨hST, hSM, hSS⟩, ⟨hTM, hTS⟩, hMS⟩ := hLanes
  let loaded := setValue multiplier coefficient v
  have hLoad : (incrementBy multiplier coefficient).RunsValues x coefficient v loaded := by
    simpa only [hMultiplier, Nat.zero_add, loaded] using
      runsValues_incrementBy multiplier coefficient x v
  have hLoadedScratch : loaded scratch = 0 :=
    (setValue_other (Ne.symm hMS) coefficient v).trans hScratch
  have hRun := runsValues_multiply multiplier source target scratch x loaded (Ne.symm hSM)
    (Ne.symm hTM) hMS hST hSS hTS hLoadedScratch
  have hRestore : setValue multiplier 0 loaded = v := by
    dsimp only [loaded]
    rw [setValue_replace, ← hMultiplier, setValue_current]
  simp only [show loaded multiplier = coefficient from setValue_same ..,
    show loaded source = v source from setValue_other hSM ..,
    show loaded target = v target from setValue_other hTM .., hRestore] at hRun
  let multiplied := setValue target (v target + coefficient * v source) v
  have hOffset := runsValues_incrementBy target constant x multiplied
  simpa only [accumulateAffine, affineTime, multiplied, setValue_same, setValue_replace] using
    (hLoad.seq hRun).seq hOffset

end PvsNP.RegisterMachine.Fragment
