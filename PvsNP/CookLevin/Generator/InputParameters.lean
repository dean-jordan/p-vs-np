module

public import PvsNP.CookLevin.VerifierTableau
public import PvsNP.TuringMachine.Registers.ValueRuns

/-! # Register prelude for the input parameters

The prelude counts the input, computes the certificate capacity, and adds
the length of the longest encoded instance–certificate pair.
-/

@[expose] public section

namespace PvsNP.CookLevin

open RegisterMachine

/-- The registers used to initialize the verifier tableau dimensions. -/
inductive ParameterLane where
  | length | capacity | pairBound | horizon | width | stride | work | scratch
  deriving DecidableEq

variable {R K : Type}

/-- Initialize the input length, certificate capacity, and largest pair length. -/
abbrev inputParameters (lanes : ParameterLane ↪ R) (k : Nat) : Fragment R :=
  (Fragment.inputLength (lanes .length)).seq
    ((Fragment.power (lanes .length) (lanes .capacity) (lanes .work) (lanes .scratch) k).seq
      ((Fragment.add (lanes .length) (lanes .pairBound) (lanes .scratch)).seq
        ((Fragment.incrementBy (lanes .pairBound) 1).seq
          (Fragment.add (lanes .capacity) (lanes .pairBound) (lanes .scratch)))))

/-- The exact abstract instruction count of the input prelude. -/
def inputParameterTime (n k : Nat) : Nat :=
  (2 * n + 1) + ((1 + powerTailTime n 1 k) + ((5 * n + 2) + (1 + (5 * n ^ k + 2))))

theorem inputParameterTime_polynomiallyBounded (k : Nat) :
    PolynomiallyBounded (fun n ↦ inputParameterTime n k) := by
  let constant := PolynomiallyBounded.const
  let length := PolynomiallyBounded.id
  have count := ((constant 2).mul length).add (constant 1)
  have power := (constant 1).add (powerTailTime_polynomiallyBounded length (constant 1) k)
  have addLength := ((constant 5).mul length).add (constant 2)
  have addCapacity := ((constant 5).mul (length.pow k)).add (constant 2)
  exact count.add (power.add (addLength.add ((constant 1).add addCapacity)))

private theorem different_lanes (lanes : ParameterLane ↪ R) {a b : ParameterLane}
    (h : a ≠ b) : lanes a ≠ lanes b := fun heq ↦ h (lanes.injective heq)

variable [DecidableEq R]

/-- The input prelude only initializes the three input parameters. -/
def inputParameterValues (lanes : ParameterLane ↪ R) (n k : Nat) : R → Nat :=
  setValue (lanes .pairBound) (inputBound n k)
    (setValue (lanes .capacity) (n ^ k) (setValue (lanes .length) n (fun _ ↦ 0)))

@[simp] theorem inputParameterValues_length (lanes : ParameterLane ↪ R) (n k : Nat) :
    inputParameterValues lanes n k (lanes .length) = n := by
  rw [inputParameterValues, setValue_other (different_lanes lanes (by decide :
    ParameterLane.length ≠ .pairBound)), setValue_other (different_lanes lanes (by decide :
      ParameterLane.length ≠ .capacity)), setValue_same]

@[simp] theorem inputParameterValues_capacity (lanes : ParameterLane ↪ R) (n k : Nat) :
    inputParameterValues lanes n k (lanes .capacity) = n ^ k := by
  rw [inputParameterValues, setValue_other (different_lanes lanes (by decide :
    ParameterLane.capacity ≠ .pairBound)), setValue_same]

@[simp] theorem inputParameterValues_pairBound (lanes : ParameterLane ↪ R) (n k : Nat) :
    inputParameterValues lanes n k (lanes .pairBound) = inputBound n k :=
  setValue_same ..

theorem inputParameterValues_other (lanes : ParameterLane ↪ R) (n k : Nat) {r : R}
    (hLength : r ≠ lanes .length) (hCapacity : r ≠ lanes .capacity)
    (hPairBound : r ≠ lanes .pairBound) : inputParameterValues lanes n k r = 0 := by
  rw [inputParameterValues, setValue_other hPairBound, setValue_other hCapacity,
    setValue_other hLength]

private theorem setValue_overwrite (r : R) (a b : Nat) (values : R → Nat) :
    setValue r b (setValue r a values) = setValue r b values := by
  funext s
  by_cases h : s = r <;> simp [setValue, h]

/-- The linked prelude preserves output and leaves the cursor unmarked. -/
theorem runsValues_inputParameters (lanes : ParameterLane ↪ R) (k : Nat) (x : BinaryWord) :
    Fragment.RunsValues (inputParameters lanes k) x (inputParameterTime x.length k)
      (fun _ ↦ 0) (inputParameterValues lanes x.length k) := by
  let n := x.length
  let length := lanes .length
  let capacity := lanes .capacity
  let pairBound := lanes .pairBound
  let work := lanes .work
  let scratch := lanes .scratch
  have capacity_ne_length : capacity ≠ length := different_lanes lanes (by decide)
  have capacity_ne_work : capacity ≠ work := different_lanes lanes (by decide)
  have capacity_ne_scratch : capacity ≠ scratch := different_lanes lanes (by decide)
  have length_ne_work : length ≠ work := different_lanes lanes (by decide)
  have length_ne_scratch : length ≠ scratch := different_lanes lanes (by decide)
  have work_ne_scratch : work ≠ scratch := different_lanes lanes (by decide)
  have length_ne_pairBound : length ≠ pairBound := different_lanes lanes (by decide)
  have capacity_ne_pairBound : capacity ≠ pairBound := different_lanes lanes (by decide)
  have pairBound_ne_scratch : pairBound ≠ scratch := different_lanes lanes (by decide)
  let initial : R → Nat := fun _ ↦ 0
  let counted := setValue length n initial
  let powered := setValue capacity (n ^ k) counted
  let lengthAdded := setValue pairBound n powered
  let separatorAdded := setValue pairBound (n + 1) powered
  have countedLength : counted length = n := setValue_same ..
  have poweredLength : powered length = n :=
    (setValue_other capacity_ne_length.symm ..).trans countedLength
  have poweredCapacity : powered capacity = n ^ k := setValue_same ..
  have poweredOther {r : R} (hCapacity : r ≠ capacity) (hLength : r ≠ length) :
      powered r = 0 := (setValue_other hCapacity ..).trans (setValue_other hLength ..)
  have countRun : Fragment.RunsValues (Fragment.inputLength length) x (2 * n + 1)
      initial counted := by
    simpa only [initial, counted, Nat.zero_add] using
      Fragment.runsValues_inputLength length x initial
  have powerRun := Fragment.runsValues_power length capacity work scratch k x counted
    capacity_ne_length capacity_ne_work capacity_ne_scratch length_ne_work length_ne_scratch
    work_ne_scratch (setValue_other capacity_ne_length ..)
    (setValue_other length_ne_work.symm ..) (setValue_other length_ne_scratch.symm ..)
  rw [countedLength] at powerRun
  have addLengthRun : Fragment.RunsValues (Fragment.add length pairBound scratch) x
      (5 * n + 2) powered lengthAdded := by
    have h := Fragment.runsValues_add length pairBound scratch x powered length_ne_pairBound
      length_ne_scratch pairBound_ne_scratch
      (poweredOther capacity_ne_scratch.symm length_ne_scratch.symm)
    simpa only [poweredLength, poweredOther capacity_ne_pairBound.symm length_ne_pairBound.symm,
      Nat.zero_add, lengthAdded] using h
  have addSeparatorRun : Fragment.RunsValues (Fragment.incrementBy pairBound 1) x
      1 lengthAdded separatorAdded := by
    have h := Fragment.runsValues_incrementBy pairBound 1 x lengthAdded
    have atPair : lengthAdded pairBound = n := setValue_same ..
    rw [atPair] at h
    simpa only [lengthAdded, separatorAdded, setValue_overwrite] using h
  have addCapacityRun : Fragment.RunsValues (Fragment.add capacity pairBound scratch) x
      (5 * n ^ k + 2) separatorAdded (inputParameterValues lanes n k) := by
    have hScratch : separatorAdded scratch = 0 :=
      (setValue_other pairBound_ne_scratch.symm ..).trans
        (poweredOther capacity_ne_scratch.symm length_ne_scratch.symm)
    have readCapacity : separatorAdded capacity = n ^ k :=
      (setValue_other capacity_ne_pairBound ..).trans poweredCapacity
    have readPair : separatorAdded pairBound = n + 1 := setValue_same ..
    have h := Fragment.runsValues_add capacity pairBound scratch x separatorAdded
      capacity_ne_pairBound capacity_ne_scratch pairBound_ne_scratch hScratch
    rw [readCapacity, readPair] at h
    simpa only [separatorAdded, setValue_overwrite, inputParameterValues, inputBound] using h
  exact countRun.seq (powerRun.seq (addLengthRun.seq (addSeparatorRun.seq addCapacityRun)))

/-- Run the input prelude from any configuration with zero registers and no mark. -/
theorem run_inputParameters (lanes : ParameterLane ↪ R) (k : Nat) (x : BinaryWord)
    (cfg : Config R K) (hZero : ∀ r, cfg.values r = 0) (hCursor : cfg.cursor = none) :
    (inputParameters lanes k).run x (inputParameterTime x.length k)
        ((inputParameters lanes k).enter cfg) =
      some ⟨some none, inputParameterValues lanes x.length k, none, cfg.output⟩ := by
  have hValues : cfg.values = fun _ ↦ 0 := funext hZero
  simpa only [Fragment.enter, hValues, hCursor] using
    runsValues_inputParameters lanes k x cfg.output

end PvsNP.CookLevin
