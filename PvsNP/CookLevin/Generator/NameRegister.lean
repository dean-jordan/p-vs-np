module

public import PvsNP.Complexity.TimeBounds
public import PvsNP.TuringMachine.Registers.Fragments
public import PvsNP.TuringMachine.Registers.Copy
public import PvsNP.TuringMachine.Registers.Multiply

/-! # Register block for the time component of tableau names -/

@[expose] public section

namespace PvsNP.RegisterMachine.Fragment

/-- The time-copy and multiplication phases of the tableau name block. -/
inductive NameLabel where
  | takeTime | addMultiplier | saveTime | restoreTime | addBackTime
  | multiply | takeStride | addIndex | saveStride | restoreStride | addBackStride

private def nameLabelCode : NameLabel → Fin 11
  | .takeTime => 0
  | .addMultiplier => 1
  | .saveTime => 2
  | .restoreTime => 3
  | .addBackTime => 4
  | .multiply => 5
  | .takeStride => 6
  | .addIndex => 7
  | .saveStride => 8
  | .restoreStride => 9
  | .addBackStride => 10

instance : Finite NameLabel :=
  Finite.of_injective nameLabelCode (by
    intro a b h
    cases a <;> cases b <;> simp_all [nameLabelCode])

variable {R K : Type}

/-- The copy and multiplication instructions of the tableau name block. -/
def accumulateNameCode (time stride index multiplier scratch : R) :
    NameLabel → Instruction R (Option NameLabel)
  | .takeTime => .dec time (some .restoreTime) (some .addMultiplier)
  | .addMultiplier => .inc multiplier (some .saveTime)
  | .saveTime => .inc scratch (some .takeTime)
  | .restoreTime => .dec scratch (some .multiply) (some .addBackTime)
  | .addBackTime => .inc time (some .restoreTime)
  | .multiply => .dec multiplier none (some .takeStride)
  | .takeStride => .dec stride (some .restoreStride) (some .addIndex)
  | .addIndex => .inc index (some .saveStride)
  | .saveStride => .inc scratch (some .takeStride)
  | .restoreStride => .dec scratch (some .multiply) (some .addBackStride)
  | .addBackStride => .inc stride (some .restoreStride)

/-- Add `time * stride` to an existing tableau name offset. -/
def accumulateName (time stride index multiplier scratch : R) : Fragment R where
  Label := NameLabel
  entry := some .takeTime
  code := accumulateNameCode time stride index multiplier scratch

private def nameCopyRules (time stride index multiplier scratch : R) :
    CopyRules (accumulateName time stride index multiplier scratch).close
      time multiplier scratch where
  entry := some .takeTime
  addTarget := some .addMultiplier
  addScratch := some .saveTime
  restore := some .restoreTime
  addSource := some .addBackTime
  next := some .multiply
  takeSource := rfl
  writeTarget := rfl
  writeScratch := rfl
  takeScratch := rfl
  writeSource := rfl

private def nameMultiplyRules (time stride index multiplier scratch : R) :
    MultiplyRules (accumulateName time stride index multiplier scratch).close
      multiplier stride index scratch where
  entry := some .multiply
  next := none
  add := {
    entry := some .takeStride
    addTarget := some .addIndex
    addScratch := some .saveStride
    restore := some .restoreStride
    addSource := some .addBackStride
    next := some .multiply
    takeSource := rfl
    writeTarget := rfl
    writeScratch := rfl
    takeScratch := rfl
    writeSource := rfl }
  takeMultiplier := rfl
  addReturns := rfl

/-- The exact cost of copying the time and then accumulating the product. -/
def accumulateNameTime (time stride : Nat) : Nat :=
  (5 * time + 2) + (time * (5 * stride + 3) + 1)

theorem accumulateNameTime_polynomiallyBounded {time stride : Nat → Nat}
    (hTime : PolynomiallyBounded time) (hStride : PolynomiallyBounded stride) :
    PolynomiallyBounded (fun n ↦ accumulateNameTime (time n) (stride n)) :=
  (((PolynomiallyBounded.const 5).mul hTime).add (PolynomiallyBounded.const 2)).add
    ((hTime.mul (((PolynomiallyBounded.const 5).mul hStride).add
      (PolynomiallyBounded.const 3))).add (PolynomiallyBounded.const 1))

/-- Accumulate the tableau name and reach the live exit. The work registers return to zero,
and the input cursor and output are preserved. -/
theorem run_accumulateName [DecidableEq R] (x : BinaryWord)
    (time stride index multiplier scratch : R) (cfg : Config R K)
    (hDistinct : [time, stride, index, multiplier, scratch].Nodup)
    (hMultiplier : cfg.values multiplier = 0) (hScratch : cfg.values scratch = 0) :
    let block := accumulateName time stride index multiplier scratch
    block.run x (accumulateNameTime (cfg.values time) (cfg.values stride)) (block.enter cfg) =
      some { block.enter cfg with
        pc := some none
        values := fun r ↦ if r = index then
          cfg.values index + cfg.values time * cfg.values stride else cfg.values r } := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or,
    not_false_eq_true, List.nodup_nil, and_true] at hDistinct
  rcases hDistinct with
    ⟨⟨_, _, hTimeMultiplier, hTimeScratch⟩, ⟨hStrideIndex, hStrideMultiplier, hStrideScratch⟩,
      ⟨hIndexMultiplier, hIndexScratch⟩, hMultiplierScratch⟩
  let block := accumulateName time stride index multiplier scratch
  let start := block.enter cfg
  let mid : block.Cfg := { start with
    pc := some (some NameLabel.multiply)
    values := copyValues time multiplier cfg.values }
  have hCopy : block.run x (5 * cfg.values time + 2) start = some mid :=
    run_copy (nameCopyRules time stride index multiplier scratch) x
      hTimeMultiplier hTimeScratch hMultiplierScratch (cfg := start) rfl hMultiplier hScratch
  have hMidMultiplier : mid.values multiplier = cfg.values time := by
    simp [mid, copyValues]
  have hMidStride : mid.values stride = cfg.values stride := by
    simp [mid, copyValues, hStrideMultiplier]
  have hMidScratch : mid.values scratch = 0 := by
    simp [mid, copyValues, Ne.symm hMultiplierScratch, hScratch]
  have hMidIndex : mid.values index = cfg.values index := by
    simp [mid, copyValues, hIndexMultiplier]
  have hMultiply := run_multiply (nameMultiplyRules time stride index multiplier scratch) x
    (Ne.symm hStrideMultiplier) (Ne.symm hIndexMultiplier) hMultiplierScratch
    hStrideIndex hStrideScratch hIndexScratch (cfg := mid) rfl hMidScratch
  rw [hMidMultiplier, hMidStride] at hMultiply
  have hValues : multiplyValues multiplier stride index mid.values = fun r ↦
      if r = index then cfg.values index + cfg.values time * cfg.values stride
      else cfg.values r := by
    funext r
    by_cases hMul : r = multiplier
    · subst r
      simp [multiplyValues, Ne.symm hIndexMultiplier, hMultiplier]
    by_cases hIdx : r = index
    · subst r
      simp only [multiplyValues, ite_eq_right hIndexMultiplier, ite_true, hMidIndex,
        hMidMultiplier, hMidStride]
    simp [multiplyValues, mid, copyValues, hMul, hIdx]
  change RegisterMachine.run block.close x
    (accumulateNameTime (cfg.values time) (cfg.values stride)) start = _
  change RegisterMachine.run block.close x (5 * cfg.values time + 2) start = _ at hCopy
  change RegisterMachine.run block.close x
    (cfg.values time * (5 * cfg.values stride + 3) + 1) mid = _ at hMultiply
  rw [accumulateNameTime, RegisterMachine.run_add, hCopy, Option.bind_some, hMultiply, hValues]
  rfl

end PvsNP.RegisterMachine.Fragment
