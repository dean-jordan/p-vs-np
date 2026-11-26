module

public import PvsNP.MCSP.PaddedFieldRegister
public import PvsNP.TuringMachine.Registers.ReverseWindow

/-! # Read the gate count at a forward padded-description offset -/

public section

namespace PvsNP.MCSP

open Circuits RegisterMachine RegisterMachine.Fragment

/-- The offset workspace and the decoded count. -/
inductive DescriptionCountLane where
  | offset (lane : ReverseWindowLane)
  | count
  deriving DecidableEq

variable {R : Type}

private def countReaderLane : Fin 5 → DescriptionCountLane
  | 0 => .offset .position
  | 1 => .offset .widthCopy
  | 2 => .count
  | 3 => .offset .multiplier
  | _ => .offset .scratch

private theorem countReaderLane_injective : Function.Injective countReaderLane := by decide

private def clearCountPosition (lane : R) : Fragment R where
  Label := Unit
  entry := some ()
  code _ := .dec lane none (some ())

/-- Compute the reverse offset, read the count, and restore the offset workspace. -/
def descriptionCountRegister (lanes : DescriptionCountLane → R) : Fragment R :=
  let offset := lanes ∘ DescriptionCountLane.offset
  (((reverseWindowRegister 4 offset).seq (add (offset .width) (offset .widthCopy)
    (offset .scratch))).seq (stridedField 4 (lanes ∘ countReaderLane))).seq
      (clearCountPosition (offset .position))

/-- The count read has a polynomial instruction bound even if its value exceeds the gate cap. -/
@[expose] def descriptionCountRegisterCost (length base width : Nat) : Nat :=
  reverseWindowRegisterCost 4 length base width + (5 * width + 2) +
    stridedFieldCost 4 length width length + (length + 4 * width + 1)

theorem descriptionCountRegisterCost_polynomiallyBounded {length base width : Nat → Nat}
    (hLength : PolynomiallyBounded length) (hBase : PolynomiallyBounded base)
    (hWidth : PolynomiallyBounded width) :
    PolynomiallyBounded (fun n ↦ descriptionCountRegisterCost (length n) (base n) (width n)) :=
  (((reverseWindowRegisterCost_polynomiallyBounded 4 hLength hBase hWidth).add
    (((PolynomiallyBounded.const 5).mul hWidth).add (PolynomiallyBounded.const 2))).add
    (stridedFieldCost_polynomiallyBounded 4 hLength hWidth hLength)).add
    ((hLength.add ((PolynomiallyBounded.const 4).mul hWidth)).add (PolynomiallyBounded.const 1))

/-- The physical input length bounds every fixed-width count in the description window. -/
theorem circuitDescriptionCount_le_wordLength {word code : BinaryWord} {start arity cap : Nat}
    (hWindow : PaddedDescriptionWindow word code start arity cap) :
    circuitDescriptionCount arity cap code ≤ word.length := by
  have hFits : circuitFieldWidth arity cap ≤ code.length := by
    rw [hWindow.length, mergeWitnessLength]
    omega
  exact (fieldValue_le_circuitFieldWidth_cap arity cap _ (List.length_take_of_le hFits)).trans
    hWindow.capacity

variable [DecidableEq R]

private theorem runsValues_clearCountPosition (lane : R) (word : BinaryWord) (v : R → Nat) :
    (clearCountPosition lane).RunsValues word (v lane + 1) v (setValue lane 0 v) := by
  intro output
  exact run_clear word (program := (clearCountPosition lane).close) rfl
    (cfg := (clearCountPosition lane).enter (⟨none, v, none, output⟩ : Config R Unit)) rfl

/-- Read any claimed count from a padded window using its physical start and width.
The count is the only modified register. -/
theorem runsValues_descriptionCountRegister (lanes : DescriptionCountLane → R)
    (hLanes : Function.Injective lanes) {word code : BinaryWord} {start arity cap : Nat}
    (hWindow : PaddedDescriptionWindow word code start arity cap) (before : R → Nat)
    (hLength : before (lanes (.offset .inputLength)) = word.length)
    (hBase : before (lanes (.offset .base)) = start)
    (hWidth : before (lanes (.offset .width)) = circuitFieldWidth arity cap)
    (hZero : ∀ lane, lane ≠ .offset .inputLength → lane ≠ .offset .base →
      lane ≠ .offset .width → before (lanes lane) = 0) :
    ∃ ticks ≤ descriptionCountRegisterCost word.length start (circuitFieldWidth arity cap),
      (descriptionCountRegister lanes).RunsValues word ticks before
        (setValue (lanes .count) (circuitDescriptionCount arity cap code) before) := by
  let offset := lanes ∘ DescriptionCountLane.offset
  let reader := lanes ∘ countReaderLane
  let width := circuitFieldWidth arity cap
  let reverse := reverseWindowStart word.length start 4 width
  let positioned := setValue (offset .position) reverse before
  let seeded := setValue (offset .widthCopy) width positioned
  have hLane (a b : DescriptionCountLane) : lanes a = lanes b ↔ a = b :=
    ⟨fun h ↦ hLanes h, congrArg lanes⟩
  have hOffset : Function.Injective offset := hLanes.comp fun _ _ h ↦
    DescriptionCountLane.offset.inj h
  have hReader : Function.Injective reader := hLanes.comp countReaderLane_injective
  have hScratchZero := hZero (.offset .scratch) (by decide) (by decide) (by decide)
  have hCopyZero := hZero (.offset .widthCopy) (by decide) (by decide) (by decide)
  have hIndexZero := hZero (.offset .multiplier) (by decide) (by decide) (by decide)
  have hCountZero := hZero .count (by decide) (by decide) (by decide)
  have hPositionZero := hZero (.offset .position) (by decide) (by decide) (by decide)
  obtain ⟨offsetTicks, hOffsetTime, hOffsetRun⟩ :=
    runsValues_reverseWindowRegister 4 offset hOffset word before (by
      intro lane hLength hBase hWidth
      exact hZero (.offset lane) (by simpa using hLength) (by simpa using hBase)
        (by simpa using hWidth))
  change before (offset .inputLength) = word.length at hLength
  change before (offset .base) = start at hBase
  change before (offset .width) = width at hWidth
  rw [hLength, hBase, hWidth] at hOffsetTime hOffsetRun
  have hPositionedWidth : positioned (offset .width) = width := by
    simp [positioned, offset, setValue, hLane, ← hWidth]
  have hPositionedCopy : positioned (offset .widthCopy) = 0 := by
    simp [positioned, offset, setValue, hLane, hCopyZero]
  have hPositionedScratch : positioned (offset .scratch) = 0 := by
    simp [positioned, offset, setValue, hLane, hScratchZero]
  have hCopy : (add (offset .width) (offset .widthCopy) (offset .scratch)).RunsValues
      word (5 * width + 2) positioned seeded := by
    simpa only [hPositionedWidth, hPositionedCopy, Nat.zero_add, seeded] using
      runsValues_add (offset .width) (offset .widthCopy) (offset .scratch) word positioned
        (by simp [offset, hLane]) (by simp [offset, hLane]) (by simp [offset, hLane])
        hPositionedScratch
  have hSeedPos : seeded (reader 0) = reverse := by
    simp [seeded, positioned, reader, offset, countReaderLane, setValue, hLane]
  have hSeedWidth : seeded (reader 1) = width := by
    simp [seeded, reader, offset, countReaderLane]
  have hSeedCount : seeded (reader 2) = 0 := by
    simp [seeded, positioned, reader, offset, countReaderLane, setValue, hLane, hCountZero]
  have hSeedIndex : seeded (reader 3) = 0 := by
    simp [seeded, positioned, reader, offset, countReaderLane, setValue, hLane, hIndexZero]
  have hSeedScratch : seeded (reader 4) = 0 := by
    simp [seeded, positioned, reader, offset, countReaderLane, setValue, hLane, hScratchZero]
  obtain ⟨readTicks, hReadTime, read, hReadRun, hEndWidth, hEndPosition, hEndCount, hReadFrame⟩ :=
    runsValues_paddedDescriptionCount reader hReader hWindow seeded hSeedPos hSeedWidth
      hSeedCount hSeedIndex hSeedScratch
  change read (offset .widthCopy) = 0 at hEndWidth
  change read (offset .position) = seeded (reader 0) + 4 * width at hEndPosition
  change read (lanes .count) = _ at hEndCount
  let cleared := setValue (offset .position) 0 read
  have hCleared : cleared = setValue (lanes .count) (circuitDescriptionCount arity cap code)
      before := by
    funext r
    by_cases hp : r = offset .position
    · subst r
      simp [cleared, setValue, offset, hLane, hPositionZero]
    by_cases hw : r = offset .widthCopy
    · subst r
      change read (lanes (.offset .widthCopy)) = 0 at hEndWidth
      simp [cleared, setValue, offset, hLane, hCopyZero, hEndWidth]
    by_cases hc : r = lanes .count
    · subst r
      simp [cleared, setValue, offset, hLane, hEndCount]
    have hStable := hReadFrame r hp hw hc
    simp [cleared, seeded, positioned, setValue, hp, hw, hc, hStable]
  have hClear := runsValues_clearCountPosition (offset .position) word read
  change (clearCountPosition (offset .position)).RunsValues word
    (read (offset .position) + 1) read cleared at hClear
  have hPositionBound : read (offset .position) ≤ word.length + 4 * width := by
    rw [hEndPosition, hSeedPos]
    exact Nat.add_le_add_right ((Nat.sub_le ..).trans (Nat.sub_le ..)) _
  rw [hCleared] at hClear
  exact ⟨_, Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hOffsetTime (Nat.le_refl _)) hReadTime)
    (Nat.add_le_add_right hPositionBound 1), ((hOffsetRun.seq hCopy).seq hReadRun).seq hClear⟩

end PvsNP.MCSP
