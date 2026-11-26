module

public import PvsNP.TuringMachine.Registers.Affine
public import PvsNP.TuringMachine.Registers.ForwardLookup

/-! # Indexed reads of a strided region -/

public section

namespace PvsNP.RegisterMachine.Fragment

variable {R : Type}

/-- Read at `base + stride * offset`. The length and the two operands are preserved.
The address, lookup, multiplier, and arithmetic registers start and finish at zero. -/
def affineLookup (stride : Nat) (lanes : Fin 7 → R) (branches : Option Bool → Fragment R) :
    Fragment R :=
  ((add (lanes 1) (lanes 3) (lanes 6)).seq
    (accumulateAffine (lanes 2) (lanes 3) (lanes 5) (lanes 6) stride 0)).seq
    (forwardLookup (lanes 0) (lanes 3) (lanes 4) (lanes 6) branches)

@[expose] def affineLookupCost (stride length base offset : Nat) : Nat :=
  5 * base + 2 + affineTime stride 0 offset + forwardLookupCost length (base + stride * offset)

theorem affineLookupCost_le (stride length base offset : Nat) :
    affineLookupCost stride length base offset ≤
      7 * length + 6 * base + 6 * stride * offset + 4 * stride + 8 := by
  have hLookup := forwardLookupCost_le length (base + stride * offset)
  unfold affineLookupCost affineTime at *
  simp only [Nat.mul_add, Nat.mul_left_comm stride 5, Nat.mul_assoc, Nat.add_zero] at *
  omega

variable [DecidableEq R]

/-- A continuation sees the original registers and the bit at the computed input position.
An address beyond the input selects `none`. -/
theorem runsValues_affineLookup (stride : Nat) (lanes : Fin 7 → R)
    (hLanes : Function.Injective lanes) (branches : Option Bool → Fragment R)
    (x : BinaryWord) (before : R → Nat) (hLength : before (lanes 0) = x.length)
    (hAddress : before (lanes 3) = 0) (hWork : before (lanes 4) = 0)
    (hMultiplier : before (lanes 5) = 0) (hScratch : before (lanes 6) = 0)
    {ticks : Nat} {after : R → Nat}
    (hBody : (branches x[before (lanes 1) + stride * before (lanes 2)]?).RunsValues
      x ticks before after) :
    (affineLookup stride lanes branches).RunsValues x
      (affineLookupCost stride x.length (before (lanes 1)) (before (lanes 2)) + ticks)
      before after := by
  have distinct (i j : Fin 7) (h : i ≠ j) : lanes i ≠ lanes j := fun he ↦ h (hLanes he)
  have hCopy := runsValues_add (lanes 1) (lanes 3) (lanes 6) x before
    (distinct 1 3 (by decide)) (distinct 1 6 (by decide)) (distinct 3 6 (by decide)) hScratch
  let copied := setValue (lanes 3) (before (lanes 1)) before
  have hCopy' : (add (lanes 1) (lanes 3) (lanes 6)).RunsValues
      x (5 * before (lanes 1) + 2) before copied := by
    simpa only [hAddress, Nat.zero_add, copied] using hCopy
  let pos := before (lanes 1) + stride * before (lanes 2)
  let addressed := setValue (lanes 3) pos before
  have hOther (i : Fin 7) (hi : i ≠ 3) : copied (lanes i) = before (lanes i) :=
    setValue_other (distinct i 3 hi) _ _
  have hNodup : [lanes 2, lanes 3, lanes 5, lanes 6].Nodup :=
    ((by decide : ([2, 3, 5, 6] : List (Fin 7)).Nodup).map hLanes)
  have hAffine := runsValues_accumulateAffine (lanes 2) (lanes 3) (lanes 5) (lanes 6)
    stride 0 x copied hNodup ((hOther 5 (by decide)).trans hMultiplier)
      ((hOther 6 (by decide)).trans hScratch)
  have hAffine' : (accumulateAffine (lanes 2) (lanes 3) (lanes 5) (lanes 6) stride 0).RunsValues
      x (affineTime stride 0 (before (lanes 2))) copied addressed := by
    simpa only [hOther 2 (by decide), copied, setValue_same, Nat.add_zero, setValue_replace,
      addressed, pos] using hAffine
  have hAddressed (i : Fin 7) (hi : i ≠ 3) : addressed (lanes i) = before (lanes i) :=
    setValue_other (distinct i 3 hi) _ _
  have hRestored : setValue (lanes 3) 0 addressed = before := by
    simp only [addressed, setValue_replace, ← hAddress, setValue_current]
  have hLookup := runsValues_forwardLookup (lanes 0) (lanes 3) (lanes 4) (lanes 6)
    branches x addressed (distinct 0 4 (by decide)) (distinct 0 6 (by decide))
    (distinct 3 4 (by decide)) (distinct 4 6 (by decide))
    ((hAddressed 0 (by decide)).trans hLength) ((hAddressed 4 (by decide)).trans hWork)
    ((hAddressed 6 (by decide)).trans hScratch)
    (by simpa only [addressed, setValue_same, hRestored, pos] using hBody)
  simpa only [affineLookup, affineLookupCost, addressed, setValue_same, pos, Nat.add_assoc]
    using (hCopy'.seq hAffine').seq hLookup

end PvsNP.RegisterMachine.Fragment
