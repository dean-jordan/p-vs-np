module

public import PvsNP.SAT.VerifierSweeps

/-! # Reading and releasing the certificate cursor

The terminal unary bit reads the marked certificate cell, restores it, and
returns to the next formula cell. At the end blank the read defaults to false.
-/

@[expose] public section

namespace PvsNP.SATMachine

open Turing

private theorem tick_release (f c sign : Bool) (left : List Symbol) (after : BinaryWord) :
    verifierMachine.tick (phaseConfig (.seek (.index f c sign) false) left (markFirst after)) =
      leftOfCut (.restore (.clause f (c || SATCursor.literalValue sign after.head?)) false)
        left (bits after) := by
  cases after with
  | nil =>
    let q := SATCursor.Control.clause f (c || SATCursor.literalValue sign none)
    have hTick := tick_left (.seek (.index f c sign) false) (.restore q false)
      left [] (.certificateMark none) .blank rfl
    have hBlank := verifierMachine.tapeFromLists_right_blank left
    exact hTick.trans (congrArg (fun t ↦ (⟨.inl (.inr (.restore q false)),
      @Tape.move _ verifierMachine.tapeInhabited .left t⟩ : verifierMachine.Config)) hBlank)
  | cons value after =>
    exact tick_left (.seek (.index f c sign) false)
      (.restore (.clause f (c || SATCursor.literalValue sign (some value))) false)
      left (bits after) (.certificateMark (some value)) (.bit value) rfl

/-- Read the certificate for the terminal unary bit, remove its marker, and
return to the following formula cell in two sweeps and three additional moves. -/
theorem run_release (f c sign : Bool) (left : List Symbol) (rest before after : BinaryWord) :
    verifierMachine.run (2 * (rest.length + before.length) + 5)
      (phaseConfig (.parse (.index f c sign)) left
        (.bit false :: (bits rest ++ .delimiter :: (bits before ++ markFirst after)))) =
      phaseConfig (.parse (.clause f (c || SATCursor.literalValue sign after.head?)))
        (.bit false :: left) (bits rest ++ .delimiter :: bits (before ++ after)) := by
  let q := SATCursor.Control.index f c sign
  let next := SATCursor.Control.clause f (c || SATCursor.literalValue sign after.head?)
  let crossed := bits rest ++ .delimiter :: bits before
  have hCross : ∀ a ∈ crossed, Traversable a := traversable_bit_delimiter rest before
  have hLen : crossed.length = rest.length + before.length + 1 := by
    simp only [crossed, List.length_append, List.length_cons, List.length_map]
    omega
  have hAppend (tail : List Symbol) :
      crossed ++ tail = bits rest ++ .delimiter :: (bits before ++ tail) := by
    simp [crossed, List.append_assoc]
  have hSeek : verifierMachine.run (1 + crossed.length)
      (phaseConfig (.parse q) left (.bit false :: (crossed ++ markFirst after))) =
      phaseConfig (.seek q false) (crossed.reverse ++ .formulaMark :: left) (markFirst after) := by
    rw [Machine.run_add]
    change verifierMachine.run crossed.length (verifierMachine.tick
      (phaseConfig (.parse q) left (.bit false :: (crossed ++ markFirst after)))) = _
    rw [tick_right (.parse q) (.seek q false) left (crossed ++ markFirst after)
      (.bit false) .formulaMark rfl]
    exact run_seek q false (.formulaMark :: left) crossed (markFirst after) hCross
  have clocks : 2 * (rest.length + before.length) + 5 =
      (1 + crossed.length + 1) + (crossed.length + 1) := by omega
  rw [← hAppend (markFirst after), clocks,
    verifierMachine.run_add (1 + crossed.length + 1) (crossed.length + 1),
    verifierMachine.run_add (1 + crossed.length) 1, hSeek]
  change verifierMachine.run (crossed.length + 1) (verifierMachine.tick
    (phaseConfig (.seek (.index f c sign) false)
      (crossed.reverse ++ .formulaMark :: left) (markFirst after))) = _
  rw [tick_release]
  simpa only [hAppend, List.map_append] using
    run_restore next false left crossed (bits after) hCross

end PvsNP.SATMachine
