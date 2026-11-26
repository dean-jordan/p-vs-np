module

public import PvsNP.SAT.VerifierProgram

/-! # Counted shuttles in the single-tape verifier

The shuttle sweeps over unmarked bits and the delimiter. A return sweep
restores the formula bit at the marker and resumes at the next formula cell.
-/

@[expose] public section

namespace PvsNP.SATMachine

open Turing

theorem transition_running (q q' : Phase) (a b : Symbol) (d : Dir)
    (h : verifierTransition q a = (.inl q', b, d)) :
    verifierMachine.transition (.inr q) a = (.inl (.inr q'), b, d) := by
  change verifierProgram q a = _
  simp [verifierProgram, h]

theorem tick_right (q q' : Phase) (left right : List Symbol) (scanned written : Symbol)
    (h : verifierTransition q scanned = (.inl q', written, .right)) :
    verifierMachine.tick (phaseConfig q left (scanned :: right)) =
      phaseConfig q' (written :: left) right := by
  rw [verifierMachine.tick_tapeFromLists_cons (.inr q) left right scanned
    (transition_running q q' scanned written .right h)]
  rw [verifierMachine.move_tapeFromLists_right_cons]

theorem tick_left (q q' : Phase) (left right : List Symbol) (scanned written : Symbol)
    (h : verifierTransition q scanned = (.inl q', written, .left)) :
    verifierMachine.tick (phaseConfig q left (scanned :: right)) =
      leftOfCut q' left (written :: right) :=
  verifierMachine.tick_tapeFromLists_cons (.inr q) left right scanned
    (transition_running q q' scanned written .left h)

theorem tick_left_blank (q q' : Phase) (left : List Symbol) (written : Symbol)
    (h : verifierTransition q .blank = (.inl q', written, .left)) :
    verifierMachine.tick (phaseConfig q left []) = leftOfCut q' left [written] :=
  verifierMachine.tick_tapeFromLists_nil (.inr q) left
    (transition_running q q' .blank written .left h)

/-- Shuttles preserve both bits and the separator while crossing the input. -/
def Traversable (a : Symbol) : Prop := (∃ b, a = .bit b) ∨ a = .delimiter

theorem traversable_bits (x : BinaryWord) : ∀ a ∈ bits x, Traversable a := by
  intro a ha
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
  exact Or.inl ⟨b, rfl⟩

theorem traversable_bit_delimiter (x y : BinaryWord) :
    ∀ a ∈ bits x ++ .delimiter :: bits y, Traversable a := by
  intro a ha
  rcases List.mem_append.mp ha with h | h
  · exact traversable_bits x a h
  · rcases List.mem_cons.mp h with rfl | hb
    · exact Or.inr rfl
    · exact traversable_bits y a hb

/-- Walk from the formula marker toward the certificate marker. -/
theorem run_seek (q : SATCursor.Control) (advance : Bool) (left crossed right : List Symbol)
    (h : ∀ a ∈ crossed, Traversable a) :
    verifierMachine.run crossed.length (phaseConfig (.seek q advance) left (crossed ++ right)) =
      phaseConfig (.seek q advance) (crossed.reverse ++ left) right := by
  apply verifierMachine.run_sweep_right (.inr (.seek q advance)) crossed left right
  intro a ha
  obtain ⟨b, rfl⟩ | rfl := h a ha
  · rfl
  · rfl

/-- Return across the input segment and restore the marked formula cell. -/
theorem run_restore (q : SATCursor.Control) (restoreBit : Bool) (left crossed right : List Symbol)
    (h : ∀ a ∈ crossed, Traversable a) :
    verifierMachine.run (crossed.length + 1)
      (leftOfCut (.restore q restoreBit) (crossed.reverse ++ .formulaMark :: left) right) =
    phaseConfig (.parse q) (.bit restoreBit :: left) (crossed ++ right) := by
  have hLeft (a : Symbol) (ha : a ∈ crossed.reverse) :
      verifierMachine.transition (.inr (.restore q restoreBit)) a =
        (.inl (.inr (.restore q restoreBit)), a, .left) := by
    obtain ⟨b, rfl⟩ | rfl := h a (List.mem_reverse.mp ha)
    · rfl
    · rfl
  have hs := verifierMachine.run_sweep_left (.inr (.restore q restoreBit)) crossed.reverse
    (.formulaMark :: left) right hLeft
  have hSweep : verifierMachine.run crossed.length
      (leftOfCut (.restore q restoreBit) (crossed.reverse ++ .formulaMark :: left) right) =
      leftOfCut (.restore q restoreBit) (.formulaMark :: left) (crossed ++ right) := by
    simpa only [List.length_reverse, List.reverse_reverse] using hs
  rw [Machine.run_add, hSweep]
  change verifierMachine.tick (leftOfCut (.restore q restoreBit) (.formulaMark :: left)
    (crossed ++ right)) = _
  have hm : leftOfCut (.restore q restoreBit) (.formulaMark :: left) (crossed ++ right) =
      phaseConfig (.restore q restoreBit) left (.formulaMark :: (crossed ++ right)) := by
    unfold leftOfCut phaseConfig
    rw [verifierMachine.move_tapeFromLists_left_cons]
  rw [hm]
  exact tick_right _ _ _ _ .formulaMark (.bit restoreBit) rfl

end PvsNP.SATMachine
