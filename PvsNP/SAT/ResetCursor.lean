module

public import PvsNP.SAT.VerifierSweeps

/-! # Resetting the certificate cursor

The verifier records the sign bit in finite control, crosses the end of the
formula, and marks the first certificate cell. It returns left to the sign
cell, restores the bit, and continues parsing on the following cell.
-/

@[expose] public section

namespace PvsNP.SATMachine

private theorem tick_reset_start (f c sign : Bool) (left right : List Symbol) :
    verifierMachine.tick (phaseConfig (.parse (.sign f c)) left (.bit sign :: right)) =
      phaseConfig (.reset (.index f c sign) sign) (.formulaMark :: left) right :=
  tick_right (.parse (.sign f c)) (.reset (.index f c sign) sign) left right
    (.bit sign) .formulaMark rfl

private theorem run_reset_scan (q : SATCursor.Control) (sign : Bool)
    (left : List Symbol) (rest : BinaryWord) (right : List Symbol) :
    verifierMachine.run rest.length (phaseConfig (.reset q sign) left (bits rest ++ right)) =
      phaseConfig (.reset q sign) ((bits rest).reverse ++ left) right := by
  have h (s : Symbol) (hs : s ∈ bits rest) :
      verifierMachine.transition (.inr (.reset q sign)) s =
        (.inl (.inr (.reset q sign)), s, .right) := by
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hs
    rfl
  simpa only [List.length_map] using
    verifierMachine.run_sweep_right (.inr (.reset q sign)) (bits rest) left right h

private theorem tick_reset_delimiter (q : SATCursor.Control) (sign : Bool)
    (left right : List Symbol) :
    verifierMachine.tick (phaseConfig (.reset q sign) left (.delimiter :: right)) =
      phaseConfig (.place q sign) (.delimiter :: left) right :=
  tick_right (.reset q sign) (.place q sign) left right .delimiter .delimiter rfl

private theorem tick_reset_place (q : SATCursor.Control) (sign : Bool)
    (left : List Symbol) (assignment : BinaryWord) :
    verifierMachine.tick (phaseConfig (.place q sign) left (bits assignment)) =
      leftOfCut (.restore q sign) left (markFirst assignment) := by
  cases assignment with
  | nil => exact tick_left_blank (.place q sign) (.restore q sign) left (.certificateMark none) rfl
  | cons b assignment =>
    exact tick_left (.place q sign) (.restore q sign) left (bits assignment)
      (.bit b) (.certificateMark (some b)) rfl

/-- Process the sign and reset the certificate marker to its first cell. -/
theorem run_reset (f c sign : Bool) (left : List Symbol) (rest assignment : BinaryWord) :
    verifierMachine.run (2 * rest.length + 5)
      (phaseConfig (.parse (.sign f c)) left
        (.bit sign :: (bits rest ++ .delimiter :: bits assignment))) =
      phaseConfig (.parse (.index f c sign)) (.bit sign :: left)
        (bits rest ++ .delimiter :: markFirst assignment) := by
  let crossed : List Symbol := bits rest ++ [.delimiter]
  have clocks : 2 * rest.length + 5 = (1 + rest.length + 1 + 1) + (crossed.length + 1) := by
    simp only [crossed, List.length_append, List.length_map, List.length_cons, List.length_nil]
    omega
  rw [clocks, verifierMachine.run_add (1 + rest.length + 1 + 1) (crossed.length + 1),
    verifierMachine.run_add (1 + rest.length + 1) 1, verifierMachine.run_add (1 + rest.length) 1,
    verifierMachine.run_add 1 rest.length]
  have runOne (config : verifierMachine.Config) :
      verifierMachine.run 1 config = verifierMachine.tick config := rfl
  simp only [runOne, tick_reset_start, run_reset_scan, tick_reset_delimiter, tick_reset_place]
  simpa only [crossed, List.reverse_append, List.reverse_singleton, List.cons_append,
    List.nil_append, List.append_assoc] using
    run_restore (.index f c sign) sign left crossed (markFirst assignment)
      (traversable_bit_delimiter rest [])

end PvsNP.SATMachine
