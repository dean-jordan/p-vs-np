module

public import PvsNP.SAT.VerifierSweeps

/-! # Counted advance of the SAT certificate marker

A unary `1` moves the marker across one certificate bit. If the marker is
on the terminal blank, it stays there. Both cases restore the formula bit
and return to parsing at the next cell.
-/

@[expose] public section

namespace PvsNP.SATMachine

private theorem run_one (cfg : verifierMachine.Config) :
    verifierMachine.run 1 cfg = verifierMachine.tick cfg := by
  change verifierMachine.run (0 + 1) cfg = _
  rw [Machine.run_succ, Machine.run_zero]

private theorem tick_place_first (q : SATCursor.Control) (restoreBit : Bool)
    (left : List Symbol) (tail : BinaryWord) :
    verifierMachine.tick (phaseConfig (.place q restoreBit) left (bits tail)) =
      leftOfCut (.restore q restoreBit) left (markFirst tail) := by
  cases tail with
  | nil =>
    exact tick_left_blank (.place q restoreBit) (.restore q restoreBit)
      left (.certificateMark none) rfl
  | cons a tail =>
    exact tick_left (.place q restoreBit) (.restore q restoreBit)
      left (bits tail) (.bit a) (.certificateMark (some a)) rfl

/-- A unary `1` advances the marked assignment cursor, clamping it at the
end blank, in at most two traversals of the intervening tape plus seven ticks. -/
theorem run_advance (f c sign : Bool) (left : List Symbol)
    (rest before after : BinaryWord) :
    ∃ t ≤ 2 * (rest.length + before.length) + 7,
      verifierMachine.run t
        (phaseConfig (.parse (.index f c sign)) left
          (.bit true :: (bits rest ++ .delimiter :: (bits before ++ markFirst after)))) =
      phaseConfig (.parse (.index f c sign)) (.bit true :: left)
        (bits rest ++ .delimiter :: (match after with
          | [] => bits before ++ markFirst []
          | a :: tail => bits (before ++ [a]) ++ markFirst tail)) := by
  let q := SATCursor.Control.index f c sign
  let crossed := bits rest ++ .delimiter :: bits before
  have hCross : ∀ a ∈ crossed, Traversable a := traversable_bit_delimiter rest before
  have hLen : crossed.length = rest.length + before.length + 1 := by
    simp only [crossed, List.length_append, List.length_cons, List.length_map]
    omega
  have hAppend (tail : List Symbol) :
      crossed ++ tail = bits rest ++ .delimiter :: (bits before ++ tail) := by
    simp [crossed, List.append_assoc]
  have hSeek : verifierMachine.run (1 + crossed.length)
      (phaseConfig (.parse q) left (.bit true :: (crossed ++ markFirst after))) =
      phaseConfig (.seek q true) (crossed.reverse ++ .formulaMark :: left) (markFirst after) := by
    rw [Machine.run_add, run_one,
      tick_right (.parse q) (.seek q true) left (crossed ++ markFirst after)
      (.bit true) .formulaMark rfl]
    exact run_seek q true (.formulaMark :: left) crossed (markFirst after) hCross
  rw [← hAppend (markFirst after)]
  cases after with
  | nil =>
    refine ⟨1 + crossed.length + 1 + (crossed.length + 1), by omega, ?_⟩
    rw [verifierMachine.run_add (1 + crossed.length + 1) (crossed.length + 1),
      verifierMachine.run_add (1 + crossed.length) 1, hSeek, run_one]
    change verifierMachine.run (crossed.length + 1)
      (verifierMachine.tick
        (phaseConfig (.seek q true) (crossed.reverse ++ .formulaMark :: left)
          [.certificateMark none])) = _
    rw [tick_left (.seek q true) (.restore q true) (crossed.reverse ++ .formulaMark :: left)
      [] (.certificateMark none) (.certificateMark none) rfl]
    simpa only [hAppend, markFirst] using
      run_restore q true left crossed [Symbol.certificateMark none] hCross
  | cons a tail =>
    let extended := crossed ++ [Symbol.bit a]
    have hExtended : ∀ s ∈ extended, Traversable s := by
      intro s hs
      rcases List.mem_append.mp hs with hs | hs
      · exact hCross s hs
      · exact Or.inl ⟨a, List.mem_singleton.mp hs⟩
    have hReverse :
        .bit a :: (crossed.reverse ++ .formulaMark :: left) =
          extended.reverse ++ .formulaMark :: left := by
      simp [extended, List.reverse_append]
    have hExtendedLength : extended.length = crossed.length + 1 := by
      simp [extended]
    have hOutput : extended ++ markFirst tail =
        bits rest ++ .delimiter :: (bits (before ++ [a]) ++ markFirst tail) := by
      simp [extended, crossed, List.map_append, List.append_assoc]
    refine ⟨1 + crossed.length + 1 + 1 + (extended.length + 1), by omega, ?_⟩
    rw [verifierMachine.run_add (1 + crossed.length + 1 + 1) (extended.length + 1),
      verifierMachine.run_add (1 + crossed.length + 1) 1,
      verifierMachine.run_add (1 + crossed.length) 1, hSeek, run_one, run_one]
    change verifierMachine.run (extended.length + 1)
      (verifierMachine.tick (verifierMachine.tick
        (phaseConfig (.seek q true) (crossed.reverse ++ .formulaMark :: left)
          (.certificateMark (some a) :: bits tail)))) = _
    rw [tick_right (.seek q true) (.place q true) (crossed.reverse ++ .formulaMark :: left)
      (bits tail) (.certificateMark (some a)) (.bit a) rfl, hReverse, tick_place_first]
    simpa only [hOutput] using run_restore q true left extended (markFirst tail) hExtended

end PvsNP.SATMachine
