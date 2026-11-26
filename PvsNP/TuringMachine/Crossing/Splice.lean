module

public import PvsNP.TuringMachine.Crossing.Absolute

/-! # Replay two halted computations across a common tape cut -/

public section

namespace PvsNP.Machine

variable {α : Type} (M : Machine α)

private theorem absoluteConfig_eq {a b : M.AbsoluteConfig}
    (hState : a.state = b.state) (hPosition : a.position = b.position)
    (hTape : ∀ i, a.tape i = b.tape i) : a = b := by
  have ht := funext hTape
  cases a
  cases b
  cases hState
  cases hPosition
  cases ht
  rfl

private def AgreesOn (P : Int → Prop) (a b : M.AbsoluteConfig) : Prop :=
  a.state = b.state ∧ a.position = b.position ∧ ∀ i, P i → a.tape i = b.tape i

private theorem agreesOn_tick {P : Int → Prop} {a b : M.AbsoluteConfig}
    (h : AgreesOn M P a b) (hPos : P a.position) :
    AgreesOn M P (M.absoluteTick a) (M.absoluteTick b) := by
  obtain ⟨hState, hPosition, hTape⟩ := h
  have hRead := hTape a.position hPos
  cases hA : a.state with
  | inr answer =>
    have hB := hState.symm.trans hA
    simp only [absoluteTick, hA, hB]
    exact ⟨hState, hPosition, hTape⟩
  | inl q =>
    have hB := hState.symm.trans hA
    rcases hStep : M.transition q (a.tape a.position) with ⟨next, symbol, direction⟩
    have hStepB : M.transition q (b.tape b.position) = (next, symbol, direction) := by
      rwa [← hPosition, ← hRead]
    simp only [absoluteTick, hA, hB, hStep, hStepB]
    refine ⟨rfl, congrArg (fun i ↦ i + TrackCall.delta direction) hPosition, ?_⟩
    intro i hi
    dsimp only
    rw [← hPosition, hTape i hi]

private theorem tick_splice_left (cut : Int) (a b : M.AbsoluteConfig)
    (hLeft : a.position < cut) :
    M.absoluteTick (M.spliceConfig cut a b) =
      ⟨(M.absoluteTick a).state, (M.absoluteTick a).position,
        (M.spliceConfig cut (M.absoluteTick a) b).tape⟩ := by
  have same : AgreesOn M (· < cut) (M.spliceConfig cut a b) a := by
    refine ⟨?_, ?_, ?_⟩
    · simp [spliceConfig, hLeft]
    · simp [spliceConfig, hLeft]
    · intro i hi
      simp [spliceConfig, hi]
  have hAt : (M.spliceConfig cut a b).position < cut := by
    rw [same.2.1]
    exact hLeft
  obtain ⟨hState, hPosition, hTape⟩ := agreesOn_tick M same hAt
  refine absoluteConfig_eq M (by exact hState) (by exact hPosition) ?_
  intro i
  by_cases hi : i < cut
  · simpa [spliceConfig, hi] using hTape i hi
  · have hNe : i ≠ (M.spliceConfig cut a b).position := by
      intro hEq
      exact hi (hEq.symm ▸ hAt)
    rw [M.absoluteTick_tape_of_ne _ hNe]
    simp [spliceConfig, hi]

private theorem tick_splice_right (cut : Int) (a b : M.AbsoluteConfig)
    (hRightA : ¬ a.position < cut) (hRightB : ¬ b.position < cut) :
    M.absoluteTick (M.spliceConfig cut a b) =
      ⟨(M.absoluteTick b).state, (M.absoluteTick b).position,
        (M.spliceConfig cut a (M.absoluteTick b)).tape⟩ := by
  have same : AgreesOn M (fun i ↦ ¬ i < cut) (M.spliceConfig cut a b) b := by
    refine ⟨?_, ?_, ?_⟩
    · simp [spliceConfig, hRightA]
    · simp [spliceConfig, hRightA]
    · intro i hi
      simp [spliceConfig, hi]
  have hAt : ¬ (M.spliceConfig cut a b).position < cut := by
    rw [same.2.1]
    exact hRightB
  obtain ⟨hState, hPosition, hTape⟩ := agreesOn_tick M same hAt
  refine absoluteConfig_eq M (by exact hState) (by exact hPosition) ?_
  intro i
  by_cases hi : i < cut
  · have hNe : i ≠ (M.spliceConfig cut a b).position := by
      intro hEq
      exact hAt (hEq ▸ hi)
    rw [M.absoluteTick_tape_of_ne _ hNe]
    simp [spliceConfig, hi]
  · simpa [spliceConfig, hi] using hTape i hi

private theorem splice_stay_left (cut : Int) (a b : M.AbsoluteConfig)
    (hStay : a.position < cut ↔ (M.absoluteTick a).position < cut) :
    M.spliceConfig cut (M.absoluteTick a) b = M.spliceConfig cut a b ∨
    M.spliceConfig cut (M.absoluteTick a) b = M.absoluteTick (M.spliceConfig cut a b) := by
  by_cases hLeft : a.position < cut
  · right
    rw [tick_splice_left M cut a b hLeft]
    have hNext := hStay.mp hLeft
    apply absoluteConfig_eq M
    · simp [spliceConfig, hNext]
    · simp [spliceConfig, hNext]
    · intro i
      rfl
  · left
    have hNext : ¬ (M.absoluteTick a).position < cut := fun h ↦ hLeft (hStay.mpr h)
    apply absoluteConfig_eq M
    · simp [spliceConfig, hLeft, hNext]
    · simp [spliceConfig, hLeft, hNext]
    · intro i
      by_cases hi : i < cut
      · simp [spliceConfig, hi, M.absoluteTick_tape_of_ne a (show i ≠ a.position by omega)]
      · simp [spliceConfig, hi]

private theorem splice_stay_right (cut : Int) (a b : M.AbsoluteConfig)
    (hSide : a.position < cut ↔ b.position < cut) :
    M.spliceConfig cut a (M.absoluteTick b) = M.spliceConfig cut a b ∨
    M.spliceConfig cut a (M.absoluteTick b) = M.absoluteTick (M.spliceConfig cut a b) := by
  by_cases hLeft : a.position < cut
  · left
    have hLeftB := hSide.mp hLeft
    apply absoluteConfig_eq M
    · simp [spliceConfig, hLeft]
    · simp [spliceConfig, hLeft]
    · intro i
      by_cases hi : i < cut
      · simp [spliceConfig, hi]
      · simp [spliceConfig, hi, M.absoluteTick_tape_of_ne b (show i ≠ b.position by omega)]
  · right
    have hRightB : ¬ b.position < cut := fun h ↦ hLeft (hSide.mpr h)
    rw [tick_splice_right M cut a b hLeft hRightB]
    apply absoluteConfig_eq M
    · simp [spliceConfig, hLeft]
    · simp [spliceConfig, hLeft]
    · intro i
      rfl

private theorem splice_cross (cut : Int) (a b : M.AbsoluteConfig)
    (hSide : a.position < cut ↔ b.position < cut)
    (hCrossA : ¬ (a.position < cut ↔ (M.absoluteTick a).position < cut))
    (hCrossB : ¬ (b.position < cut ↔ (M.absoluteTick b).position < cut))
    (hState : (M.absoluteTick a).state = (M.absoluteTick b).state) :
    ((M.absoluteTick a).position < cut ↔ (M.absoluteTick b).position < cut) ∧
    M.spliceConfig cut (M.absoluteTick a) (M.absoluteTick b) =
      M.absoluteTick (M.spliceConfig cut a b) := by
  obtain ⟨hLowerA, hUpperA⟩ := M.absoluteTick_position_le a
  obtain ⟨hLowerB, hUpperB⟩ := M.absoluteTick_position_le b
  by_cases hLeftA : a.position < cut
  · have hLeftB := hSide.mp hLeftA
    have hRightNextA : ¬ (M.absoluteTick a).position < cut := by simpa [hLeftA] using hCrossA
    have hRightNextB : ¬ (M.absoluteTick b).position < cut := by simpa [hLeftB] using hCrossB
    have hPosition : (M.absoluteTick a).position = (M.absoluteTick b).position := by omega
    refine ⟨by rw [hPosition], ?_⟩
    rw [tick_splice_left M cut a b hLeftA]
    apply absoluteConfig_eq M
    · simpa [spliceConfig, hRightNextA] using hState.symm
    · simpa [spliceConfig, hRightNextA] using hPosition.symm
    · intro i
      by_cases hi : i < cut
      · simp [spliceConfig, hi]
      · simp [spliceConfig, hi, M.absoluteTick_tape_of_ne b (show i ≠ b.position by omega)]
  · have hRightB : ¬ b.position < cut := fun h ↦ hLeftA (hSide.mpr h)
    have hLeftNextA : (M.absoluteTick a).position < cut := by simpa [hLeftA] using hCrossA
    have hLeftNextB : (M.absoluteTick b).position < cut := by simpa [hRightB] using hCrossB
    have hPosition : (M.absoluteTick a).position = (M.absoluteTick b).position := by omega
    refine ⟨by rw [hPosition], ?_⟩
    rw [tick_splice_right M cut a b hLeftA hRightB]
    apply absoluteConfig_eq M
    · simpa [spliceConfig, hLeftNextA] using hState
    · simpa [spliceConfig, hLeftNextA] using hPosition
    · intro i
      by_cases hi : i < cut
      · simp [spliceConfig, hi, M.absoluteTick_tape_of_ne a (show i ≠ a.position by omega)]
      · simp [spliceConfig, hi]

private theorem replay_after_step {c d : M.AbsoluteConfig} {answer : Bool}
    (hStep : d = c ∨ d = M.absoluteTick c)
    (hLater : ∃ t, (M.absoluteRun t d).state = .inr answer) :
    ∃ t, (M.absoluteRun t c).state = .inr answer := by
  obtain ⟨t, ht⟩ := hLater
  rcases hStep with rfl | rfl
  · exact ⟨t, ht⟩
  · exact ⟨t + 1, ht⟩

/-- With equal crossing transcripts, splicing two runs with the same halting
answer produces a run with that answer. The two scans can spend different
numbers of ticks on each side of the cut. -/
theorem absolute_halts_splice_of_crossingTranscript_eq (cut : Int) (a b : M.AbsoluteConfig)
    (tA tB : Nat) (answer : Bool) (hSide : a.position < cut ↔ b.position < cut)
    (hA : (M.absoluteRun tA a).state = .inr answer)
    (hB : (M.absoluteRun tB b).state = .inr answer)
    (hTranscript : M.crossingTranscript cut tA a = M.crossingTranscript cut tB b) :
    ∃ t, (M.absoluteRun t (M.spliceConfig cut a b)).state = .inr answer := by
  -- Each noncrossing step advances one source; a matched crossing advances both.
  cases tA with
  | zero =>
    by_cases hLeft : a.position < cut
    · exact ⟨0, by simpa [absoluteRun, spliceConfig, hLeft] using hA⟩
    · cases tB with
      | zero => exact ⟨0, by simpa [absoluteRun, spliceConfig, hLeft] using hB⟩
      | succ tB =>
        have hStay : b.position < cut ↔ (M.absoluteTick b).position < cut := by
          by_contra hCross
          simp [crossingTranscript, hCross] at hTranscript
        have hRest : M.crossingTranscript cut 0 a =
            M.crossingTranscript cut tB (M.absoluteTick b) := by
          simpa only [crossingTranscript, ite_eq_left hStay] using hTranscript
        exact replay_after_step M (splice_stay_right M cut a b hSide)
          (absolute_halts_splice_of_crossingTranscript_eq cut a (M.absoluteTick b) 0 tB answer
            (hSide.trans hStay) hA hB hRest)
  | succ tA =>
    cases tB with
    | zero =>
      by_cases hLeft : a.position < cut
      · have hStay : a.position < cut ↔ (M.absoluteTick a).position < cut := by
          by_contra hCross
          simp [crossingTranscript, hCross] at hTranscript
        have hRest : M.crossingTranscript cut tA (M.absoluteTick a) =
            M.crossingTranscript cut 0 b := by
          simpa only [crossingTranscript, ite_eq_left hStay] using hTranscript
        exact replay_after_step M (splice_stay_left M cut a b hStay)
          (absolute_halts_splice_of_crossingTranscript_eq cut (M.absoluteTick a) b tA 0 answer
            (hStay.symm.trans hSide) hA hB hRest)
      · exact ⟨0, by simpa [absoluteRun, spliceConfig, hLeft] using hB⟩
    | succ tB =>
      by_cases hStayA : a.position < cut ↔ (M.absoluteTick a).position < cut
      · have hRest : M.crossingTranscript cut tA (M.absoluteTick a) =
            M.crossingTranscript cut (tB + 1) b := by
          rwa [crossingTranscript, ite_eq_left hStayA] at hTranscript
        exact replay_after_step M (splice_stay_left M cut a b hStayA)
          (absolute_halts_splice_of_crossingTranscript_eq cut (M.absoluteTick a) b tA (tB + 1)
            answer (hStayA.symm.trans hSide) hA hB hRest)
      · by_cases hStayB : b.position < cut ↔ (M.absoluteTick b).position < cut
        · have hRest : M.crossingTranscript cut (tA + 1) a =
              M.crossingTranscript cut tB (M.absoluteTick b) := by
            simpa only [crossingTranscript, ite_eq_left hStayB] using hTranscript
          exact replay_after_step M (splice_stay_right M cut a b hSide)
            (absolute_halts_splice_of_crossingTranscript_eq cut a (M.absoluteTick b) (tA + 1) tB
              answer (hSide.trans hStayB) hA hB hRest)
        · have hMerged := hTranscript
          simp only [crossingTranscript, ite_eq_right hStayA, ite_eq_right hStayB,
            List.cons.injEq] at hMerged
          obtain ⟨hNew, hStep⟩ := splice_cross M cut a b hSide hStayA hStayB hMerged.1
          exact replay_after_step M (Or.inr hStep)
            (absolute_halts_splice_of_crossingTranscript_eq cut (M.absoluteTick a)
              (M.absoluteTick b) tA tB answer hNew hA hB hMerged.2)
termination_by tA + tB
decreasing_by all_goals omega

end PvsNP.Machine
