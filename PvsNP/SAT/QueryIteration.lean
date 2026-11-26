module

public import PvsNP.SAT.QueryBuffer
public import PvsNP.SAT.QueryIterationRules

/-! # Correctness of one physical query iteration -/

@[expose] public section

namespace PvsNP.SATSearch

open TrackCall TrackCall.QueryEdit Turing

variable {D : Machine Bool} {ρ : Type} [Finite ρ] [Inhabited ρ]
variable {C : Controller D (Cell ρ)} {labels : StepLabels C.State}
variable {stop left right : ρ → Bool}

/-- Given the unary stop and workspace edges on the auxiliary track, one
iteration appends the false trial, loads and runs it, and commits the sign
selected by the answer. The physical configuration is ready at the origin. -/
theorem run_query_iteration (rules : StepRules C labels stop (queryLayout D left right))
    (word : BinaryWord) (i L R clock : Nat)
    {tape : C.compile.Tape} {work : Int → D.Symbol} {data : Int → Cell ρ}
    (hTracks : TracksAt D ρ tape 0 work data) (hBuffer : QueryBuffer data word none)
    (hBlank : Loader.BlankOutside D (Cell ρ) tape L R)
    (hEdgesLeft : ∀ a : Int, left (data a).1 = true ↔ a = -(L : Int))
    (hEdgesRight : ∀ a : Int, right (data a).1 = decide (a = (R : Int)))
    (hStop : ∀ a : Nat, a ≤ i →
      stop (data ((word.dropLast.length : Int) + 3 + (a : Int))).1 = decide (a = i))
    (hPositive : 0 < R) (hFit : (appendUnitQuery word i false).length ≤ R + 1)
    (hLeftClock : clock ≤ L) (hRightClock : clock ≤ R)
    (hClock : D.HaltsWithin (appendUnitQuery word i false) clock) :
    let j := word.dropLast.length
    let trialData := writeEdits (j : Int) (appendEdits i) data
    ∃ (answer : Bool) (ticks : Nat) (nextWork : Int → D.Symbol),
      ticks ≤ queryStepBound j i L R clock ∧
      let final := C.compile.run ticks ⟨.inl (.inl labels.append.seekTail), tape⟩
      let nextData := updateCell ((j + 2 : Nat) : Int) (ordinary (!answer)) trialData
      final.state = .inl (.inl labels.next) ∧
      TracksAt D ρ final.tape 0 nextWork nextData ∧
      QueryBuffer nextData (appendUnitQuery word i (!answer)) none ∧
      Loader.BlankOutside D (Cell ρ) final.tape L R ∧
      (answer = true ↔ D.Accepts (appendUnitQuery word i false)) := by
  dsimp only
  let j := word.dropLast.length
  let appendTicks := 2 * (j + i + 6) + 2
  let trialData := writeEdits (j : Int) (appendEdits i) data
  let trialWord := appendUnitQuery word i false
  let start : C.compile.Config := ⟨.inl (.inl labels.append.seekTail), tape⟩
  have hTail (a : Int) (_ : 0 ≤ a) (ha : a < (j : Int)) : tail (data a) = false := by
    rw [hBuffer.tail_mark]
    exact decide_eq_false_iff_not.mpr (ne_of_lt ha)
  have hTailAt : tail (data (j : Int)) = true := by
    rw [hBuffer.tail_mark]
    exact decide_eq_true (Eq.refl _)
  have hAppend := run_append rules.appendRules j i hTracks hTail hTailAt hStop
  let appended := C.compile.run appendTicks start
  have hAppState : appended.state = .inl (.inl labels.loader.seekLeft) := by
    rw [← rules.loadLabel]
    exact hAppend.1
  have hAppEq : appended = ⟨.inl (.inl labels.loader.seekLeft), appended.tape⟩ := by
    rw [← hAppState]
  have hApp : TracksAt D ρ appended.tape 0 work trialData := hAppend.2
  have hTrial : QueryBuffer trialData trialWord (some (j + 2)) := queryBuffer_append hBuffer i
  have hAuxLeft (a : Int) : left (trialData a).1 = true ↔ a = -(L : Int) := by
    simpa only [trialData, writeEdits_payload] using hEdgesLeft a
  have hAuxRight (a : Int) : right (trialData a).1 = decide (a = (R : Int)) := by
    simpa only [trialData, writeEdits_payload] using hEdgesRight a
  have hWindow := windowSpec_of_tracksAt D ρ left right L R trialWord
    hApp hTrial.bits hAuxLeft hAuxRight hPositive
  have hWorkBlank := (tracksAt_blankOutside_iff D ρ hTracks L R).mp hBlank
  have hAppBlank := (tracksAt_blankOutside_iff D ρ hApp L R).mpr hWorkBlank
  obtain ⟨answer, callTicks, hCallTicks, hCallState, hCallFrame, hCallBlank, hAnswer⟩ :=
    Loader.run_load_call C labels.loader (queryLayout D left right) rules.loaderRules L R trialWord
      hWindow (tracksAt_frameOrigin D ρ hApp) hAppBlank hFit hLeftClock hRightClock hClock
  let called := C.compile.run callTicks ⟨.inl (.inl labels.loader.seekLeft), appended.tape⟩
  have hCalledState : called.state = .inl (.inl (labels.commit answer).seekSign) := by
    rw [← rules.commitLabel answer]
    exact hCallState
  have hCalledEq : called = ⟨.inl (.inl (labels.commit answer).seekSign), called.tape⟩ := by
    rw [← hCalledState]
  let nextWork := workAtOrigin D ρ called.tape
  have hCallTracks : TracksAt D ρ called.tape 0 nextWork trialData :=
    tracksAt_of_frameOrigin D ρ hCallFrame (tracksAt_savedTrack D ρ hApp)
  have hBeforeSign (a : Int) (_ : 0 ≤ a) (ha : a < ((j + 2 : Nat) : Int)) :
      pending (trialData a) = false := by
    rw [hTrial.pending_mark]
    exact decide_eq_false_iff_not.mpr (fun h ↦ (ne_of_gt ha) (Option.some.inj h))
  have hAtSign : pending (trialData ((j + 2 : Nat) : Int)) = true := by
    rw [hTrial.pending_mark]
    exact decide_eq_true rfl
  let commitTicks := 2 * (j + 2) + 2
  let nextData := updateCell ((j + 2 : Nat) : Int) (ordinary (!answer)) trialData
  have hCommit := run_commit (rules.commitRules answer) (j + 2) (by omega)
    hCallTracks hBeforeSign hAtSign
  let committed := C.compile.run commitTicks
    ⟨.inl (.inl (labels.commit answer).seekSign), called.tape⟩
  have hNext : committed.state = .inl (.inl labels.next) := by
    rw [← rules.nextLabel answer]
    exact hCommit.1
  have hCommitted : TracksAt D ρ committed.tape 0 nextWork nextData := hCommit.2
  have hBeforeEnd : j + 2 < trialWord.dropLast.length := by
    simp only [trialWord, List.length_dropLast, length_appendUnitQuery, j]
    omega
  have hBufferNext : QueryBuffer nextData (appendUnitQuery word i (!answer)) none := by
    have h := queryBuffer_commit hTrial hBeforeEnd (!answer)
    change QueryBuffer nextData ((appendUnitQuery word i false).set
      (word.dropLast.length + 2) (!answer)) none at h
    rwa [appendUnitQuery_set_sign] at h
  have hNextBlank : Loader.BlankOutside D (Cell ρ) committed.tape L R :=
    (tracksAt_blankOutside_iff D ρ hCommitted L R).mpr
      ((tracksAt_blankOutside_iff D ρ hCallTracks L R).mp hCallBlank)
  refine ⟨answer, appendTicks + callTicks + commitTicks, nextWork,
    Nat.add_le_add_right (Nat.add_le_add_left hCallTicks appendTicks) commitTicks, ?_⟩
  rw [C.compile.run_add (appendTicks + callTicks) commitTicks,
    C.compile.run_add appendTicks callTicks]
  change
    let final := C.compile.run commitTicks (C.compile.run callTicks appended)
    final.state = .inl (.inl labels.next) ∧ TracksAt D ρ final.tape 0 nextWork nextData ∧
      QueryBuffer nextData (appendUnitQuery word i (!answer)) none ∧
      Loader.BlankOutside D (Cell ρ) final.tape L R ∧ (answer = true ↔ D.Accepts trialWord)
  rw [hAppEq]
  change
    let final := C.compile.run commitTicks called
    final.state = .inl (.inl labels.next) ∧ TracksAt D ρ final.tape 0 nextWork nextData ∧
      QueryBuffer nextData (appendUnitQuery word i (!answer)) none ∧
      Loader.BlankOutside D (Cell ρ) final.tape L R ∧ (answer = true ↔ D.Accepts trialWord)
  rw [hCalledEq]
  exact ⟨hNext, hCommitted, hBufferNext, hNextBlank, hAnswer⟩

end PvsNP.SATSearch
