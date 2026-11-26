module

public import PvsNP.TuringMachine.TrackCall.Loader.Travel
public import PvsNP.TuringMachine.TrackCall.Loader.Write
public import PvsNP.TuringMachine.TrackCall.Return

import PvsNP.TuringMachine.OutputBound

/-! # Reset the workspace and enter a Cook call -/

@[expose] public section

namespace PvsNP.TrackCall.Loader

open Turing

variable {α : Type} {D : Machine α} {ρ : Type} [Finite ρ] [Inhabited ρ]

/-- The protected cells specify the boundaries and the contents of the workspace. -/
structure WindowSpec (layout : Layout D ρ) (saved : Tape ρ) (target : D.Tape)
    (L R : Nat) : Prop where
  right_pos : 0 < R
  left_mark : ∀ i : Int, layout.leftEdge (saved.nth i) = true ↔ i = -(L : Int)
  right_mark : ∀ i : Int, layout.rightEdge (saved.nth i) = decide (i = (R : Int))
  contents : ∀ i : Int, -(L : Int) ≤ i → i ≤ (R : Int) →
    layout.load (saved.nth i) = @Tape.nth _ D.tapeInhabited target i

private theorem tape_eq_of_nth {Γ : Type} [Inhabited Γ] {a b : Tape Γ}
    (h : ∀ i : Int, a.nth i = b.nth i) : a = b := by
  cases a with
  | mk head left right =>
    cases b with
    | mk head' left' right' =>
      have hHead : head = head' := h 0
      have hLeft : left = left' := ListBlank.ext (fun n ↦ h (Int.negSucc n))
      have hRight : right = right' := ListBlank.ext (fun n ↦ h (Int.ofNat (n + 1)))
      rw [hHead, hLeft, hRight]

theorem scratchAt_origin_iff (D : Machine α) (ρ : Type) [Finite ρ] [Inhabited ρ]
    (tape : (machine D ρ).Tape) (target : D.Tape) :
    ScratchAt D ρ tape target 0 (fun _ ↦ True) ↔ scratch D ρ tape = target := by
  let _ := D.tapeInhabited
  constructor
  · intro h
    apply tape_eq_of_nth
    intro i
    rw [scratch_nth D ρ]
    simpa only [Int.sub_zero] using h i trivial
  · intro h i _
    rw [Int.sub_zero, ← scratch_nth D ρ, h]

variable (C : Controller D ρ) (labels : Labels C.State) (layout : Layout D ρ)

/-- Overwrite the entire workspace, restore the origin, and enter the child.
Cells outside the workspace are already in their required state. -/
theorem run_load (rules : Rules C labels layout) (L R : Nat)
    {tape : C.compile.Tape} {saved : Tape ρ} {target : D.Tape}
    (window : WindowSpec layout saved target L R) (hFrame : FrameAt D ρ tape saved 0)
    (hOutside : ScratchAt D ρ tape target 0 (fun i ↦ i < -(L : Int) ∨ (R : Int) < i)) :
    let final := C.compile.run (2 * (L + R) + 4) ⟨.inl (.inl labels.seekLeft), tape⟩
    final = C.embedCall labels.reject labels.accept (entry D ρ final.tape) ∧
      FrameAt D ρ final.tape saved 0 ∧ scratch D ρ final.tape = target := by
  dsimp only
  let left := C.compile.run (L + 2) ⟨.inl (.inl labels.seekLeft), tape⟩
  obtain ⟨hLeftState, hLeftFrame, hLeftScratch⟩ :=
    run_seekLeft rules L hFrame hOutside window.left_mark
  change left.state = .inl (.inl labels.writeForward) at hLeftState
  have hLeft : left = ⟨.inl (.inl labels.writeForward), left.tape⟩ := by rw [← hLeftState]
  let wrote := C.compile.run (L + R + 1) ⟨.inl (.inl labels.writeForward), left.tape⟩
  obtain ⟨hWroteState, hWroteFrame, hWroteScratch⟩ :=
    run_writeForward C labels layout rules L R hLeftFrame hLeftScratch
      window.right_mark window.contents
  change wrote.state = .inl (.inl labels.seekOrigin) at hWroteState
  have hWrote : wrote = ⟨.inl (.inl labels.seekOrigin), wrote.tape⟩ := by rw [← hWroteState]
  obtain ⟨hFinalState, hFinalFrame, hFinalScratch⟩ :=
    run_seekOrigin rules R window.right_pos hWroteFrame hWroteScratch
  rw [show 2 * (L + R) + 4 = (L + 2 + (L + R + 1)) + (R + 1) by omega,
    C.compile.run_add (L + 2 + (L + R + 1)) (R + 1), C.compile.run_add (L + 2) (L + R + 1)]
  change
    let final := C.compile.run (R + 1) (C.compile.run (L + R + 1) left)
    final = C.embedCall labels.reject labels.accept (entry D ρ final.tape) ∧
      FrameAt D ρ final.tape saved 0 ∧ scratch D ρ final.tape = target
  rw [hLeft]
  change
    let final := C.compile.run (R + 1) wrote
    final = C.embedCall labels.reject labels.accept (entry D ρ final.tape) ∧
      FrameAt D ρ final.tape saved 0 ∧ scratch D ρ final.tape = target
  rw [hWrote]
  refine ⟨?_, hFinalFrame, (scratchAt_origin_iff D ρ _ _).mp hFinalScratch⟩
  let final := C.compile.run (R + 1) ⟨.inl (.inl labels.seekOrigin), wrote.tape⟩
  change final = (⟨C.enter (.call labels.reject labels.accept), final.tape⟩ : C.compile.Config)
  have hState : final.state = C.enter (.call labels.reject labels.accept) := hFinalState
  rw [← hState]

/-- At the origin, the scratch track has no data outside its workspace. -/
def BlankOutside (D : Machine α) (ρ : Type) [Finite ρ] [Inhabited ρ]
    (tape : (machine D ρ).Tape) (L R : Nat) : Prop :=
  ∀ i : Int, i < -(L : Int) ∨ (R : Int) < i →
    (@Tape.nth _ (machine D ρ).tapeInhabited tape i).1 = D.blank

theorem start_nth_eq_blank (D : Machine α) (input : List α) (i : Int)
    (hOutside : i < 0 ∨ (input.length : Int) ≤ i) :
    @Tape.nth _ D.tapeInhabited (D.start input).tape i = D.blank := by
  let _ := D.tapeInhabited
  cases i with
  | ofNat n =>
    change (n : Int) < 0 ∨ (input.length : Int) ≤ (n : Int) at hOutside
    have hn : input.length ≤ n := by omega
    change (Tape.mk₁ (input.map D.input)).nth (n : Int) = D.blank
    rw [Machine.mk₁_nth_nat]
    exact List.getI_eq_default _ (by simpa only [List.length_map] using hn)
  | negSucc n =>
    change (ListBlank.mk ([] : List D.Symbol)).nth n = D.blank
    rw [ListBlank.nth_mk]
    rfl

/-- Load a query and run the decider. The time bound fits both sides of the
workspace, so the next loader pass can reuse the same region. -/
theorem run_load_call (rules : Rules C labels layout) (L R : Nat)
    (input : List α) {tape : C.compile.Tape} {saved : Tape ρ} {bound : Nat}
    (window : WindowSpec layout saved (D.start input).tape L R)
    (hFrame : FrameAt D ρ tape saved 0) (hBlank : BlankOutside D ρ tape L R)
    (hLength : input.length ≤ R + 1) (hLeft : bound ≤ L) (hRight : bound ≤ R)
    (hTime : D.HaltsWithin input bound) :
    ∃ (answer : Bool) (ticks : Nat), ticks ≤ 2 * (L + R) + 2 * bound + 6 ∧
      let final := C.compile.run ticks ⟨.inl (.inl labels.seekLeft), tape⟩
      final.state = .inl (.inl (C.resume labels.reject labels.accept answer)) ∧
      FrameAt D ρ final.tape saved 0 ∧ BlankOutside D ρ final.tape L R ∧
      (answer = true ↔ D.Accepts input) := by
  have hTarget (i : Int) (hi : i < -(L : Int) ∨ (R : Int) < i) :
      @Tape.nth _ D.tapeInhabited (D.start input).tape i = D.blank :=
    start_nth_eq_blank D input i (by omega)
  have hOutside : ScratchAt D ρ tape (D.start input).tape 0
      (fun i ↦ i < -(L : Int) ∨ (R : Int) < i) := by
    intro i hi
    rw [Int.sub_zero, hBlank i hi, hTarget i hi]
  let loaded := C.compile.run (2 * (L + R) + 4) ⟨.inl (.inl labels.seekLeft), tape⟩
  obtain ⟨hEntry, hLoadedFrame, hScratch⟩ :=
    run_load C labels layout rules L R window hFrame hOutside
  obtain ⟨answer, t, ht, hState, hFinalFrame, hAnswer, hUntouched⟩ :=
    C.run_call_preserving_outside labels.reject labels.accept input saved loaded.tape
      hScratch hLoadedFrame hTime
  refine ⟨answer, (2 * (L + R) + 4) + t, by omega, ?_⟩
  rw [Machine.run_add, hEntry]
  refine ⟨hState, hFinalFrame, ?_, hAnswer⟩
  intro i hi
  have hFar : bound ≤ i.natAbs := by
    rcases hi with hneg | hpos
    · have hn : i ≤ 0 := by omega
      have h := Int.ofNat_natAbs_of_nonpos hn
      omega
    · have hp : 0 ≤ i := by omega
      have h := Int.ofNat_natAbs_of_nonneg hp
      omega
  rw [hUntouched i hFar, ← scratch_nth D ρ, hScratch, hTarget i hi]

end PvsNP.TrackCall.Loader
