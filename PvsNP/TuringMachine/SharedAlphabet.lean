module

public import PvsNP.TuringMachine.Core

import Mathlib.Basic.Finite.Sum
import Mathlib.Data.Fintype.Option

/-!
# Shared tape alphabet for binary machines

The common alphabet has one blank, two binary symbols, and separate names for
each machine's working symbols. Mapping a canonical binary tape from either
machine yields the same tape in the common alphabet.
-/

@[expose] public section

namespace PvsNP.Machine

/-- Use shared names for the blank and input bits, and disjoint names for all other symbols. -/
abbrev SharedAlphabet (M D : Machine Bool) := Option Bool ⊕ (M.Symbol ⊕ D.Symbol)

namespace SharedAlphabet

variable (M D : Machine Bool)

/-- The common blank. -/
def blank : SharedAlphabet M D := .inl none

/-- The common input alphabet. -/
def input : Bool ↪ SharedAlphabet M D := ⟨fun b ↦ .inl (some b),
  fun _ _ h ↦ Option.some.inj (Sum.inl.inj h)⟩

theorem input_ne_blank (b : Bool) : input M D b ≠ blank M D := by
  intro h
  exact Option.some_ne_none b (Sum.inl.inj h)

/-- Mathlib's tape uses the common blank as its distinguished inhabitant. -/
abbrev inhabited : Inhabited (SharedAlphabet M D) := ⟨blank M D⟩

theorem finite : Finite (SharedAlphabet M D) := by
  let _ : Finite M.Symbol := M.symbolFinite
  let _ : Finite D.Symbol := D.symbolFinite
  infer_instance

/-- Interpret a shared symbol in the left machine or a left working symbol directly. -/
def readLeft : SharedAlphabet M D → Option M.Symbol
  | .inl none => some M.blank
  | .inl (some b) => some (M.input b)
  | .inr (.inl a) => some a
  | .inr (.inr _) => none

/-- Interpret a shared symbol in the right machine or a right working symbol directly. -/
def readRight : SharedAlphabet M D → Option D.Symbol
  | .inl none => some D.blank
  | .inl (some b) => some (D.input b)
  | .inr (.inl _) => none
  | .inr (.inr a) => some a

end SharedAlphabet

end PvsNP.Machine

end

public section

namespace PvsNP.Machine.SharedAlphabet

variable (M D : Machine Bool)

private noncomputable def classify (a : M.Symbol) : Option Bool ⊕ M.Symbol := by
  classical
  exact if a = M.blank then .inl none
    else if a = M.input false then .inl (some false)
    else if a = M.input true then .inl (some true)
    else .inr a

private theorem classify_blank : classify M M.blank = .inl none := by
  simp [classify]

private theorem classify_input (b : Bool) : classify M (M.input b) = .inl (some b) := by
  cases b <;> simp [classify, M.input_ne_blank, M.input.injective.eq_iff]

private def recover : Option Bool ⊕ M.Symbol → M.Symbol
  | .inl none => M.blank
  | .inl (some b) => M.input b
  | .inr a => a

private theorem recover_classify (a : M.Symbol) : recover M (classify M a) = a := by
  unfold classify
  split
  · rename_i h
    exact h.symm
  · split
    · rename_i h
      exact h.symm
    · split
      · rename_i h
        exact h.symm
      · rfl

private theorem readLeft_classify (a : M.Symbol) :
    readLeft M D ((classify M a).map id Sum.inl) = some a := by
  calc
    _ = some (recover M (classify M a)) := by
      generalize classify M a = c
      cases c with
      | inl b => cases b <;> rfl
      | inr s => rfl
    _ = _ := congrArg some (recover_classify M a)

private theorem readRight_classify (a : D.Symbol) :
    readRight M D ((classify D a).map id Sum.inr) = some a := by
  calc
    _ = some (recover D (classify D a)) := by
      generalize classify D a = c
      cases c with
      | inl b => cases b <;> rfl
      | inr s => rfl
    _ = _ := congrArg some (recover_classify D a)

/-- Embed the first machine's symbols, using common names for the blank and bits. -/
noncomputable def left : M.Symbol ↪ SharedAlphabet M D where
  toFun a := (classify M a).map id Sum.inl
  inj' := by
    intro a b hab
    exact Option.some.inj <| (readLeft_classify M D a).symm.trans
      ((congrArg (readLeft M D) hab).trans (readLeft_classify M D b))

/-- Embed the second machine's symbols, using common names for the blank and bits. -/
noncomputable def right : D.Symbol ↪ SharedAlphabet M D where
  toFun a := (classify D a).map id Sum.inr
  inj' := by
    intro a b hab
    exact Option.some.inj <| (readRight_classify M D a).symm.trans
      ((congrArg (readRight M D) hab).trans (readRight_classify M D b))

@[simp] theorem left_blank : left M D M.blank = blank M D := by
  change (classify M M.blank).map id Sum.inl = _
  rw [classify_blank]
  rfl

@[simp] theorem right_blank : right M D D.blank = blank M D := by
  change (classify D D.blank).map id Sum.inr = _
  rw [classify_blank]
  rfl

@[simp] theorem left_input (b : Bool) : left M D (M.input b) = input M D b := by
  change (classify M (M.input b)).map id Sum.inl = _
  rw [classify_input]
  rfl

@[simp] theorem right_input (b : Bool) : right M D (D.input b) = input M D b := by
  change (classify D (D.input b)).map id Sum.inr = _
  rw [classify_input]
  rfl

@[simp] theorem readLeft_left (a : M.Symbol) : readLeft M D (left M D a) = some a :=
  readLeft_classify M D a

@[simp] theorem readRight_right (a : D.Symbol) : readRight M D (right M D a) = some a :=
  readRight_classify M D a

end PvsNP.Machine.SharedAlphabet

end

@[expose] public section

namespace PvsNP.Machine.SharedAlphabet

variable (M D : Machine Bool)

/-- The first embedding sends the tape blank to the common blank. -/
noncomputable def leftPointed :
    @Turing.PointedMap M.Symbol (SharedAlphabet M D) M.tapeInhabited (inhabited M D) :=
  @Turing.PointedMap.mk _ _ M.tapeInhabited (inhabited M D) (left M D) (left_blank M D)

/-- The second embedding sends the tape blank to the common blank. -/
noncomputable def rightPointed :
    @Turing.PointedMap D.Symbol (SharedAlphabet M D) D.tapeInhabited (inhabited M D) :=
  @Turing.PointedMap.mk _ _ D.tapeInhabited (inhabited M D) (right M D) (right_blank M D)

@[simp] theorem leftPointed_input (b : Bool) : leftPointed M D (M.input b) = input M D b :=
  left_input M D b

@[simp] theorem rightPointed_input (b : Bool) : rightPointed M D (D.input b) = input M D b :=
  right_input M D b

@[simp] theorem readLeft_leftPointed (a : M.Symbol) :
    readLeft M D (leftPointed M D a) = some a := readLeft_left M D a

@[simp] theorem readRight_rightPointed (a : D.Symbol) :
    readRight M D (rightPointed M D a) = some a := readRight_right M D a

/-- The initial tape for a binary word, over the common symbols. -/
def canonicalTape (x : List Bool) : @Turing.Tape (SharedAlphabet M D) (inhabited M D) :=
  @Turing.Tape.mk₁ _ (inhabited M D) (x.map (input M D))

@[simp] theorem leftPointed_map_start (x : List Bool) :
    @Turing.Tape.map _ _ M.tapeInhabited (inhabited M D) (leftPointed M D) (M.start x).tape =
      canonicalTape M D x := by
  change @Turing.Tape.map _ _ M.tapeInhabited (inhabited M D) (leftPointed M D)
    (@Turing.Tape.mk₁ _ M.tapeInhabited (x.map M.input)) = canonicalTape M D x
  rw [@Turing.Tape.map_mk₁ _ _ M.tapeInhabited (inhabited M D) (leftPointed M D)]
  simp only [canonicalTape, List.map_map, Function.comp_def, leftPointed_input]

@[simp] theorem rightPointed_map_start (x : List Bool) :
    @Turing.Tape.map _ _ D.tapeInhabited (inhabited M D) (rightPointed M D) (D.start x).tape =
      canonicalTape M D x := by
  change @Turing.Tape.map _ _ D.tapeInhabited (inhabited M D) (rightPointed M D)
    (@Turing.Tape.mk₁ _ D.tapeInhabited (x.map D.input)) = canonicalTape M D x
  rw [@Turing.Tape.map_mk₁ _ _ D.tapeInhabited (inhabited M D) (rightPointed M D)]
  simp only [canonicalTape, List.map_map, Function.comp_def, rightPointed_input]

end PvsNP.Machine.SharedAlphabet
