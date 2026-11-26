module

public import Init.Data.List.Lemmas
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Logic.Embedding.Basic

/-! # Cook's instance–certificate encoding

The instance is binary and the certificate has its own finite alphabet. The
verifier reads Cook's word `x#y` directly over the union of the alphabets and
the separator.
-/

namespace PvsNP

/-- Finite words over the two-element input alphabet. -/
public abbrev BinaryWord := List Bool

/-- The verifier input alphabet is exactly the union of the images of the
instance and certificate alphabets and the separator. The images can overlap.
Only the instance alphabet must exclude the separator, so the first separator
always determines the boundary. -/
public structure CheckingAlphabet where
  Symbol : Type
  Certificate : Type
  symbolFinite : Finite Symbol
  certificateFinite : Finite Certificate
  certificateNonempty : Nonempty Certificate
  bit : Bool ↪ Symbol
  certificate : Certificate ↪ Symbol
  separator : Symbol
  bit_ne_separator : ∀ b, bit b ≠ separator
  symbolCovered : ∀ s, s = separator ∨ (∃ b, bit b = s) ∨ (∃ c, certificate c = s)

namespace CheckingAlphabet

/-- Cook's word `x#y` over the checking alphabet. -/
@[expose] public def encode (A : CheckingAlphabet) (x : BinaryWord)
    (y : List A.Certificate) : List A.Symbol :=
  x.map A.bit ++ A.separator :: y.map A.certificate

/-- Adding the separator increases the combined length by exactly one. -/
@[simp] public theorem length_encode (A : CheckingAlphabet) (x : BinaryWord)
    (y : List A.Certificate) : (A.encode x y).length = x.length + y.length + 1 := by
  simp [encode, Nat.add_assoc]

/-- Split the input at its first separator and return the raw prefix and
suffix. Further separators in the suffix are preserved. -/
public def splitAtSeparator (A : CheckingAlphabet) [DecidableEq A.Symbol] :
    List A.Symbol → Option (List A.Symbol × List A.Symbol)
  | [] => none
  | s :: w =>
    if s = A.separator then some ([], w)
    else (A.splitAtSeparator w).map (fun (x, y) => (s :: x, y))

/-- A separator-free prefix fixes exactly where the splitter stops. -/
public theorem splitAtSeparator_append (A : CheckingAlphabet) [DecidableEq A.Symbol]
    (x y : List A.Symbol) (h : A.separator ∉ x) :
    A.splitAtSeparator (x ++ A.separator :: y) = some (x, y) := by
  induction x with
  | nil => simp [splitAtSeparator]
  | cons s x ih =>
    obtain ⟨hne, htail⟩ : A.separator ≠ s ∧ A.separator ∉ x := by simpa using h
    simp [splitAtSeparator, Ne.symm hne, ih htail]

/-- A successful split locates the first separator in the input. -/
public theorem splitAtSeparator_eq_some_iff (A : CheckingAlphabet) [DecidableEq A.Symbol]
    {w x y : List A.Symbol} :
    A.splitAtSeparator w = some (x, y) ↔
      w = x ++ A.separator :: y ∧ A.separator ∉ x := by
  constructor
  · intro h
    induction w generalizing x y with
    | nil => simp [splitAtSeparator] at h
    | cons s w ih =>
      by_cases hs : s = A.separator
      · simp only [splitAtSeparator, ite_eq_left hs, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [hs]
      · cases hw : A.splitAtSeparator w with
        | none => simp [splitAtSeparator, hs, hw] at h
        | some p =>
          obtain ⟨u, v⟩ := p
          simp only [splitAtSeparator, ite_eq_right hs, hw, Option.map_some, Option.some.injEq,
            Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨rfl, hu⟩ := ih hw
          simp [Ne.symm hs, hu]
  · rintro ⟨rfl, h⟩
    exact A.splitAtSeparator_append x y h

/-- Splitting an encoded word recovers its two component symbol lists. -/
public theorem splitAtSeparator_encode (A : CheckingAlphabet) [DecidableEq A.Symbol]
    (x : BinaryWord) (y : List A.Certificate) :
    A.splitAtSeparator (A.encode x y) = some (x.map A.bit, y.map A.certificate) := by
  apply A.splitAtSeparator_append
  intro h
  obtain ⟨b, _, hb⟩ := List.mem_map.mp h
  exact A.bit_ne_separator b hb

/-- Distinct instance–certificate pairs have distinct encodings. -/
public theorem encode_injective (A : CheckingAlphabet) :
    Function.Injective (fun p : BinaryWord × List A.Certificate => A.encode p.1 p.2) := by
  classical
  rintro ⟨x, y⟩ ⟨u, v⟩ h
  have h' := congrArg A.splitAtSeparator h
  simp only [A.splitAtSeparator_encode, Option.some.injEq, Prod.mk.injEq] at h'
  exact Prod.ext ((List.map_inj_right (fun _ _ h => A.bit.injective h)).mp h'.1)
    ((List.map_inj_right (fun _ _ h => A.certificate.injective h)).mp h'.2)

end CheckingAlphabet

/-- A verifier input symbol. `none` represents the separator `#`, distinct
from a Turing machine's tape blank. -/
public abbrev VerifierSymbol := Option Bool

/-- Finite words over the verifier alphabet. -/
public abbrev VerifierWord := List VerifierSymbol

/-- The checking alphabet for binary certificates, where both alphabets
have the same image. -/
@[expose] public def binaryCheckingAlphabet : CheckingAlphabet where
  Symbol := VerifierSymbol
  Certificate := Bool
  symbolFinite := by
    refine Finite.intro (n := 3) ?_
    exact
      { toFun := fun
          | none => 0
          | some false => 1
          | some true => 2
        invFun := fun i => if i.val = 0 then none else if i.val = 1 then some false else some true
        left_inv := by
          rintro (_ | (_ | _)) <;> rfl
        right_inv := by
          rintro ⟨i, hi⟩
          have h : i = 0 ∨ i = 1 ∨ i = 2 := by omega
          rcases h with rfl | rfl | rfl <;> rfl }
  certificateFinite := inferInstance
  certificateNonempty := ⟨false⟩
  bit := ⟨some, Option.some_injective _⟩
  certificate := ⟨some, Option.some_injective _⟩
  separator := none
  bit_ne_separator := fun _ => Option.some_ne_none _
  symbolCovered := by
    rintro (_ | b)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨b, rfl⟩)

/-- The word `x#y` over the verifier alphabet. -/
public def encodePair (x y : BinaryWord) : VerifierWord := binaryCheckingAlphabet.encode x y

public theorem binaryCheckingAlphabet_encode_eq_encodePair (x y : BinaryWord) :
    binaryCheckingAlphabet.encode x y = encodePair x y := by
  unfold encodePair
  rfl

/-- The direct list description of the encoding with binary certificates. -/
public theorem encodePair_eq (x y : BinaryWord) :
    encodePair x y = x.map some ++ none :: y.map some := by
  unfold encodePair CheckingAlphabet.encode binaryCheckingAlphabet
  rfl

private def decodeBits : VerifierWord → Option BinaryWord
  | [] => some []
  | none :: _ => none
  | some b :: w => (decodeBits w).map (List.cons b)

/-- Parse a word with exactly one separator into its binary instance and
certificate. -/
public def decodePair : VerifierWord → Option (BinaryWord × BinaryWord)
  | [] => none
  | none :: w => (decodeBits w).map (fun y => ([], y))
  | some b :: w => (decodePair w).map (fun (x, y) => (b :: x, y))

private theorem decodeBits_map_some (w : BinaryWord) :
    decodeBits (w.map some) = some w := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [decodeBits, ih]

/-- The decoder recovers both components of every encoded pair. -/
public theorem decodePair_encodePair (x y : BinaryWord) :
    decodePair (encodePair x y) = some (x, y) := by
  induction x with
  | nil => simp [encodePair_eq, decodePair, decodeBits_map_some]
  | cons b x ih =>
    change (decodePair (encodePair x y)).map _ = _
    rw [ih]
    rfl

private theorem map_some_of_decodeBits {w : VerifierWord} {x : BinaryWord}
    (h : decodeBits w = some x) : x.map some = w := by
  induction w generalizing x with
  | nil =>
    cases h
    rfl
  | cons s w ih =>
    cases s with
    | none => simp [decodeBits] at h
    | some b =>
      cases hw : decodeBits w with
      | none => simp [decodeBits, hw] at h
      | some y =>
        simp only [decodeBits, hw, Option.map_some, Option.some.injEq] at h
        rw [← h]
        simp [ih hw]

/-- Successful decoding certifies that the input is exactly the encoding of
the returned pair. -/
public theorem encodePair_of_decodePair {w : VerifierWord} {x y : BinaryWord}
    (h : decodePair w = some (x, y)) : encodePair x y = w := by
  induction w generalizing x y with
  | nil => simp [decodePair] at h
  | cons s w ih =>
    cases s with
    | none =>
      cases hw : decodeBits w with
      | none => simp [decodePair, hw] at h
      | some v =>
        simp only [decodePair, hw, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [encodePair_eq, map_some_of_decodeBits hw]
    | some b =>
      cases hw : decodePair w with
      | none => simp [decodePair, hw] at h
      | some p =>
        obtain ⟨u, v⟩ := p
        simp only [decodePair, hw, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        change some b :: encodePair u v = some b :: w
        rw [ih hw]

/-- The returned pair is precisely the pair represented by the input word. -/
public theorem decodePair_eq_some_iff {w : VerifierWord} {x y : BinaryWord} :
    decodePair w = some (x, y) ↔ w = encodePair x y := by
  constructor
  · intro h
    exact (encodePair_of_decodePair h).symm
  · rintro rfl
    exact decodePair_encodePair x y

/-- The instance and certificate are uniquely determined by the encoding. -/
public theorem encodePair_injective {x y u v : BinaryWord}
    (h : encodePair x y = encodePair u v) : (x, y) = (u, v) := by
  have h' := congrArg decodePair h
  simpa [decodePair_encodePair] using h'

/-- The separator costs exactly one symbol. -/
@[simp] public theorem length_encodePair (x y : BinaryWord) :
    (encodePair x y).length = x.length + y.length + 1 :=
  binaryCheckingAlphabet.length_encode x y

end PvsNP
