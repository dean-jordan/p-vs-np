module

public import PvsNP.Complexity.PairEncoding
public import PvsNP.TuringMachine.Core
public import PvsNP.Complexity.TimeBounds

/-!
# Cook's complexity classes over binary words

The decider halts on every input, including inputs outside the language. For NP the
verifier decides the entire checking language over the finite verifier alphabet.
The certificate alphabet is allowed to vary with the verifier.
-/

@[expose] public section

namespace PvsNP

/-- A decision language over finite binary strings. -/
abbrev BinaryLanguage := Set BinaryWord

/-- Polynomial-time decision languages over an input alphabet `α`. -/
def POver (α : Type) : Set (Set (List α)) :=
  {L | ∃ M : Machine α, M.PolyTime ∧ M.Decides L}

/-- Polynomial-time decision languages over finite binary strings. -/
def P : Set BinaryLanguage := POver Bool

/-- The language of exactly the encoded pairs belonging to a checking relation. -/
def CheckingAlphabet.checkingLanguage (A : CheckingAlphabet)
    (R : BinaryWord → List A.Certificate → Prop) : Set (List A.Symbol) :=
  {z | ∃ x y, z = A.encode x y ∧ R x y}

theorem CheckingAlphabet.encode_mem_checkingLanguage_iff (A : CheckingAlphabet)
    (R : BinaryWord → List A.Certificate → Prop) (x : BinaryWord) (y : List A.Certificate) :
    A.encode x y ∈ A.checkingLanguage R ↔ R x y := by
  constructor
  · rintro ⟨u, v, h, hR⟩
    have hp : (x, y) = (u, v) := A.encode_injective h
    cases hp
    exact hR
  · exact fun h ↦ ⟨x, y, rfl, h⟩

/-- Cook's verifier definition, with the exact certificate length bound `|x|^k`. -/
def NP : Set BinaryLanguage :=
  {L | ∃ (A : CheckingAlphabet) (R : BinaryWord → List A.Certificate → Prop),
    A.checkingLanguage R ∈ POver A.Symbol ∧
    ∃ k : Nat, ∀ x, x ∈ L ↔ ∃ y, y.length ≤ x.length ^ k ∧ R x y}

/-- The relation-based definition is equivalent to a total machine verifier that rejects
words outside the range of the instance–certificate encoding. -/
theorem mem_NP_iff_exists_verifier (L : BinaryLanguage) :
    L ∈ NP ↔ ∃ (A : CheckingAlphabet) (V : Machine A.Symbol) (k : Nat),
      V.PolyTime ∧ (∀ z, V.Accepts z → ∃ x y, z = A.encode x y) ∧
      ∀ x, x ∈ L ↔ ∃ y, y.length ≤ x.length ^ k ∧ V.Accepts (A.encode x y) := by
  constructor
  · rintro ⟨A, R, ⟨V, htime, hdec⟩, k, hL⟩
    refine ⟨A, V, k, htime, ?_, fun x ↦ (hL x).trans ?_⟩
    · intro z hz
      obtain ⟨x, y, h, _⟩ := (hdec z).mpr hz
      exact ⟨x, y, h⟩
    · exact exists_congr fun y ↦ and_congr_right' <|
        (A.encode_mem_checkingLanguage_iff R x y).symm.trans (hdec (A.encode x y))
  · rintro ⟨A, V, k, htime, hencoding, hL⟩
    refine ⟨A, fun x y ↦ V.Accepts (A.encode x y), ⟨V, htime, ?_⟩, k, hL⟩
    intro z
    constructor
    · rintro ⟨x, y, rfl, h⟩
      exact h
    · intro hz
      obtain ⟨x, y, rfl⟩ := hencoding z hz
      exact ⟨x, y, rfl, hz⟩

/-- The remaining class inclusion asks for a polynomial-time decider for every
length-bounded existential projection of a checker. -/
theorem NP_subset_P_iff_verifierProjection :
    NP ⊆ P ↔ ∀ (A : CheckingAlphabet) (V : Machine A.Symbol) (k : Nat),
      V.PolyTime → (∀ z, V.Accepts z → ∃ x y, z = A.encode x y) →
      ∃ D : Machine Bool, D.PolyTime ∧ ∀ x,
        D.Accepts x ↔ ∃ y, y.length ≤ x.length ^ k ∧ V.Accepts (A.encode x y) := by
  constructor
  · intro h A V k htime hencoding
    let L : BinaryLanguage := {x | ∃ y, y.length ≤ x.length ^ k ∧ V.Accepts (A.encode x y)}
    have hNP : L ∈ NP := (mem_NP_iff_exists_verifier L).mpr
      ⟨A, V, k, htime, hencoding, fun _ ↦ Iff.rfl⟩
    obtain ⟨D, hD, hdec⟩ := h hNP
    exact ⟨D, hD, fun x ↦ (hdec x).symm⟩
  · intro h L hL
    obtain ⟨A, V, k, htime, hencoding, hmem⟩ := (mem_NP_iff_exists_verifier L).mp hL
    obtain ⟨D, hD, hdec⟩ := h A V k htime hencoding
    exact ⟨D, hD, fun x ↦ (hmem x).trans (hdec x).symm⟩

theorem Machine.polyTime_iff_polynomiallyBounded {α : Type} (M : Machine α) :
    M.PolyTime ↔ ∃ f : Nat → Nat, PolynomiallyBounded f ∧
      ∀ x, M.HaltsWithin x (f x.length) := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨fun n ↦ n ^ k + k,
      (polynomiallyBounded_iff_cook _).mpr ⟨k, fun _ ↦ Nat.le_refl _⟩, hk⟩
  · rintro ⟨f, hf, h⟩
    obtain ⟨k, hk⟩ := (polynomiallyBounded_iff_cook f).mp hf
    refine ⟨k, fun x ↦ ?_⟩
    obtain ⟨n, hn, b, hb⟩ := h x
    exact ⟨n, Nat.le_trans hn (hk x.length), b, hb⟩

/-- The tape model decides the same languages within the same bound as the appendix rules. -/
theorem mem_POver_iff_appendix {α : Type} (L : Set (List α)) :
    L ∈ POver α ↔ ∃ (M : Machine α) (k : Nat),
      (∀ x, ∃ n ≤ x.length ^ k + k, ∃ b,
        (M.appendixRun n (M.appendixStart x)).state = .inr b) ∧
      ∀ x, x ∈ L ↔ ∃ n, (M.appendixRun n (M.appendixStart x)).state = .inr true := by
  constructor
  · rintro ⟨M, ⟨k, hk⟩, hL⟩
    exact ⟨M, k, fun x ↦ (M.haltsWithin_iff_appendix x _).mp (hk x),
      fun x ↦ (hL x).trans (M.accepts_iff_appendix x)⟩
  · rintro ⟨M, k, hk, hL⟩
    exact ⟨M, ⟨k, fun x ↦ (M.haltsWithin_iff_appendix x _).mpr (hk x)⟩,
      fun x ↦ (hL x).trans (M.accepts_iff_appendix x).symm⟩

end PvsNP
