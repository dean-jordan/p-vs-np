module

public import PvsNP.TuringMachine.PairedInput

/-! # Binary checking languages and Cook's separator alphabet -/

public section

namespace PvsNP

/-- Use `00` and `01` for bits and `10` for the separator. -/
@[expose] def verifierSymbolCode : VerifierSymbol ↪ Bool × Bool where
  toFun
    | none => (true, false)
    | some b => (false, b)
  inj' := by
    intro a b h
    cases a <;> cases b <;> simp_all

@[expose] def packedPair (x y : BinaryWord) : BinaryWord :=
  Machine.packInput verifierSymbolCode (encodePair x y)

@[simp] theorem length_packedPair (x y : BinaryWord) :
    (packedPair x y).length = 2 * (x.length + y.length + 1) := by
  rw [packedPair, Machine.length_packInput, length_encodePair]

theorem packedPair_injective : Function.Injective
    (fun p : BinaryWord × BinaryWord ↦ packedPair p.1 p.2) :=
  fun _ _ h ↦ encodePair_injective (Machine.packInput_injective verifierSymbolCode h)

private def unpackVerifier : BinaryWord → Option VerifierWord
  | [] => some []
  | false :: b :: tail => (unpackVerifier tail).map (List.cons (some b))
  | true :: false :: tail => (unpackVerifier tail).map (List.cons none)
  | _ => none

private theorem unpackVerifier_packInput (word : VerifierWord) :
    unpackVerifier (Machine.packInput verifierSymbolCode word) = some word := by
  induction word with
  | nil => rfl
  | cons a tail ih =>
    cases a <;> simp only [Machine.packInput, List.flatMap_cons, verifierSymbolCode,
      Function.Embedding.coeFn_mk, List.cons_append, List.nil_append, unpackVerifier] at * <;>
      rw [ih] <;> rfl

private theorem packInput_of_unpackVerifier {raw : BinaryWord} {word : VerifierWord}
    (h : unpackVerifier raw = some word) : Machine.packInput verifierSymbolCode word = raw := by
  induction raw using unpackVerifier.induct generalizing word with
  | case1 =>
    cases h
    rfl
  | case2 b tail ih =>
    obtain ⟨decoded, hDecoded, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [← ih hDecoded]
    rfl
  | case3 tail ih =>
    obtain ⟨decoded, hDecoded, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [← ih hDecoded]
    rfl
  | case4 raw hNil hBit hSeparator =>
    cases raw with
    | nil => exact (hNil rfl).elim
    | cons a tail =>
      cases tail with
      | nil => cases a <;> cases h
      | cons b rest =>
        cases a
        · exact (hBit b rest rfl).elim
        · cases b
          · exact (hSeparator rest rfl).elim
          · cases h

/-- Parse the binary representation of exactly one Cook instance–certificate pair. -/
def decodePackedPair (raw : BinaryWord) : Option (BinaryWord × BinaryWord) :=
  (unpackVerifier raw).bind decodePair

theorem decodePackedPair_eq_some_iff {raw x y : BinaryWord} :
    decodePackedPair raw = some (x, y) ↔ raw = packedPair x y := by
  constructor
  · intro h
    unfold decodePackedPair at h
    obtain ⟨word, hWord, hd⟩ := Option.bind_eq_some_iff.mp h
    rw [decodePair_eq_some_iff.mp hd] at hWord
    exact (packInput_of_unpackVerifier hWord).symm
  · rintro rfl
    simp only [decodePackedPair, packedPair, unpackVerifier_packInput, Option.bind_some,
      decodePair_encodePair]

/-- The binary language of canonical encodings of pairs satisfying a relation. -/
@[expose] def packedCheckingLanguage (R : BinaryWord → BinaryWord → Prop) : BinaryLanguage :=
  {word | ∃ x y, word = packedPair x y ∧ R x y}

theorem packedPair_mem_packedCheckingLanguage_iff (R : BinaryWord → BinaryWord → Prop)
    (x y : BinaryWord) : packedPair x y ∈ packedCheckingLanguage R ↔ R x y := by
  constructor
  · rintro ⟨u, v, hPair, hR⟩
    have h := packedPair_injective (a₁ := (x, y)) (a₂ := (u, v)) hPair
    cases h
    exact hR
  · exact fun h ↦ ⟨x, y, rfl, h⟩

/-- A binary checker yields a Cook checker for all words over the separator alphabet. -/
theorem checkingLanguage_mem_POver_of_packedCheckingLanguage_mem_P
    {R : BinaryWord → BinaryWord → Prop} (h : packedCheckingLanguage R ∈ P) :
    binaryCheckingAlphabet.checkingLanguage R ∈ POver VerifierSymbol := by
  obtain ⟨M, hTime, hDecides⟩ := h
  refine ⟨M.pairedInput verifierSymbolCode, M.pairedInput_polyTime verifierSymbolCode hTime, ?_⟩
  obtain ⟨k, hClock⟩ := hTime
  intro word
  rw [M.pairedInput_accepts_iff verifierSymbolCode word (hClock _), ← hDecides]
  have hPack (x y : BinaryWord) :
      Machine.packInput verifierSymbolCode (binaryCheckingAlphabet.encode x y) = packedPair x y :=
    congrArg (Machine.packInput verifierSymbolCode)
      (binaryCheckingAlphabet_encode_eq_encodePair x y)
  constructor
  · rintro ⟨x, y, rfl, hR⟩
    exact ⟨x, y, hPack x y, hR⟩
  · rintro ⟨x, y, hWord, hR⟩
    exact ⟨x, y, Machine.packInput_injective verifierSymbolCode (hWord.trans (hPack x y).symm), hR⟩

/-- The bounded existential projection of a polynomial binary checker belongs to Cook's NP. -/
theorem mem_NP_of_packedCheckingLanguage_mem_P {L : BinaryLanguage}
    {R : BinaryWord → BinaryWord → Prop} (h : packedCheckingLanguage R ∈ P) (k : Nat)
    (hLang : ∀ x, x ∈ L ↔ ∃ y : BinaryWord, y.length ≤ x.length ^ k ∧ R x y) : L ∈ NP :=
  ⟨binaryCheckingAlphabet, R, checkingLanguage_mem_POver_of_packedCheckingLanguage_mem_P h,
    k, hLang⟩

end PvsNP
