module

public import PvsNP.SAT.BinaryLanguage

/-! # Bounded assignment certificates for binary CNF

The verifier decodes the complete formula word and evaluates each clause under
the supplied bit list. A witness can assign every index below the code length,
which suffices for the unary variable names.
-/

@[expose] public section

namespace PvsNP.SATAssignment

/-- Read the assignment as a total function by using `false` beyond its end. -/
def lookup (assignment : BinaryWord) (index : Nat) : Bool := assignment[index]?.getD false

/-- Evaluate a literal using one bit of the assignment. -/
def evalLiteral (assignment : BinaryWord) : CNF.Literal Nat → Bool
  | .pos i => lookup assignment i
  | .neg i => !(lookup assignment i)

/-- Accept a decoded formula exactly when each clause has a true literal. -/
def checkFormula (F : CNF.Formula Nat) (assignment : BinaryWord) : Bool :=
  F.all fun clause ↦ clause.any (evalLiteral assignment)

/-- Check a binary formula word and its assignment certificate. -/
def checkWord (word assignment : BinaryWord) : Bool :=
  match CNFCode.decode word with
  | none => false
  | some F => checkFormula F assignment

/-- The Boolean literal check agrees with the CNF semantics. -/
theorem evalLiteral_eq_true_iff (assignment : BinaryWord) (l : CNF.Literal Nat) :
    evalLiteral assignment l = true ↔ l.Sat (lookup assignment) := by
  cases l <;> simp [evalLiteral]

/-- The Boolean formula check agrees with the CNF semantics. -/
theorem checkFormula_eq_true_iff (F : CNF.Formula Nat) (assignment : BinaryWord) :
    checkFormula F assignment = true ↔ CNF.Sat (lookup assignment) F := by
  simp only [checkFormula, List.all_eq_true, List.any_eq_true, evalLiteral_eq_true_iff,
    CNF.Sat, CNF.Clause.Sat]

/-- An accepted pair decodes to a formula satisfied by its supplied assignment. -/
theorem checkWord_eq_true_iff (word assignment : BinaryWord) :
    checkWord word assignment = true ↔
      ∃ F, CNFCode.decode word = some F ∧ CNF.Sat (lookup assignment) F := by
  cases h : CNFCode.decode word <;> simp [checkWord, h, checkFormula_eq_true_iff]

/-- Reject an invalid formula word regardless of the assignment supplied. -/
theorem checkWord_eq_false_of_malformed {word : BinaryWord}
    (h : CNFCode.decode word = none) (assignment : BinaryWord) :
    checkWord word assignment = false := by
  simp [checkWord, h]

/-- Take the first `n` bits of a total assignment. -/
def ofAssignment (σ : Nat → Bool) (n : Nat) : BinaryWord := List.ofFn fun i : Fin n ↦ σ i.val

@[simp] theorem length_ofAssignment (σ : Nat → Bool) (n : Nat) :
    (ofAssignment σ n).length = n := List.length_ofFn

theorem lookup_ofAssignment (σ : Nat → Bool) {n i : Nat} (hi : i < n) :
    lookup (ofAssignment σ n) i = σ i := by
  simp [lookup, ofAssignment, hi]

private theorem literal_sat_transfer (l : CNF.Literal Nat) {σ τ : Nat → Bool}
    (h : σ (CNFCode.literalIndex l) = τ (CNFCode.literalIndex l)) (hs : l.Sat σ) : l.Sat τ := by
  cases l <;> simp only [CNFCode.literalIndex, CNF.Literal.sat_pos, CNF.Literal.sat_neg] at *
  all_goals rw [← h]; exact hs

/-- The finite assignment already covers every index of a decoded formula. -/
theorem literalIndex_lt_length_word {word : BinaryWord} {F : CNF.Formula Nat}
    (h : CNFCode.decode word = some F) {c : CNF.Clause Nat} {l : CNF.Literal Nat}
    (hc : c ∈ F) (hl : l ∈ c) : CNFCode.literalIndex l < word.length := by
  rw [CNFCode.decode_eq_some_iff.mp h]
  exact CNFCode.literalIndex_lt_length_encode hc hl

/-- The binary SAT language has a sound and complete checker with a linear certificate bound. -/
theorem mem_CNFSAT_iff_exists_assignment (word : BinaryWord) :
    word ∈ CNFSAT ↔
      ∃ assignment : BinaryWord,
        assignment.length ≤ word.length ∧ checkWord word assignment = true := by
  constructor
  · rintro ⟨F, hDecode, σ, hSat⟩
    let assignment := ofAssignment σ word.length
    refine ⟨assignment, by simp [assignment], (checkWord_eq_true_iff _ _).mpr ⟨F, hDecode, ?_⟩⟩
    intro c hc
    obtain ⟨l, hl, hLiteral⟩ := hSat c hc
    have hIndex := literalIndex_lt_length_word hDecode hc hl
    exact ⟨l, hl, literal_sat_transfer l (lookup_ofAssignment σ hIndex).symm hLiteral⟩
  · rintro ⟨assignment, _, hCheck⟩
    obtain ⟨F, hDecode, hSat⟩ := (checkWord_eq_true_iff _ _).mp hCheck
    exact ⟨F, hDecode, lookup assignment, hSat⟩

/-- Check an entire `word#assignment` input, rejecting malformed pair encodings. -/
def checkEncoded (pair : VerifierWord) : Bool :=
  match decodePair pair with
  | none => false
  | some (word, assignment) => checkWord word assignment

/-- The whole-input checker recognizes exactly the checking language. -/
theorem checkEncoded_eq_true_iff (pair : VerifierWord) :
    checkEncoded pair = true ↔
      pair ∈ binaryCheckingAlphabet.checkingLanguage
        (fun word assignment ↦ checkWord word assignment = true) := by
  have hPair (word assignment : BinaryWord) :
      encodePair word assignment = binaryCheckingAlphabet.encode word assignment := by
    rw [encodePair_eq]
    rfl
  constructor
  · intro hCheck
    cases h : decodePair pair with
    | none => simp [checkEncoded, h] at hCheck
    | some values =>
      obtain ⟨word, assignment⟩ := values
      have hEncoded := decodePair_eq_some_iff.mp h
      refine ⟨word, assignment, hEncoded.trans (hPair word assignment), ?_⟩
      simpa only [checkEncoded, h] using hCheck
  · rintro ⟨word, assignment, hEncoded, hCheck⟩
    have h := decodePair_eq_some_iff.mpr (hEncoded.trans (hPair word assignment).symm)
    simpa only [checkEncoded, h] using hCheck

/-- A Cook polynomial decider for the whole-input checker puts binary CNF in NP. -/
theorem mem_NP_of_checkEncoded_mem_P
    (h : {pair : VerifierWord | checkEncoded pair = true} ∈ POver VerifierSymbol) :
    CNFSAT ∈ NP := by
  let R : BinaryWord → BinaryWord → Prop := fun word assignment ↦ checkWord word assignment = true
  have hLanguage : binaryCheckingAlphabet.checkingLanguage R =
      {pair : VerifierWord | checkEncoded pair = true} :=
    Set.ext fun pair ↦ (checkEncoded_eq_true_iff pair).symm
  refine ⟨binaryCheckingAlphabet, R, hLanguage.symm ▸ h, 1, fun word ↦ ?_⟩
  change word ∈ CNFSAT ↔
    ∃ assignment : BinaryWord,
      assignment.length ≤ word.length ^ 1 ∧ checkWord word assignment = true
  simpa only [Nat.pow_one] using mem_CNFSAT_iff_exists_assignment word

end PvsNP.SATAssignment
