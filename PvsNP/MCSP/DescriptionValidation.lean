module

public import PvsNP.Circuits.DescriptionValidation
public import PvsNP.MCSP.MergeSearch

/-! # Exact record checks for the old and candidate merge circuit codecs -/

public section

namespace PvsNP.MCSP

open Circuits

/-- Successful padded decoding checks the exact total length and zero suffix,
then decodes the bounded prefix containing the header, gates, and output. -/
theorem decodeMergeWitness_eq_some_iff_trim {n cap : Nat} {word : BinaryWord}
    {c : BooleanCircuit n} :
    decodeMergeWitness n cap word = some c ↔
      word.length = mergeWitnessLength n cap ∧
      (word.drop (circuitDescriptionCodeLength n cap word)).all (!·) ∧
      decodeCircuit n cap (word.take (circuitDescriptionCodeLength n cap word)) = some c := by
  let codeLength := circuitDescriptionCodeLength n cap word
  let ok := word.length = mergeWitnessLength n cap ∧ (word.drop codeLength).all (!·)
  change (if ok then decodeCircuit n cap (word.take codeLength) else none) = some c ↔ _
  by_cases h : ok
  · rw [ite_eq_left h]
    exact ⟨fun hDecode ↦ ⟨h.1, h.2, hDecode⟩, fun hDecode ↦ hDecode.2.2⟩
  · rw [ite_eq_right h]
    constructor
    · intro hDecode
      contradiction
    · intro hDecode
      exact (h ⟨hDecode.1, hDecode.2.1⟩).elim

/-- A successful merge witness decoder already ensures a canonical circuit code. -/
theorem decodeMergeWitness_eq_some_iff_canonical {n cap : Nat} {word : BinaryWord}
    {c : BooleanCircuit n} : decodeMergeWitness n cap word = some c ↔
      c.size ≤ cap ∧ word = encodeMergeWitness cap c := by
  constructor
  · intro hDecode
    obtain ⟨hLength, hPadding, hTrim⟩ := decodeMergeWitness_eq_some_iff_trim.mp hDecode
    obtain ⟨hSize, hCode⟩ := decodeCircuit_eq_some_iff_canonical.mp hTrim
    apply And.intro hSize
    have hLocalTrim := circuitDescriptionValid_iff_canonical.mpr ⟨c, hSize, hCode⟩
    have hValid := paddedCircuitDescriptionValid_iff_trim.mpr ⟨hLength, hPadding, hLocalTrim⟩
    obtain ⟨other, hOtherSize, hWord⟩ := paddedCircuitDescriptionValid_iff_canonical.mp hValid
    change word = encodeMergeWitness cap other at hWord
    have hOther := decodeMergeWitness_encodeMergeWitness cap other hOtherSize
    rw [hWord, hOther] at hDecode
    exact (Option.some.inj hDecode) ▸ hWord
  · rintro ⟨hSize, rfl⟩
    exact decodeMergeWitness_encodeMergeWitness cap c hSize

/-- The bounded local checks characterize the exact padded words accepted by the codec.
Use budget `max 1 cap` for the old circuit and `cap` for the candidate. -/
theorem decodeMergeWitness_isSome_iff_paddedDescriptionValid {n cap : Nat} {word : BinaryWord} :
    (decodeMergeWitness n cap word).isSome ↔ PaddedCircuitDescriptionValid n cap word := by
  rw [Option.isSome_iff_exists, paddedCircuitDescriptionValid_iff_canonical]
  constructor
  · rintro ⟨c, h⟩
    exact ⟨c, decodeMergeWitness_eq_some_iff_canonical.mp h⟩
  · rintro ⟨c, h⟩
    exact ⟨c, decodeMergeWitness_eq_some_iff_canonical.mpr h⟩

/-- The padded raw header agrees with the reconstructed circuit size. -/
theorem circuitDescriptionCount_of_decodeMergeWitness {n cap : Nat} {word : BinaryWord}
    {c : BooleanCircuit n} (h : decodeMergeWitness n cap word = some c) :
    circuitDescriptionCount n cap word = c.size := by
  have hTrim := (decodeMergeWitness_eq_some_iff_trim.mp h).2.2
  have hCount := circuitDescriptionCount_of_decode hTrim
  rwa [circuitDescriptionCount_trim] at hCount

/-- The bounded raw output field is the decoded circuit's output wire. -/
theorem circuitDescriptionOutput_of_decodeMergeWitness {n cap : Nat} {word : BinaryWord}
    {c : BooleanCircuit n} (h : decodeMergeWitness n cap word = some c) :
    circuitDescriptionOutput (circuitFieldWidth n cap) (circuitDescriptionCount n cap word) word =
      c.output.val := by
  have hTrim := (decodeMergeWitness_eq_some_iff_trim.mp h).2.2
  have hOutput := circuitDescriptionOutput_of_decode hTrim
  rw [circuitDescriptionCount_trim] at hOutput
  unfold circuitDescriptionCodeLength at hOutput
  rwa [circuitDescriptionOutput_trim] at hOutput

/-- Each bounded record in the padded raw word is the decoded circuit instruction. -/
theorem circuitDescriptionGateAt_of_decodeMergeWitness {n cap : Nat} {word : BinaryWord}
    {c : BooleanCircuit n} (h : decodeMergeWitness n cap word = some c)
    (i : Nat) (hi : i < c.size) :
    (circuitDescriptionGateAt (circuitFieldWidth n cap) n word i).map Gate.traceInstruction =
      c.network.traceInstructions[i]? := by
  have hTrim := (decodeMergeWitness_eq_some_iff_trim.mp h).2.2
  have hGate := circuitDescriptionGateAt_of_decode hTrim i hi
  have hBound : i < circuitDescriptionCount n cap word :=
    (circuitDescriptionCount_of_decodeMergeWitness h).symm ▸ hi
  unfold circuitDescriptionCodeLength at hGate
  rwa [circuitDescriptionGateAt_trim _ _ _ _ _ hBound] at hGate

end PvsNP.MCSP
