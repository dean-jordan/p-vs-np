module

public import PvsNP.Circuits.Description
public import PvsNP.MCSP.Streaming

/-! # Retained state and merge calls in the MCSP stream

The retained state consists of a fixed-width row counter and the current
circuit. The call count measures requests made by the stream control, with
each merger treated as one operation.
-/

public section

namespace PvsNP.MCSP

open Circuits

/-- Only the initial constant circuit may exceed the requested gate cap. -/
theorem runStream_retained_bounds {n cap : Nat} {merge : MergeOracle n}
    (correct : CorrectMerge merge cap) {bits : BinaryWord} {state : StreamState n}
    (h : runStream n merge bits = some state) :
    state.seen ≤ 2 ^ n ∧ state.circuit.size ≤ max 1 cap := by
  obtain ⟨hSeen, hPrefix, hSize⟩ := runStream_sound correct h
  refine ⟨hSeen ▸ length_le_of_matchesPrefix hPrefix, ?_⟩
  by_cases hEmpty : bits = []
  · subst bits
    change some (startStream n) = some state at h
    cases h
    simpa only [startStream, BooleanCircuit.size_const] using Nat.le_max_left 1 cap
  · exact Nat.le_trans (hSize hEmpty) (Nat.le_max_right 1 cap)

/-- The first `n + 1` bits hold the counter. The rest describe the circuit. -/
@[expose] def encodeStreamState {n : Nat} (cap : Nat) (state : StreamState n) : BinaryWord :=
  fieldBits (n + 1) state.seen ++ encodeCircuit (max 1 cap) state.circuit

@[expose] def decodeStreamState (n cap : Nat) (bits : BinaryWord) : Option (StreamState n) :=
  (decodeCircuit n (max 1 cap) (bits.drop (n + 1))).map fun circuit ↦
    ⟨fieldValue (bits.take (n + 1)), circuit⟩

@[expose] def streamStateBitBound (n cap : Nat) : Nat :=
  let gateBudget := max 1 cap
  let width := circuitFieldWidth n gateBudget
  n + 1 + (2 * width + gateBudget * (3 + 2 * width))

theorem length_encodeStreamState_le {n : Nat} (cap : Nat) (state : StreamState n)
    (hSize : state.circuit.size ≤ max 1 cap) :
    (encodeStreamState cap state).length ≤ streamStateBitBound n cap := by
  simp only [encodeStreamState, List.length_append, length_fieldBits, streamStateBitBound]
  exact Nat.add_le_add_left (length_encodeCircuit_le (max 1 cap) state.circuit hSize) _

theorem decodeStreamState_encodeStreamState {n : Nat} (cap : Nat) (state : StreamState n)
    (hSeen : state.seen ≤ 2 ^ n) (hSize : state.circuit.size ≤ max 1 cap) :
    decodeStreamState n cap (encodeStreamState cap state) = some state := by
  have hFit : state.seen < 2 ^ (n + 1) := by
    rw [Nat.pow_succ]
    have hPos := Nat.two_pow_pos n
    omega
  have hLength := length_fieldBits (n + 1) state.seen
  simp only [decodeStreamState, encodeStreamState, List.take_left' hLength, List.drop_left' hLength,
    fieldValue_bits (n + 1) state.seen hFit, decodeCircuit_encodeCircuit _ _ hSize, Option.map_some]

/-- The retained data of a successful prefix has a bounded, reversible description. -/
theorem runStream_retained_encoding {n cap : Nat} {merge : MergeOracle n}
    (correct : CorrectMerge merge cap) {bits : BinaryWord} {state : StreamState n}
    (h : runStream n merge bits = some state) :
    decodeStreamState n cap (encodeStreamState cap state) = some state ∧
      (encodeStreamState cap state).length ≤ streamStateBitBound n cap := by
  obtain ⟨hSeen, hSize⟩ := runStream_retained_bounds correct h
  exact ⟨decodeStreamState_encodeStreamState cap state hSeen hSize,
    length_encodeStreamState_le cap state hSize⟩

private def mergeCharge {n : Nat} : Option (StreamState n) → Nat
  | none => 0
  | some state => if state.seen < 2 ^ n then 1 else 0

private def countedPushBit {n : Nat} (merge : MergeOracle n)
    (before : Option (StreamState n) × Nat) (bit : Bool) : Option (StreamState n) × Nat :=
  (pushBit merge before.1 bit, before.2 + mergeCharge before.1)

/-- Count one call for each live state with a row left, even if the request fails. -/
def runStreamCounted (n : Nat) (merge : MergeOracle n) (bits : BinaryWord) :
    Option (StreamState n) × Nat :=
  bits.foldl (countedPushBit merge) (some (startStream n), 0)

private theorem mergeCharge_le_one {n : Nat} (before : Option (StreamState n)) :
    mergeCharge before ≤ 1 := by
  cases before with
  | none => exact Nat.zero_le _
  | some state =>
    by_cases hRoom : state.seen < 2 ^ n <;> simp [mergeCharge, hRoom]

private theorem mergeCharge_eq_one_of_pushBit_ne_none {n : Nat} (merge : MergeOracle n)
    (before : Option (StreamState n)) (bit : Bool) (h : pushBit merge before bit ≠ none) :
    mergeCharge before = 1 := by
  cases before with
  | none => exact (h rfl).elim
  | some state =>
    by_cases hRoom : state.seen < 2 ^ n
    · simp [mergeCharge, hRoom]
    · exact (h (by simp [pushBit, hRoom])).elim

private theorem foldl_pushBit_none {n : Nat} (merge : MergeOracle n) (bits : BinaryWord) :
    bits.foldl (pushBit merge) none = none := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => exact ih

private theorem foldl_countedPushBit_spec {n : Nat} (merge : MergeOracle n) (bits : BinaryWord)
    (before : Option (StreamState n)) (calls : Nat) :
    let output := bits.foldl (countedPushBit merge) (before, calls)
    output.1 = bits.foldl (pushBit merge) before ∧ output.2 ≤ calls + bits.length ∧
      (output.1.isSome = true → output.2 = calls + bits.length) := by
  induction bits generalizing before calls with
  | nil => simp
  | cons bit rest ih =>
    simp only [List.foldl_cons, countedPushBit, List.length_cons]
    obtain ⟨hState, hCalls, hExact⟩ :=
      ih (pushBit merge before bit) (calls + mergeCharge before)
    refine ⟨hState, ?_, ?_⟩
    · have hCharge := mergeCharge_le_one before
      omega
    · intro hSuccess
      have hPush : pushBit merge before bit ≠ none := by
        intro hNone
        rw [hState, hNone, foldl_pushBit_none] at hSuccess
        contradiction
      have hCount := hExact hSuccess
      have hCharge := mergeCharge_eq_one_of_pushBit_ne_none merge before bit hPush
      omega

theorem runStreamCounted_fst (n : Nat) (merge : MergeOracle n) (bits : BinaryWord) :
    (runStreamCounted n merge bits).1 = runStream n merge bits :=
  (foldl_countedPushBit_spec merge bits (some (startStream n)) 0).1

theorem runStreamCounted_mergeCalls_le (n : Nat) (merge : MergeOracle n) (bits : BinaryWord) :
    (runStreamCounted n merge bits).2 ≤ bits.length := by
  simpa only [runStreamCounted, Nat.zero_add] using
    (foldl_countedPushBit_spec merge bits (some (startStream n)) 0).2.1

theorem runStreamCounted_mergeCalls_eq_of_some {n : Nat} {merge : MergeOracle n}
    {bits : BinaryWord} {state : StreamState n} (h : runStream n merge bits = some state) :
    (runStreamCounted n merge bits).2 = bits.length := by
  have hSuccess : (runStreamCounted n merge bits).1.isSome = true := by
    rw [runStreamCounted_fst, h]
    rfl
  simpa only [runStreamCounted, Nat.zero_add] using
    (foldl_countedPushBit_spec merge bits (some (startStream n)) 0).2.2 hSuccess

end PvsNP.MCSP
