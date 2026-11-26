module

public import PvsNP.Complexity.PackedPairs
public import PvsNP.TuringMachine.Registers.ValueRuns

/-! # Scan a packed Cook input in reverse

Each data symbol has a zero high bit and a separator has low bit zero
and high bit one. The reverse cursor reads the certificate first. A
single separator changes the count to the instance lane.
-/

public section

namespace PvsNP.RegisterMachine.Fragment

variable {R : Type}

/-- Add one reverse-scanned data bit to the field selected by the separator state. -/
@[expose] def pushReverseData (seen : Bool) (lo : Bool) (fields : BinaryWord × BinaryWord) :
    BinaryWord × BinaryWord :=
  if seen then (lo :: fields.1, fields.2) else (fields.1, lo :: fields.2)

/-- Parse the remaining reverse-oriented pair bits, given the separator state. -/
@[expose] def scanReverse (seen : Bool) : BinaryWord → Option (BinaryWord × BinaryWord)
  | [] => if seen then some ([], []) else none
  | lo :: false :: tail => (scanReverse seen tail).map (pushReverseData seen lo)
  | false :: true :: tail => if seen then none else scanReverse true tail
  | _ => none

private def reverseData (bits : BinaryWord) : BinaryWord := bits.flatMap fun b ↦ [b, false]

private theorem scanReverse_data (seen : Bool) (bits rest : BinaryWord) :
    scanReverse seen (reverseData bits ++ rest) = (scanReverse seen rest).map
      (fun p ↦ if seen then (bits ++ p.1, p.2) else (p.1, bits ++ p.2)) := by
  induction bits with
  | nil =>
    change scanReverse seen rest = _
    cases seen <;> cases scanReverse _ rest <;> rfl
  | cons b tail ih =>
    change (scanReverse seen (reverseData tail ++ rest)).map (pushReverseData seen b) = _
    rw [ih]
    cases scanReverse seen rest <;> cases seen <;> rfl

private theorem reverse_packedPair (x y : BinaryWord) :
    (packedPair x y).reverse = reverseData y.reverse ++ [false, true] ++ reverseData x.reverse := by
  simp only [packedPair, encodePair_eq, Machine.packInput, reverseData, List.reverse_flatMap,
    List.reverse_append, List.reverse_cons, ← List.map_reverse, List.flatMap_append,
    List.flatMap_map, verifierSymbolCode, List.append_assoc, Function.comp_def]
  rfl

private theorem scanReverse_sound (seen : Bool) (raw : BinaryWord) (x y : BinaryWord)
    (h : scanReverse seen raw = some (x, y)) :
    (if seen then raw = reverseData x ∧ y = []
     else raw = reverseData y ++ [false, true] ++ reverseData x) := by
  cases raw with
  | nil =>
    cases seen
    · simp [scanReverse] at h
    · have hFields : ([], []) = (x, y) := Option.some.inj h
      cases hFields
      simp [reverseData]
  | cons lo rest =>
    cases rest with
    | nil => cases lo <;> simp [scanReverse] at h
    | cons hi tail =>
      cases hi with
      | false =>
        obtain ⟨⟨a, b⟩, hTail, hFields⟩ := Option.map_eq_some_iff.mp h
        have hRaw := scanReverse_sound seen tail a b hTail
        cases seen
        · change (a, lo :: b) = (x, y) at hFields
          cases hFields
          simp only [Bool.false_eq_true, ite_false] at hRaw ⊢
          rw [hRaw]
          rfl
        · change (lo :: a, b) = (x, y) at hFields
          cases hFields
          obtain ⟨hData, rfl⟩ := hRaw
          exact ⟨by rw [hData]; rfl, rfl⟩
      | true =>
        cases lo
        · cases seen
          · obtain ⟨hData, rfl⟩ := scanReverse_sound true tail x y h
            simpa only [Bool.false_eq_true, ite_false, reverseData, List.flatMap_nil,
              List.cons_append, List.nil_append] using
              congrArg (fun suffix ↦ false :: true :: suffix) hData
          · simp [scanReverse] at h
        · simp [scanReverse] at h
termination_by raw.length

/-- Starting before the separator, the reverse parser agrees with the packed decoder. -/
theorem scanReverse_eq_some_iff {raw x y : BinaryWord} :
    scanReverse false raw.reverse = some (x.reverse, y.reverse) ↔
      decodePackedPair raw = some (x, y) := by
  rw [decodePackedPair_eq_some_iff]
  constructor
  · intro h
    apply List.reverse_inj.mp
    rw [reverse_packedPair]
    exact scanReverse_sound false raw.reverse x.reverse y.reverse h
  · intro h
    rw [h, reverse_packedPair]
    have hInstance : scanReverse true (reverseData x.reverse) = some (x.reverse, []) := by
      simpa [scanReverse] using scanReverse_data true x.reverse []
    simp [List.append_assoc, scanReverse_data, scanReverse, hInstance]

/-- Control remembers the first bit of a pair and whether it passed the separator. -/
inductive PackedScanPhase where
  | entry | low (seen : Bool) (bit : Bool) | count (seen : Bool) | advance (seen : Bool)
  | invalid | valid

private def packedScanPhaseCode : PackedScanPhase → Fin 6 × Bool × Bool
  | .entry => (0, false, false)
  | .low seen bit => (1, seen, bit)
  | .count seen => (2, seen, false)
  | .advance seen => (3, seen, false)
  | .invalid => (4, false, false)
  | .valid => (5, false, false)

instance : Finite PackedScanPhase :=
  Finite.of_injective packedScanPhaseCode (by
    intro a b h
    cases a <;> cases b <;> simp_all [packedScanPhaseCode])

/-- Interpret the low bit, or finish at a symbol boundary. -/
@[expose] def scanLow (seen : Bool) : Option Bool → Option PackedScanPhase
  | some lo => some (.low seen lo)
  | none => if seen then some .valid else none

/-- Interpret the high bit using the saved low bit. -/
@[expose] def scanHigh (seen lo : Bool) : Option Bool → Option PackedScanPhase
  | none => none
  | some false => some (.count seen)
  | some true => if seen || lo then some .invalid else some (.advance true)

/-- Count the certificate and instance symbols, and increment `valid` exactly
when the packed input is a canonical pair. -/
abbrev packedPairScan (instanceLength certificateLength valid : R) : Fragment R where
  Label := PackedScanPhase
  entry := some .entry
  code
    | .entry => .readFirst (scanLow false)
    | .low seen lo => .readNext (scanHigh seen lo)
    | .count seen => .inc (if seen then instanceLength else certificateLength)
        (some (.advance seen))
    | .advance seen => .readNext (scanLow seen)
    | .invalid => .resetInput none
    | .valid => .inc valid none

variable [DecidableEq R]

private def scanReadConfig (x : BinaryWord) (i : Nat) (seen : Bool) (values : R → Nat)
    (output : BinaryWord) : Config R (Option PackedScanPhase) :=
  let cfg : Config R (Option PackedScanPhase) := ⟨none, values, none, output⟩
  cfg.readAt x i (scanLow seen)

private def scanCounts (inst cert valid : R) (before after : R → Nat) :
    Option (BinaryWord × BinaryWord) → Prop
  | none => after valid = before valid
  | some (x, y) => after valid = before valid + 1 ∧
      after inst = before inst + x.length ∧ after cert = before cert + y.length

private theorem scanCounts_data (inst cert valid : R) (hIC : inst ≠ cert)
    (hVI : valid ≠ inst) (hVC : valid ≠ cert) (seen lo : Bool)
    (before after : R → Nat) (fields : Option (BinaryWord × BinaryWord))
    (h : scanCounts inst cert valid
      (incrementValues (if seen then inst else cert) before) after fields) :
    scanCounts inst cert valid before after (fields.map (pushReverseData seen lo)) := by
  cases fields with
  | none =>
    cases seen <;> simpa [scanCounts, incrementValues, hVI, hVC] using h
  | some pair =>
    obtain ⟨x, y⟩ := pair
    cases seen <;>
      simp [scanCounts, pushReverseData, incrementValues, hIC, hIC.symm, hVI, hVC] at h ⊢ <;>
      omega

private theorem run_scanRead (inst cert valid : R) (hIC : inst ≠ cert)
    (hVI : valid ≠ inst) (hVC : valid ≠ cert) (x rest : BinaryWord) (i : Nat)
    (seen : Bool) (before : R → Nat) (hSuffix : x.reverse.drop i = rest) :
    ∃ ticks ≤ 2 * rest.length + 1, ∃ after : R → Nat,
      (∀ output, (packedPairScan inst cert valid).run x ticks
        (scanReadConfig x i seen before output) =
        some ⟨some none, after, none, output⟩) ∧
      scanCounts inst cert valid before after (scanReverse seen rest) ∧
      ∀ lane, lane ≠ inst → lane ≠ cert → lane ≠ valid → after lane = before lane := by
  let f := packedPairScan inst cert valid
  have hRead (j : Nat) : x.reverse[i + j]? = rest[j]? := by
    rw [← hSuffix, List.getElem?_drop]
  cases rest with
  | nil =>
    have hEnd : x.reverse[i]? = none := by simpa using hRead 0
    cases seen
    · refine ⟨0, by simp, before, ?_, rfl, fun _ _ _ _ ↦ rfl⟩
      intro output
      change RegisterMachine.run f.close x 0 (scanReadConfig x i false before output) = _
      simp [scanReadConfig, Config.readAt, hEnd, scanLow, RegisterMachine.run_zero]
    · refine ⟨1, by simp, incrementValues valid before, ?_, ?_, ?_⟩
      · intro output
        let start := scanReadConfig x i true before output
        have tick := step_inc (program := f.close) (x := x) (cfg := start)
          (label := some .valid) (by simp [start, scanReadConfig, Config.readAt, hEnd, scanLow]) rfl
        change RegisterMachine.run f.close x 1 start = _
        rw [RegisterMachine.run_succ, tick, Option.bind_some, RegisterMachine.run_zero]
        simp [start, scanReadConfig, Config.readAt, hEnd]
      · simp [scanReverse, scanCounts, incrementValues, hVI.symm, hVC.symm]
      · intro lane _ _ h
        simp [incrementValues, h]
  | cons lo rest =>
    have hLow : x.reverse[i]? = some lo := by simpa using hRead 0
    let start (output : BinaryWord) := scanReadConfig x i seen before output
    let high (output : BinaryWord) := (start output).readAt x (i + 1) (scanHigh seen lo)
    have hReadHigh (output : BinaryWord) : step f.close x (start output) = some (high output) :=
      step_readNext (label := some (.low seen lo)) (i := i)
        (by simp [start, scanReadConfig, Config.readAt, hLow, scanLow]) rfl
        (by simp [start, scanReadConfig, Config.readAt, hLow])
    cases rest with
    | nil =>
      have hHigh : x.reverse[i + 1]? = none := by simpa using hRead 1
      refine ⟨1, by simp, before, ?_, ?_, fun _ _ _ _ ↦ rfl⟩
      · intro output
        change RegisterMachine.run f.close x 1 (start output) = _
        rw [RegisterMachine.run_succ, hReadHigh, Option.bind_some, RegisterMachine.run_zero]
        simp [high, start, scanReadConfig, Config.readAt, hHigh, scanHigh]
      · cases lo <;> rfl
    | cons hi tail =>
      have hHigh : x.reverse[i + 1]? = some hi := by simpa using hRead 1
      have hTail : x.reverse.drop (i + 2) = tail := by
        rw [show x.reverse.drop (i + 2) = (x.reverse.drop i).drop 2 by simp [List.drop_drop],
          hSuffix]
        rfl
      have hHighCursor (output : BinaryWord) : (high output).cursor = some (i + 1) := by
        simp [high, Config.readAt, hHigh]
      cases hi with
      | false =>
        let lane := if seen then inst else cert
        let counted (output : BinaryWord) : f.Cfg := { high output with
          pc := some (some (.advance seen)), values := incrementValues lane before }
        have hPrefix (output : BinaryWord) : RegisterMachine.run f.close x 3 (start output) =
            some (scanReadConfig x (i + 2) seen
              (incrementValues lane before) output) := by
          have hInc : step f.close x (high output) = some (counted output) :=
            step_inc (program := f.close) (x := x) (cfg := high output)
              (label := some (.count seen)) (reg := lane) (next := some (.advance seen))
              (by simp [high, Config.readAt, hHigh, scanHigh]) rfl
          have hAdvance : step f.close x (counted output) =
              some (scanReadConfig x (i + 2) seen
                (incrementValues lane before) output) :=
            step_readNext (cfg := counted output) (label := some (.advance seen)) (i := i + 1)
              rfl rfl (hHighCursor output)
          simp only [RegisterMachine.run, hReadHigh, hInc, hAdvance, Option.bind_some]
        obtain ⟨ticks, hTicks, after, hRun, hCounts, hFrame⟩ := run_scanRead inst cert valid
          hIC hVI hVC x tail (i + 2) seen (incrementValues lane before) hTail
        refine ⟨3 + ticks, by simp only [List.length_cons]; omega, after, ?_, ?_, ?_⟩
        · intro output
          change RegisterMachine.run f.close x (3 + ticks) (start output) = _
          rw [RegisterMachine.run_add, hPrefix, Option.bind_some]
          exact hRun output
        · exact scanCounts_data inst cert valid hIC hVI hVC seen lo before after _ hCounts
        · intro r hI hC hV
          rw [hFrame r hI hC hV]
          cases seen <;> simp [incrementValues, lane, hI, hC]
      | true =>
        by_cases hSep : seen = false ∧ lo = false
        · obtain ⟨rfl, rfl⟩ := hSep
          have hPrefix (output : BinaryWord) : RegisterMachine.run f.close x 2 (start output) =
              some (scanReadConfig x (i + 2) true before output) := by
            have hAdvance : step f.close x (high output) =
                some (scanReadConfig x (i + 2) true before output) :=
              step_readNext (label := some (.advance true)) (i := i + 1)
                (by simp [high, Config.readAt, hHigh, scanHigh]) rfl (hHighCursor output)
            simp only [RegisterMachine.run, hReadHigh, hAdvance, Option.bind_some]
          obtain ⟨ticks, hTicks, after, hRun, hCounts, hFrame⟩ :=
            run_scanRead inst cert valid hIC hVI hVC x tail (i + 2) true before hTail
          refine ⟨2 + ticks, by simp only [List.length_cons]; omega, after, ?_, hCounts, hFrame⟩
          intro output
          change RegisterMachine.run f.close x (2 + ticks) (start output) = _
          rw [RegisterMachine.run_add, hPrefix, Option.bind_some]
          exact hRun output
        · have hBad : (seen || lo) = true := by cases seen <;> cases lo <;> simp_all
          refine ⟨2, by simp only [List.length_cons]; omega, before, ?_, ?_, fun _ _ _ _ ↦ rfl⟩
          · intro output
            have hReset := step_resetInput (program := f.close) (x := x) (cfg := high output)
              (label := some .invalid) (by simp [high, Config.readAt, hHigh, scanHigh, hBad])
              rfl (hHighCursor output)
            change RegisterMachine.run f.close x 2 (start output) = _
            simp only [RegisterMachine.run, hReadHigh, hReset, Option.bind_some]
            rfl
          · cases seen <;> cases lo <;> simp_all [scanReverse, scanCounts]
termination_by rest.length
decreasing_by all_goals simp_all only [List.length_cons]; omega

/-- The scanner reaches its normal exit on every word. On a canonical pair
it adds both lengths and increments `valid`; otherwise `valid` is unchanged. -/
theorem runsValues_packedPairScan (inst cert valid : R) (hIC : inst ≠ cert)
    (hVI : valid ≠ inst) (hVC : valid ≠ cert) (x : BinaryWord) (before : R → Nat) :
    ∃ ticks ≤ 2 * x.length + 2, ∃ after : R → Nat,
      (packedPairScan inst cert valid).RunsValues x ticks before after ∧
      (match decodePackedPair x with
       | none => after valid = before valid
       | some (u, v) => after valid = before valid + 1 ∧
           after inst = before inst + u.length ∧ after cert = before cert + v.length) ∧
      ∀ lane, lane ≠ inst → lane ≠ cert → lane ≠ valid → after lane = before lane := by
  obtain ⟨ticks, hTicks, after, hRun, hCounts, hFrame⟩ :=
    run_scanRead inst cert valid hIC hVI hVC x x.reverse 0 false before rfl
  refine ⟨1 + ticks, ?_, after, ?_, ?_, hFrame⟩
  · rw [List.length_reverse] at hTicks
    omega
  · intro output
    let f := packedPairScan inst cert valid
    let start := f.enter (⟨none, before, none, output⟩ : Config R Unit)
    have hFirst : step f.close x start = some (scanReadConfig x 0 false before output) :=
      step_readFirst (label := some PackedScanPhase.entry) rfl rfl rfl
    change RegisterMachine.run f.close x (1 + ticks) start = _
    rw [RegisterMachine.run_add, RegisterMachine.run_succ, hFirst, Option.bind_some,
      RegisterMachine.run_zero, Option.bind_some]
    exact hRun output
  · cases hDecode : decodePackedPair x with
    | none =>
      have hFail : scanReverse false x.reverse = none := by
        cases hParse : scanReverse false x.reverse with
        | none => rfl
        | some pair =>
          obtain ⟨u, v⟩ := pair
          have hPair : scanReverse false x.reverse = some (u.reverse.reverse, v.reverse.reverse) :=
            by simpa only [List.reverse_reverse] using hParse
          have hOther := scanReverse_eq_some_iff.mp hPair
          rw [hDecode] at hOther
          contradiction
      simpa only [hFail, scanCounts] using hCounts
    | some pair =>
      obtain ⟨u, v⟩ := pair
      have hSuccess := scanReverse_eq_some_iff.mpr hDecode
      simpa only [hSuccess, scanCounts, List.length_reverse] using hCounts

end PvsNP.RegisterMachine.Fragment
