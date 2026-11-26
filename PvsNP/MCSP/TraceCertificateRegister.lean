module

public import PvsNP.MCSP.TraceCertificateLayout
public import PvsNP.TuringMachine.Registers.Affine
public import PvsNP.TuringMachine.Registers.BinaryCompare
public import PvsNP.TuringMachine.Registers.LessThan
public import PvsNP.TuringMachine.Registers.Subtract

/-! # Check the length and high row bit of a packed trace certificate -/

public section

namespace PvsNP.MCSP

open RegisterMachine RegisterMachine.Fragment

/-- Inputs, failure flag, and the temporary registers used for the guard. -/
inductive TraceCertificateLane where
  | inputLength | arity | oldCount | newCount | certificateLength
  | failure | expected | position | leftCopy | rightCopy | scratch
  deriving DecidableEq

variable {R : Type}

private def clearCertificateLane (lane : R) : Fragment R where
  Label := Unit
  entry := some ()
  code _ := .dec lane none (some ())

private def measureTraceCertificate (lanes : TraceCertificateLane → R) : Fragment R :=
  let expected := lanes .expected
  let scratch := lanes .scratch
  ((accumulateAffine (lanes .arity) expected (lanes .rightCopy) scratch 3 3).seq
    (add (lanes .oldCount) expected scratch)).seq (add (lanes .newCount) expected scratch)

private def checkCertificateHighBit (lanes : TraceCertificateLane → R) : Fragment R :=
  let distance := lanes .leftCopy
  let position := lanes .position
  let index := lanes .rightCopy
  let scratch := lanes .scratch
  let copy := add (lanes .certificateLength) distance scratch
  let offset := subtract (lanes .arity) distance index scratch
  let physical := accumulateAffine distance position index scratch 2 0
  let read := readRegisterBit position index scratch fun bit ↦
    incrementBy (lanes .failure) (bit.getD true).toNat
  ((((((copy.seq (decrementLane distance)).seq offset).seq physical).seq read).seq
    (clearCertificateLane distance)).seq (clearCertificateLane position))

/-- Check the extent before any certificate read, then test the one mandatory zero bit. -/
def traceCertificateRegister (lanes : TraceCertificateLane → R) : Fragment R :=
  let guard := ifEqual (lanes .certificateLength) (lanes .expected) (lanes .leftCopy)
    (lanes .rightCopy) (lanes .scratch) (checkCertificateHighBit lanes)
    (incrementBy (lanes .failure) 1)
  ((measureTraceCertificate lanes).seq guard).seq (clearCertificateLane (lanes .expected))

/-- An explicit linear instruction bound in the unary inputs. -/
@[expose] def traceCertificateRegisterCost (length arity oldCount newCount certificate : Nat) :
    Nat :=
  100 * (length + arity + oldCount + newCount + certificate + 1)

theorem traceCertificateRegisterCost_polynomiallyBounded
    {length arity oldCount newCount certificate : Nat → Nat} (hLength : PolynomiallyBounded length)
    (hArity : PolynomiallyBounded arity) (hOld : PolynomiallyBounded oldCount)
    (hNew : PolynomiallyBounded newCount) (hCertificate : PolynomiallyBounded certificate) :
    PolynomiallyBounded (fun n ↦ traceCertificateRegisterCost (length n) (arity n) (oldCount n)
      (newCount n) (certificate n)) :=
  (PolynomiallyBounded.const 100).mul
    (((((hLength.add hArity).add hOld).add hNew).add hCertificate).add
      (PolynomiallyBounded.const 1))

variable [DecidableEq R]

private theorem runsValues_clearCertificateLane (lane : R) (word : BinaryWord) (v : R → Nat) :
    (clearCertificateLane lane).RunsValues word (v lane + 1) v (setValue lane 0 v) := by
  intro output
  exact run_clear word (program := (clearCertificateLane lane).close) rfl
    (cfg := (clearCertificateLane lane).enter (⟨none, v, none, output⟩ : Config R Unit)) rfl

private theorem runsValues_measureTraceCertificate (lanes : TraceCertificateLane → R)
    (inj : Function.Injective lanes) (word : BinaryWord) (before : R → Nat)
    (hExpected : before (lanes .expected) = 0) (hRightCopy : before (lanes .rightCopy) = 0)
    (hScratch : before (lanes .scratch) = 0) :
    let n := before (lanes .arity)
    let old := before (lanes .oldCount)
    let new := before (lanes .newCount)
    (measureTraceCertificate lanes).RunsValues word (15 * n + 5 * old + 5 * new + 20) before
      (setValue (lanes .expected) (mergeTraceCertificateLength n old new) before) := by
  let n := before (lanes .arity)
  let old := before (lanes .oldCount)
  let new := before (lanes .newCount)
  let expected := lanes .expected
  let scratch := lanes .scratch
  let arityExtent := setValue expected (3 * n + 3) before
  have hLane (a b : TraceCertificateLane) : lanes a = lanes b ↔ a = b :=
    ⟨fun h ↦ inj h, congrArg lanes⟩
  have hRoles : ([.arity, .expected, .rightCopy, .scratch] : List TraceCertificateLane).Nodup :=
    by decide
  have hArity : (accumulateAffine (lanes .arity) expected (lanes .rightCopy) scratch 3 3).RunsValues
      word (affineTime 3 3 n) before arityExtent := by
    simpa only [expected, scratch, arityExtent, n, hExpected, Nat.zero_add] using
      runsValues_accumulateAffine (lanes .arity) expected (lanes .rightCopy) scratch 3 3 word
        before (hRoles.map inj) hRightCopy hScratch
  have hAdd (source : TraceCertificateLane) (hSE : source ≠ .expected) (hSS : source ≠ .scratch)
      (extent : Nat) : (add (lanes source) expected scratch).RunsValues word
        (5 * before (lanes source) + 2) (setValue expected extent before)
        (setValue expected (extent + before (lanes source)) before) := by
    let seeded := setValue expected extent before
    have hSource : seeded (lanes source) = before (lanes source) :=
      setValue_other (by simpa [expected, hLane] using hSE) ..
    have hWork : seeded scratch = 0 :=
      (setValue_other (by simp [scratch, expected, hLane]) ..).trans hScratch
    have hRun := runsValues_add (lanes source) expected scratch word seeded
      (by simpa [expected, hLane] using hSE) (by simpa [scratch, hLane] using hSS)
      (by simp [expected, scratch, hLane]) hWork
    rw [hSource, show seeded expected = extent from setValue_same ..] at hRun
    simpa only [seeded, setValue_replace] using hRun
  have hOld := hAdd .oldCount (by decide) (by decide) (3 * n + 3)
  have hNew := hAdd .newCount (by decide) (by decide) (3 * n + 3 + old)
  have hRun := (hArity.seq hOld).seq hNew
  change (measureTraceCertificate lanes).RunsValues word _ before _ at hRun
  have hTime : affineTime 3 3 n + (5 * old + 2) + (5 * new + 2) =
      15 * n + 5 * old + 5 * new + 20 := by simp [affineTime]; omega
  have hExtent : 3 * n + 3 + old + new = mergeTraceCertificateLength n old new := by
    unfold mergeTraceCertificateLength mergeTraceCertificateClaimOffset
      mergeTraceCertificateNewOffset mergeTraceCertificateOldOffset
    omega
  simpa only [← hExtent, ← hTime, n, old, new] using hRun

private theorem runsValues_checkCertificateHighBit (lanes : TraceCertificateLane → R)
    (inj : Function.Injective lanes) (query cert : BinaryWord) (before : R → Nat)
    (hLength : before (lanes .certificateLength) = cert.length)
    (hPosition : before (lanes .position) = 0) (hLeft : before (lanes .leftCopy) = 0)
    (hRight : before (lanes .rightCopy) = 0) (hScratch : before (lanes .scratch) = 0)
    (hFailure : before (lanes .failure) = 0) (hIn : before (lanes .arity) < cert.length) :
    let word := packedPair query cert
    let n := before (lanes .arity)
    ∃ ticks ≤ 16 * cert.length + 7 * n + 8 * word.length + 24,
      (checkCertificateHighBit lanes).RunsValues word ticks before
        (setValue (lanes .failure) (cert[n]?.getD true).toNat before) := by
  let word := packedPair query cert
  let n := before (lanes .arity)
  let distance := lanes .leftCopy
  let position := lanes .position
  let index := lanes .rightCopy
  let scratch := lanes .scratch
  let failure := lanes .failure
  let bit := cert[n]?.getD true
  let last := cert.length - 1
  let delta := last - n
  let offset := 2 * delta
  let copied := setValue distance cert.length before
  let decremented := setValue distance last before
  let measured := setValue distance delta before
  let positioned := setValue position offset measured
  let flagged := setValue failure bit.toNat positioned
  let cleared := setValue distance 0 flagged
  have hLane (a b : TraceCertificateLane) : lanes a = lanes b ↔ a = b :=
    ⟨fun h ↦ inj h, congrArg lanes⟩
  have hCopy : (add (lanes .certificateLength) distance scratch).RunsValues
      word (5 * cert.length + 2) before copied := by
    have hEmpty : before distance = 0 := hLeft
    simpa only [hLength, hEmpty, Nat.zero_add, copied] using
      runsValues_add (lanes .certificateLength) distance scratch word before
        (by simp [distance, hLane]) (by simp [scratch, hLane])
        (by simp [distance, scratch, hLane]) hScratch
  have hDecValues : decrementValues distance copied = decremented := by
    funext r
    by_cases hr : r = distance <;> simp [decrementValues, copied, decremented, setValue, hr, last]
  have hDec : (decrementLane distance).RunsValues word 1 copied decremented := by
    simpa only [hDecValues] using runsValues_decrementLane distance word copied
  have hDecArity : decremented (lanes .arity) = n :=
    setValue_other (by simp [distance, hLane]) ..
  have hDecIndex : decremented index = 0 :=
    (setValue_other (by simp [distance, index, hLane]) ..).trans hRight
  have hDecScratch : decremented scratch = 0 :=
    (setValue_other (by simp [distance, scratch, hLane]) ..).trans hScratch
  have hSub : (subtract (lanes .arity) distance index scratch).RunsValues
      word (7 * n + 3) decremented measured := by
    have hDist : decremented distance = last := setValue_same ..
    simpa only [hDecArity, hDist, delta, decremented, measured, setValue_replace] using
      runsValues_subtract (lanes .arity) distance index scratch word decremented
        (by simp [index, hLane]) (by simp [scratch, hLane]) (by simp [index, scratch, hLane])
        (by simp [distance, index, hLane]) hDecIndex hDecScratch
  have hAffineRoles : ([.leftCopy, .position, .rightCopy, .scratch] :
      List TraceCertificateLane).Nodup := by decide
  have hAffine : (accumulateAffine distance position index scratch 2 0).RunsValues
      word (affineTime 2 0 delta) measured positioned := by
    have hDist : measured distance = delta := setValue_same ..
    have hPos : measured position = 0 :=
      (setValue_other (by simp [position, distance, hLane]) ..).trans hPosition
    have hIndex : measured index = 0 :=
      (setValue_other (by simp [index, distance, hLane]) ..).trans hRight
    have hWork : measured scratch = 0 :=
      (setValue_other (by simp [scratch, distance, hLane]) ..).trans hScratch
    simpa only [hDist, hPos, Nat.zero_add, Nat.add_zero, offset, positioned] using
      runsValues_accumulateAffine distance position index scratch 2 0 word measured
        (hAffineRoles.map inj) hIndex hWork
  have hPos : positioned position = offset := setValue_same ..
  have hBit : cert[n]? = some bit := by
    have hn : n < cert.length := hIn
    simp only [bit, List.getElem?_eq_getElem hn, Option.getD_some]
  have hReadBit : word.reverse[positioned position]? = some bit := by
    rw [hPos, show offset = 2 * (cert.length - 1 - n) from rfl]
    exact (getElem?_reverse_packedPair_certificate query cert hIn).trans hBit
  have hReadIndex : positioned index = 0 := by
    simp [positioned, measured, index, position, distance, setValue, hLane, hRight]
  have hReadWork : positioned scratch = 0 := by
    simp [positioned, measured, scratch, position, distance, setValue, hLane, hScratch]
  have hReadFailure : positioned failure = 0 := by
    simp [positioned, measured, failure, position, distance, setValue, hLane, hFailure]
  have hFlag : (incrementBy failure bit.toNat).RunsValues word bit.toNat positioned flagged := by
    simpa only [hReadFailure, Nat.zero_add, flagged] using
      runsValues_incrementBy failure bit.toNat word positioned
  have hRead := runsValues_readRegisterBit position index scratch
    (fun b ↦ incrementBy failure (b.getD true).toNat) word positioned
    (by simp [position, index, hLane]) (by simp [position, scratch, hLane])
    (by simp [index, scratch, hLane]) hReadIndex hReadWork
    (by simpa only [hReadBit, Option.getD_some] using hFlag)
  have hFlaggedDistance : flagged distance = delta := by
    simp [flagged, positioned, measured, failure, position, distance, setValue, hLane]
  have hClearedPosition : cleared position = offset := by
    simp [cleared, flagged, positioned, failure, position, distance, setValue, hLane]
  have hFinal : setValue position 0 cleared = setValue failure bit.toNat before := by
    funext r
    by_cases hp : r = position
    · subst r
      simp [position, failure, setValue, hLane, hPosition]
    by_cases hd : r = distance
    · subst r
      simp [cleared, position, failure, distance, setValue, hLane, hLeft]
    simp [cleared, flagged, positioned, measured, setValue, hp, hd]
  have hClearDistance := runsValues_clearCertificateLane distance word flagged
  have hClearPosition := runsValues_clearCertificateLane position word cleared
  rw [hFlaggedDistance] at hClearDistance
  rw [hClearedPosition, hFinal] at hClearPosition
  rw [hPos] at hRead
  have hRun := (((((hCopy.seq hDec).seq hSub).seq hAffine).seq hRead).seq hClearDistance).seq
    hClearPosition
  refine ⟨_, ?_, hRun⟩
  change _ ≤ 16 * cert.length + 7 * n + 8 * word.length + 24
  have hDelta : delta ≤ cert.length := (Nat.sub_le ..).trans (Nat.sub_le ..)
  have hOffset : offset ≤ word.length := by
    have hWordLen : word.length = 2 * (query.length + cert.length + 1) := length_packedPair ..
    unfold offset
    omega
  have hLookup := inputAtCost_le offset word.length
  have hBitCost := Bool.toNat_le bit
  unfold affineTime
  omega

/-- The guard reports zero exactly for valid certificate framing, preserving every seed
and restoring all workspace. Unequal lengths are handled before the row bit is read. -/
theorem runsValues_traceCertificateRegister (lanes : TraceCertificateLane → R)
    (inj : Function.Injective lanes) (query cert : BinaryWord) (before : R → Nat)
    (hLength : before (lanes .inputLength) = (packedPair query cert).length)
    (hCert : before (lanes .certificateLength) = cert.length)
    (hZero : ∀ lane, lane ∉ [.inputLength, .arity, .oldCount, .newCount, .certificateLength] →
      before (lanes lane) = 0) :
    let word := packedPair query cert
    let n := before (lanes .arity)
    let old := before (lanes .oldCount)
    let new := before (lanes .newCount)
    ∃ ticks ≤ traceCertificateRegisterCost (before (lanes .inputLength)) n old new cert.length,
      ∃ failure, (traceCertificateRegister lanes).RunsValues word ticks before
        (setValue (lanes .failure) failure before) ∧
        (failure = 0 ↔ MergeTraceCertificateLayout n old new cert) := by
  let word := packedPair query cert
  let n := before (lanes .arity)
  let old := before (lanes .oldCount)
  let new := before (lanes .newCount)
  let expected := mergeTraceCertificateLength n old new
  let measured := setValue (lanes .expected) expected before
  let same := checkCertificateHighBit lanes
  let bad := incrementBy (lanes .failure) 1
  have hLane (a b : TraceCertificateLane) : lanes a = lanes b ↔ a = b :=
    ⟨fun h ↦ inj h, congrArg lanes⟩
  have hExpectedZero := hZero .expected (by simp)
  have hMeasure := runsValues_measureTraceCertificate lanes inj word before hExpectedZero
    (hZero .rightCopy (by simp)) (hZero .scratch (by simp))
  have hKeep (lane : TraceCertificateLane) (h : lane ≠ .expected) :
      measured (lanes lane) = before (lanes lane) := setValue_other (by simpa [hLane]) ..
  have hEmpty (lane : TraceCertificateLane) (hE : lane ≠ .expected)
      (h : lane ∉ [.inputLength, .arity, .oldCount, .newCount, .certificateLength]) :
      measured (lanes lane) = 0 := (hKeep lane hE).trans (hZero lane h)
  have hMeasuredCert : measured (lanes .certificateLength) = cert.length :=
    (hKeep _ (by decide)).trans hCert
  have hMeasuredExpected : measured (lanes .expected) = expected := setValue_same ..
  have hMeasuredArity : measured (lanes .arity) = n := hKeep _ (by decide)
  have hLeft := hEmpty .leftCopy (by decide) (by simp)
  have hRight := hEmpty .rightCopy (by decide) (by simp)
  have hScratch := hEmpty .scratch (by decide) (by simp)
  have hFailure := hEmpty .failure (by decide) (by simp)
  have hCheck : ∃ ticks ≤ 16 * cert.length + 7 * n + 8 * word.length + 24, ∃ failure,
      (ifEqual (lanes .certificateLength) (lanes .expected) (lanes .leftCopy)
        (lanes .rightCopy) (lanes .scratch) same bad).RunsValues word
          (ifEqualTime cert.length expected + ticks) measured
          (setValue (lanes .failure) failure measured) ∧
      (failure = 0 ↔ MergeTraceCertificateLayout n old new cert) := by
    by_cases hEq : cert.length = expected
    · have hIn : n < cert.length := by
        rw [hEq]
        unfold expected mergeTraceCertificateLength mergeTraceCertificateClaimOffset
          mergeTraceCertificateNewOffset mergeTraceCertificateOldOffset
        omega
      obtain ⟨ticks, hTicks, hRun⟩ := runsValues_checkCertificateHighBit lanes inj query cert
        measured hMeasuredCert (hEmpty .position (by decide) (by simp))
        hLeft hRight hScratch hFailure (hMeasuredArity.symm ▸ hIn)
      rw [hMeasuredArity] at hTicks hRun
      have hFrameBit : (cert[n]?.getD true).toNat = 0 ↔ cert[n]? = some false := by
        rw [List.getElem?_eq_getElem hIn]
        cases cert[n] <;> simp
      refine ⟨ticks, hTicks, _, ?_, ⟨fun h ↦ ⟨hEq, hFrameBit.mp h⟩,
        fun h ↦ hFrameBit.mpr h.high_clear⟩⟩
      intro output
      let cfg : Config R Unit := ⟨none, measured, none, output⟩
      have hRunEq := run_ifEqual_eq (left := lanes .certificateLength) (right := lanes .expected)
        (equal := same) (different := bad) word
        (by simp [hLane]) (by simp [hLane]) (by simp [hLane]) (by simp [hLane])
        (by simp [hLane]) (by simp [hLane]) (by simp [hLane]) (by simp [hLane]) cfg
        hLeft hRight hScratch (by simpa only [cfg, hMeasuredCert, hMeasuredExpected] using hEq)
        (hRun output) rfl
      simpa only [cfg, hMeasuredCert, hMeasuredExpected] using hRunEq
    · have hBadRun : bad.RunsValues word 1 measured (setValue (lanes .failure) 1 measured) := by
        simpa only [hFailure, Nat.zero_add, bad] using
          runsValues_incrementBy (lanes .failure) 1 word measured
      refine ⟨1, by omega, 1, ?_, ⟨fun h ↦ (Nat.one_ne_zero h).elim,
        fun h ↦ (hEq h.length_eq).elim⟩⟩
      intro output
      let cfg : Config R Unit := ⟨none, measured, none, output⟩
      have hRunNe := run_ifEqual_ne (left := lanes .certificateLength) (right := lanes .expected)
        (equal := same) (different := bad) word
        (by simp [hLane]) (by simp [hLane]) (by simp [hLane]) (by simp [hLane])
        (by simp [hLane]) (by simp [hLane]) (by simp [hLane]) (by simp [hLane]) cfg
        hLeft hRight hScratch (by simpa only [cfg, hMeasuredCert, hMeasuredExpected] using hEq)
        (hBadRun output) rfl
      simpa only [cfg, hMeasuredCert, hMeasuredExpected] using hRunNe
  obtain ⟨ticks, hTicks, failure, hCheckRun, hValid⟩ := hCheck
  let flagged := setValue (lanes .failure) failure measured
  have hStillExpected : flagged (lanes .expected) = expected :=
    (setValue_other (by simp [hLane]) ..).trans hMeasuredExpected
  have hFinal : setValue (lanes .expected) 0 flagged =
      setValue (lanes .failure) failure before := by
    funext r
    by_cases h : r = lanes .expected
    · subst r
      simp [setValue, hLane, hExpectedZero]
    simp [flagged, measured, setValue, h]
  have hClear := runsValues_clearCertificateLane (lanes .expected) word flagged
  rw [hStillExpected, hFinal] at hClear
  refine ⟨_, ?_, failure, (hMeasure.seq hCheckRun).seq hClear, hValid⟩
  change _ ≤ traceCertificateRegisterCost (before (lanes .inputLength)) n old new cert.length
  have hPhysical : before (lanes .inputLength) = word.length := hLength
  rw [hPhysical]
  unfold traceCertificateRegisterCost ifEqualTime expected mergeTraceCertificateLength
    mergeTraceCertificateClaimOffset mergeTraceCertificateNewOffset mergeTraceCertificateOldOffset
  omega

end PvsNP.MCSP
