module

public import PvsNP.MCSP.Request
public import PvsNP.Complexity.PackedPairs
public import PvsNP.TuringMachine.Registers.UnaryFieldWindow

import PvsNP.Complexity.PackedOffsets

/-! # Register reads for the two merge-request header fields

The request bits start at raw position 3 and are four positions apart in
the nested pair. Both unary scans share the ordinary cursor and the remaining
logical width. They keep separate counts and validity flags.
-/

public section

namespace PvsNP.MCSP

open RegisterMachine RegisterMachine.Fragment

/-- The values and terminators observed by the two scans. -/
structure RequestHeaderProgress where
  arity : Nat
  arityValid : Bool
  cap : Nat
  capValid : Bool

@[expose] def RequestHeaderProgress.consumed (p : RequestHeaderProgress) : Nat :=
  (p.arity + p.arityValid.toNat) + (p.cap + p.capValid.toNat)

@[expose] def requestHeaderProgress (request : BinaryWord) : RequestHeaderProgress :=
  let arity := unaryWindowResult request
  let cap := unaryWindowResult (request.drop (arity.1 + arity.2.toNat))
  ⟨arity.1, arity.2, cap.1, cap.2⟩

/-- The bounded scan and the independent unary parser agree on every word. -/
theorem readUnaryField_eq_unaryWindowResult (word : BinaryWord) :
    let p := unaryWindowResult word
    readUnaryField word = if p.2 then some (p.1, word.drop (p.1 + 1)) else none := by
  induction word with
  | nil => rfl
  | cons b rest ih =>
    cases b with
    | false => rfl
    | true =>
      cases h : unaryWindowResult rest with
      | mk count found =>
        cases found
        · have hRead : readUnaryField rest = none := by simpa [h] using ih
          simp [readUnaryField, unaryWindowResult, h, hRead]
        · have hRead : readUnaryField rest = some (count, rest.drop (count + 1)) := by
            simpa [h] using ih
          simp [readUnaryField, unaryWindowResult, h, hRead]

/-- Both successful scans give the two independent parser results and their suffix. -/
theorem readUnaryFields_eq_requestHeaderProgress (request : BinaryWord) :
    (do
      let (arity, rest) ← readUnaryField request
      let (cap, suffix) ← readUnaryField rest
      pure (arity, cap, suffix)) =
    let p := requestHeaderProgress request
    if p.arityValid && p.capValid then some (p.arity, p.cap, request.drop p.consumed)
    else none := by
  rw [readUnaryField_eq_unaryWindowResult request]
  cases hArity : unaryWindowResult request with
  | mk arity flag =>
    cases flag
    · simp [requestHeaderProgress, hArity]
    · simp only [requestHeaderProgress, hArity, ite_true, Bool.toNat_true,
        Option.bind_eq_bind, Option.bind_some]
      rw [readUnaryField_eq_unaryWindowResult]
      cases unaryWindowResult (request.drop (arity + 1)) with
      | mk cap flag => cases flag <;>
          simp [RequestHeaderProgress.consumed, List.drop_drop]

theorem readUnaryFields_iff_requestHeaderProgress (request suffix : BinaryWord) (arity cap : Nat) :
    (do
      let (first, rest) ← readUnaryField request
      let (second, suffix) ← readUnaryField rest
      pure (first, second, suffix)) = some (arity, cap, suffix) ↔
    let p := requestHeaderProgress request
    p.arityValid = true ∧ p.capValid = true ∧
      (p.arity, p.cap, request.drop p.consumed) = (arity, cap, suffix) := by
  rw [readUnaryFields_eq_requestHeaderProgress]
  cases hFirst : (requestHeaderProgress request).arityValid <;>
    cases hSecond : (requestHeaderProgress request).capValid <;> simp [hFirst, hSecond]

theorem requestHeaderProgress_arity_failure (request : BinaryWord)
    (h : (requestHeaderProgress request).arityValid = false) :
    (requestHeaderProgress request).cap = 0 ∧
      (requestHeaderProgress request).capValid = false ∧
      (requestHeaderProgress request).consumed = request.length := by
  cases hResult : unaryWindowResult request with
  | mk arity flag =>
    have hFlag : flag = false := by simpa only [requestHeaderProgress, hResult] using h
    subst flag
    have hWord : request = List.replicate arity true := by
      simpa [hResult] using unaryWindowResult_spec request
    have hLength : request.length = arity := by rw [hWord, List.length_replicate]
    simp [requestHeaderProgress, RequestHeaderProgress.consumed, hResult,
      ← hLength, unaryWindowResult]

/-- The shared position and workspace and the distinct header counters. -/
inductive RequestHeaderLane where
  | inputLength | position | remaining | arity | arityValid | cap | capValid
  | lookupIndex | lookupWork | scratch
  deriving DecidableEq

private def requestUnaryLanes (second : Bool) : Fin 8 → RequestHeaderLane
  | 0 => .inputLength
  | 1 => .position
  | 2 => .remaining
  | 3 => if second then .cap else .arity
  | 4 => if second then .capValid else .arityValid
  | 5 => .lookupIndex
  | 6 => .lookupWork
  | _ => .scratch

private theorem requestUnaryLanes_injective (second : Bool) :
    Function.Injective (requestUnaryLanes second) := by cases second <;> decide

variable {R : Type}

/-- Scan arity and cap in sequence, keeping their counts and flags separate. -/
def requestHeaderRegister (lanes : RequestHeaderLane → R) : Fragment R :=
  (unaryFieldWindow 4 (lanes ∘ requestUnaryLanes false)).seq
    (unaryFieldWindow 4 (lanes ∘ requestUnaryLanes true))

@[expose] def requestHeaderRegisterCost (inputLength requestLength : Nat) : Nat :=
  2 * unaryFieldWindowCost 4 inputLength requestLength

theorem requestHeaderRegisterCost_polynomiallyBounded {inputLength requestLength : Nat → Nat}
    (hInput : PolynomiallyBounded inputLength) (hRequest : PolynomiallyBounded requestLength) :
    PolynomiallyBounded (fun n ↦ requestHeaderRegisterCost (inputLength n) (requestLength n)) :=
  (PolynomiallyBounded.const 2).mul (unaryFieldWindowCost_polynomiallyBounded 4 hInput hRequest)

/-- Exact counts and remaining input after both scans, even on malformed requests. -/
structure RequestHeaderRegisterResult (lanes : RequestHeaderLane → R) (request : BinaryWord)
    (before after : R → Nat) : Prop where
  arity : after (lanes .arity) = (requestHeaderProgress request).arity
  arityValid : after (lanes .arityValid) = (requestHeaderProgress request).arityValid.toNat
  cap : after (lanes .cap) = (requestHeaderProgress request).cap
  capValid : after (lanes .capValid) = (requestHeaderProgress request).capValid.toNat
  position : after (lanes .position) = 3 + 4 * (requestHeaderProgress request).consumed
  remaining : after (lanes .remaining) =
    (request.drop (requestHeaderProgress request).consumed).length
  frame : ∀ r, r ≠ lanes .position → r ≠ lanes .remaining → r ≠ lanes .arity →
    r ≠ lanes .arityValid → r ≠ lanes .cap → r ≠ lanes .capValid → after r = before r

variable [DecidableEq R]

/-- Run both header scans directly on a prepared nested packed input. -/
theorem runsValues_requestHeaderRegister (lanes : RequestHeaderLane → R)
    (hLanes : Function.Injective lanes) (request candidate row : BinaryWord) (before : R → Nat)
    (hLength : before (lanes .inputLength) = (packedPair (packedPair request candidate) row).length)
    (hPosition : before (lanes .position) = 3) (hWidth : before (lanes .remaining) = request.length)
    (hZero : ∀ lane, lane ≠ .inputLength → lane ≠ .position → lane ≠ .remaining →
      before (lanes lane) = 0) :
    let word := packedPair (packedPair request candidate) row
    ∃ ticks ≤ requestHeaderRegisterCost word.length request.length, ∃ after : R → Nat,
      (requestHeaderRegister lanes).RunsValues word ticks before after ∧
      RequestHeaderRegisterResult lanes request before after := by
  let word := packedPair (packedPair request candidate) row
  let first := lanes ∘ requestUnaryLanes false
  let second := lanes ∘ requestUnaryLanes true
  let arity := unaryWindowResult request
  let used := arity.1 + arity.2.toNat
  let rest := request.drop used
  let cap := unaryWindowResult rest
  have hDiff {i j : RequestHeaderLane} (h : i ≠ j) : lanes i ≠ lanes j :=
    fun e ↦ h (hLanes e)
  have hReadFirst (i : Nat) (hi : i < request.length) :
      word[before (first 1) + 4 * i]? = request[i]? := by
    change word[before (lanes .position) + 4 * i]? = _
    rw [hPosition, Nat.add_comm]
    exact getElem?_packedPair_nested_request request candidate row hi
  obtain ⟨firstTicks, hFirstCost, mid, hFirst, hPos₁, hRem₁, hArity, hValid₁, hFrame₁⟩ :=
    runsValues_unaryFieldWindow_of_reads 4 first
      (hLanes.comp (requestUnaryLanes_injective false)) word request before hLength hWidth
      (hZero _ (by decide) (by decide) (by decide))
      (hZero _ (by decide) (by decide) (by decide))
      (hZero _ (by decide) (by decide) (by decide)) hReadFirst
  have hMidFrame {lane : RequestHeaderLane} (hP : lane ≠ .position) (hW : lane ≠ .remaining)
      (hA : lane ≠ .arity) (hV : lane ≠ .arityValid) : mid (lanes lane) = before (lanes lane) :=
    hFrame₁ _ (hDiff hP) (hDiff hW) (hDiff hA) (hDiff hV)
  have hMidPos : mid (lanes .position) = 3 + 4 * used := by
    change mid (lanes .position) = _ at hPos₁
    exact hPos₁.trans (by rw [show before (first 1) = 3 from hPosition])
  have hMidRem : mid (lanes .remaining) = rest.length := by
    change mid (lanes .remaining) = before (lanes .remaining) - used at hRem₁
    rw [hRem₁, hWidth, List.length_drop]
  have hReadSecond (i : Nat) (hi : i < rest.length) :
      word[mid (second 1) + 4 * i]? = rest[i]? := by
    have hIn : used + i < request.length := by
      simp only [rest, List.length_drop] at hi
      omega
    change word[mid (lanes .position) + 4 * i]? = (request.drop used)[i]?
    rw [hMidPos, show 3 + 4 * used + 4 * i = 4 * (used + i) + 3 by omega,
      getElem?_packedPair_nested_request request candidate row hIn, List.getElem?_drop]
  have hMidZero {lane : RequestHeaderLane} (hLen : lane ≠ .inputLength)
      (hP : lane ≠ .position) (hW : lane ≠ .remaining) (hA : lane ≠ .arity)
      (hV : lane ≠ .arityValid) : mid (lanes lane) = 0 :=
    (hMidFrame hP hW hA hV).trans (hZero lane hLen hP hW)
  obtain ⟨secondTicks, hSecondCost, after, hSecond, hPos₂, hRem₂, hCap, hValid₂, hFrame₂⟩ :=
    runsValues_unaryFieldWindow_of_reads 4 second
      (hLanes.comp (requestUnaryLanes_injective true)) word rest mid
      ((hMidFrame (by decide) (by decide) (by decide) (by decide)).trans hLength) hMidRem
      (hMidZero (by decide) (by decide) (by decide) (by decide) (by decide))
      (hMidZero (by decide) (by decide) (by decide) (by decide) (by decide))
      (hMidZero (by decide) (by decide) (by decide) (by decide) (by decide)) hReadSecond
  have hAfterFrame {lane : RequestHeaderLane} (hP : lane ≠ .position) (hW : lane ≠ .remaining)
      (hC : lane ≠ .cap) (hV : lane ≠ .capValid) : after (lanes lane) = mid (lanes lane) :=
    hFrame₂ _ (hDiff hP) (hDiff hW) (hDiff hC) (hDiff hV)
  have hBudget : unaryFieldWindowCost 4 word.length rest.length ≤
      unaryFieldWindowCost 4 word.length request.length :=
    Nat.add_le_add_right (Nat.mul_le_mul_right _ (by simp [rest])) _
  refine ⟨firstTicks + secondTicks, ?_, after, hFirst.seq hSecond, ?_⟩
  · simpa only [requestHeaderRegisterCost, Nat.two_mul] using
      Nat.add_le_add hFirstCost (hSecondCost.trans hBudget)
  · constructor
    · rw [hAfterFrame (by decide) (by decide) (by decide) (by decide)]
      change mid (lanes .arity) = before (lanes .arity) + arity.1 at hArity
      rw [hArity, hZero .arity (by decide) (by decide) (by decide), Nat.zero_add]
      rfl
    · rw [hAfterFrame (by decide) (by decide) (by decide) (by decide)]
      change mid (lanes .arityValid) = before (lanes .arityValid) + arity.2.toNat at hValid₁
      rw [hValid₁, hZero .arityValid (by decide) (by decide) (by decide), Nat.zero_add]
      rfl
    · change after (lanes .cap) = mid (lanes .cap) + cap.1 at hCap
      rw [hCap, hMidZero (by decide) (by decide) (by decide) (by decide) (by decide), Nat.zero_add]
      rfl
    · change after (lanes .capValid) = mid (lanes .capValid) + cap.2.toNat at hValid₂
      rw [hValid₂, hMidZero (by decide) (by decide) (by decide) (by decide) (by decide),
        Nat.zero_add]
      rfl
    · change after (lanes .position) = mid (lanes .position) + 4 * (cap.1 + cap.2.toNat) at hPos₂
      rw [hPos₂, hMidPos]
      change _ = 3 + 4 * (used + (cap.1 + cap.2.toNat))
      omega
    · change after (lanes .remaining) = mid (lanes .remaining) - (cap.1 + cap.2.toNat) at hRem₂
      rw [hRem₂, hMidRem]
      change rest.length - (cap.1 + cap.2.toNat) =
        (request.drop (used + (cap.1 + cap.2.toNat))).length
      rw [List.length_drop, List.length_drop, Nat.sub_sub]
    · intro r hp hw ha hva hc hvc
      exact (hFrame₂ r hp hw hc hvc).trans (hFrame₁ r hp hw ha hva)

end PvsNP.MCSP
