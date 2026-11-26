module

public import PvsNP.SAT.AppendQuery
public import PvsNP.TuringMachine.TrackCall.QueryEdit.Edits

/-! # Contents and marks of a protected SAT query buffer

Cell edits preserve the correspondence between the protected track and
its finite word while updating the formula terminator and trial sign.
-/

@[expose] public section

namespace PvsNP.SATSearch

open TrackCall.QueryEdit

/-- A nonempty word placed at the origin with its terminator and optional trial sign marked. -/
structure QueryBuffer {ρ : Type} (data : Int → Cell ρ) (word : BinaryWord)
    (signMark : Option Nat) : Prop where
  nonempty : word ≠ []
  bits : ∀ i : Int, bit (data i) = if i < 0 then none else word[i.toNat]?
  tail_mark : ∀ i : Int, tail (data i) = decide (i = (word.dropLast.length : Int))
  pending_mark : ∀ i : Int, pending (data i) = decide (signMark.map Int.ofNat = some i)

private theorem encodeIndex_eq_replicate (i : Nat) :
    CNFCode.encodeIndex i = List.replicate i true ++ [false] := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [CNFCode.encodeIndex, List.replicate_succ, List.cons_append, ih]

private theorem appendEdits_bits (i : Nat) :
    (appendEdits i).map Edit.bit = appendUnitBlock i false := by
  simp only [appendEdits, appendUnitBlock, encodeIndex_eq_replicate, List.map_append, List.map_cons,
    List.map_nil, List.map_replicate, List.append_assoc]
  rfl

private theorem appendEdits_tail_map (i : Nat) :
    (appendEdits i).map Edit.tail = List.replicate (i + 5) false ++
      true :: List.replicate 0 false := by
  rw [show i + 5 = 3 + i + 2 by omega]
  simp only [appendEdits, List.map_append, List.map_cons, List.map_nil, List.map_replicate,
    List.replicate_add, List.append_assoc]
  rfl

private theorem appendEdits_pending_map (i : Nat) :
    (appendEdits i).map Edit.pending = List.replicate 2 false ++
      true :: List.replicate (i + 3) false := by
  simp only [appendEdits, List.map_append, List.map_cons, List.map_nil, List.map_replicate,
    List.replicate_add, List.append_assoc]
  rfl

private theorem getElem?_singleMark (before after j : Nat) (hj : j < before + 1 + after) :
    (List.replicate before false ++ true :: List.replicate after false)[j]? =
      some (decide (j = before)) := by
  by_cases hBefore : j < before
  · rw [List.getElem?_append_left (by simpa using hBefore),
      List.getElem?_replicate_of_lt hBefore]
    simp [Nat.ne_of_lt hBefore]
  · rw [List.getElem?_append_right (by simpa using Nat.le_of_not_gt hBefore),
      List.length_replicate]
    by_cases hHere : j = before
    · simp [hHere]
    · have hOffset : j - before = j - before - 1 + 1 := by omega
      rw [hOffset, List.getElem?_cons_succ, List.getElem?_replicate_of_lt (by omega)]
      simp [hHere]

private theorem appendEdits_tail_at (i j : Nat) (hj : j < (appendEdits i).length) :
    (appendEdits i)[j].tail = decide (j = i + 5) := by
  have h := congrArg (fun marks : List Bool ↦ marks[j]?) (appendEdits_tail_map i)
  have hBound : j < i + 5 + 1 + 0 := by rw [length_appendEdits] at hj; omega
  rw [List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some,
    getElem?_singleMark (i + 5) 0 j hBound] at h
  exact Option.some.inj h

private theorem appendEdits_pending_at (i j : Nat) (hj : j < (appendEdits i).length) :
    (appendEdits i)[j].pending = decide (j = 2) := by
  have h := congrArg (fun marks : List Bool ↦ marks[j]?) (appendEdits_pending_map i)
  have hBound : j < 2 + 1 + (i + 3) := by rw [length_appendEdits] at hj; omega
  rw [List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some,
    getElem?_singleMark 2 (i + 3) j hBound] at h
  exact Option.some.inj h

/-- The physical append block extends the word and leaves exactly its new sign pending. -/
theorem queryBuffer_append {ρ : Type} {data : Int → Cell ρ} {word : BinaryWord}
    (h : QueryBuffer data word none) (i : Nat) :
    QueryBuffer (writeEdits (word.dropLast.length : Int) (appendEdits i) data)
      (appendUnitQuery word i false) (some (word.dropLast.length + 2)) := by
  let start := word.dropLast.length
  let output := writeEdits (start : Int) (appendEdits i) data
  let query := appendUnitQuery word i false
  have hLength : query.length = start + (i + 6) := length_appendUnitQuery word i false
  have hTail : query.dropLast.length = start + (i + 5) := by
    rw [List.length_dropLast, hLength]
    omega
  have hCell (j : Int) :
      bit (output j) = (if j < 0 then none else query[j.toNat]?) ∧
      tail (output j) = decide (j = (↑(start + (i + 5)) : Int)) ∧
      pending (output j) = decide ((↑(start + 2) : Int) = j) := by
    by_cases hBefore : j < (start : Int)
    · have hOut : output j = data j := writeEdits_outside _ _ _ j (Or.inl hBefore)
      rw [hOut, h.bits, h.tail_mark, h.pending_mark]
      have hOld : j ≠ (start : Int) := by omega
      have hNew : j ≠ (↑(start + (i + 5)) : Int) := by omega
      have hSign : (↑(start + 2) : Int) ≠ j := by omega
      refine ⟨?_, ?_, by simp only [Option.map_none, reduceCtorEq, decide_false, hSign]⟩
      · by_cases hNeg : j < 0
        · simp [hNeg]
        · have hIndex : j.toNat < start := by omega
          have hIndex' : j.toNat < word.length - 1 := by
            simpa only [start, List.length_dropLast] using hIndex
          simp only [ite_eq_right hNeg, query, appendUnitQuery, List.getElem?_append_left hIndex,
            List.getElem?_dropLast, ite_eq_left hIndex']
      · change decide (j = (start : Int)) = _
        simp only [hOld, hNew]
    · by_cases hInside : j < (start : Int) + ((appendEdits i).length : Int)
      · let offset := j.toNat - start
        have hOffset : j = (start : Int) + (offset : Int) := by dsimp [offset]; omega
        have hOffsetLt : offset < (appendEdits i).length := by omega
        have hWritten := writeEdits_at (start : Int) (appendEdits i) data offset hOffsetLt
        rw [← hOffset] at hWritten
        change output j = _ at hWritten
        rw [hWritten]
        have hBit : query[j.toNat]? = some (appendEdits i)[offset].bit := by
          change (word.dropLast ++ appendUnitBlock i false)[j.toNat]? = _
          rw [List.getElem?_append_right (show start ≤ j.toNat by omega),
            show j.toNat - word.dropLast.length = offset from rfl, ← appendEdits_bits,
            List.getElem?_map, List.getElem?_eq_getElem hOffsetLt, Option.map_some]
        have hEnd : offset = i + 5 ↔ j = (↑(start + (i + 5)) : Int) := by omega
        have hSign : offset = 2 ↔ (↑(start + 2) : Int) = j := by omega
        refine ⟨?_, ?_, ?_⟩
        · simp only [bit, writeCell, ite_eq_right (show ¬ j < 0 by omega), hBit]
        · change (appendEdits i)[offset].tail = _
          rw [appendEdits_tail_at]
          exact decide_eq_decide.mpr hEnd
        · change (appendEdits i)[offset].pending = _
          rw [appendEdits_pending_at]
          exact decide_eq_decide.mpr hSign
      · have hAfter : (start : Int) + ((appendEdits i).length : Int) ≤ j := by omega
        have hOut : output j = data j := writeEdits_outside _ _ _ j (Or.inr hAfter)
        rw [hOut, h.bits, h.tail_mark, h.pending_mark]
        rw [length_appendEdits] at hAfter
        have hOld : j ≠ (start : Int) := by omega
        have hNew : j ≠ (↑(start + (i + 5)) : Int) := by omega
        have hSign : (↑(start + 2) : Int) ≠ j := by omega
        have hStart : start = word.length - 1 := List.length_dropLast
        have hWordLength : word.length ≤ j.toNat := by omega
        have hQueryLength : query.length ≤ j.toNat := by omega
        refine ⟨?_, ?_, by simp only [Option.map_none, reduceCtorEq, decide_false, hSign]⟩
        · simp only [ite_eq_right (show ¬ j < 0 by omega), List.getElem?_eq_none hWordLength,
            List.getElem?_eq_none hQueryLength]
        · change decide (j = (start : Int)) = _
          simp only [hOld, hNew]
  refine ⟨List.length_pos_iff.mp (show 0 < query.length by omega), fun j ↦ (hCell j).1,
    fun j ↦ ?_, fun j ↦ ?_⟩
  · change tail (output j) = decide (j = (query.dropLast.length : Int))
    rw [hTail]
    exact (hCell j).2.1
  · simpa only [Option.map_some, Option.some.injEq, Int.ofNat_eq_natCast] using (hCell j).2.2

/-- Committing the pending sign keeps the terminator and clears the pending marker. -/
theorem queryBuffer_commit {ρ : Type} {data : Int → Cell ρ} {word : BinaryWord} {s : Nat}
    (h : QueryBuffer data word (some s)) (hs : s < word.dropLast.length) (b : Bool) :
    QueryBuffer (updateCell (s : Int) (ordinary b) data) (word.set s b) none := by
  have hSize : s < word.length := by rw [List.length_dropLast] at hs; omega
  have hTail : (word.set s b).dropLast.length = word.dropLast.length := by simp
  refine ⟨List.length_pos_iff.mp (by simp [List.length_pos_iff.mpr h.nonempty]), ?_, ?_, ?_⟩
  · intro j
    by_cases hHere : j = (s : Int)
    · subst j
      simp [updateCell, writeCell, ordinary, bit, List.getElem?_set_self hSize]
    · rw [updateCell, ite_eq_right hHere, h.bits]
      by_cases hNeg : j < 0
      · simp [hNeg]
      · have hOther : s ≠ j.toNat := by omega
        simp only [ite_eq_right hNeg, List.getElem?_set_ne hOther]
  · intro j
    by_cases hHere : j = (s : Int)
    · subst j
      have hBefore : (s : Int) ≠ (word.dropLast.length : Int) := by omega
      rw [updateCell, ite_eq_left rfl, hTail]
      change false = decide ((s : Int) = (word.dropLast.length : Int))
      simp only [hBefore, decide_false]
    · rw [updateCell, ite_eq_right hHere, h.tail_mark, hTail]
  · intro j
    by_cases hHere : j = (s : Int)
    · subst j
      simp [updateCell, writeCell, ordinary, pending]
    · rw [updateCell, ite_eq_right hHere, h.pending_mark]
      simp [Ne.symm hHere]

end PvsNP.SATSearch
