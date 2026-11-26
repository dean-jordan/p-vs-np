module

public import PvsNP.Complexity.PackedPairs

/-! # Input positions in nested binary encodings of Cook pairs -/

public section

namespace PvsNP

private def taggedData (word : BinaryWord) : BinaryWord :=
  word.flatMap fun bit ↦ [false, bit]

private theorem length_taggedData (word : BinaryWord) :
    (taggedData word).length = 2 * word.length := by
  induction word with
  | nil => rfl
  | cons bit tail ih =>
    simp only [taggedData, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    omega

private theorem getElem?_taggedData (word : BinaryWord) (i : Nat) :
    (taggedData word)[2 * i + 1]? = word[i]? := by
  induction word generalizing i with
  | nil => simp [taggedData]
  | cons b rest ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have hIndex : 2 * (i + 1) + 1 = (2 * i + 1) + 1 + 1 := by omega
      rw [hIndex]
      exact ih i

private theorem packedPair_layout (x y : BinaryWord) :
    packedPair x y = taggedData x ++ ([true, false] ++ taggedData y) := by
  simp only [packedPair, encodePair_eq, Machine.packInput, List.flatMap_append,
    List.flatMap_cons, List.flatMap_map, verifierSymbolCode,
    Function.Embedding.coeFn_mk, taggedData]

theorem getElem?_packedPair_left (x y : BinaryWord) {i : Nat} (h : i < x.length) :
    (packedPair x y)[2 * i + 1]? = x[i]? := by
  rw [packedPair_layout, List.getElem?_append_left (by rw [length_taggedData]; omega)]
  exact getElem?_taggedData x i

theorem getElem?_packedPair_right (x y : BinaryWord) (i : Nat) :
    (packedPair x y)[2 * (x.length + 1) + 2 * i + 1]? = y[i]? := by
  rw [packedPair_layout, List.getElem?_append_right (by rw [length_taggedData]; omega),
    length_taggedData]
  have hPosition : 2 * (x.length + 1) + 2 * i + 1 - 2 * x.length = (2 * i + 1) + 1 + 1 :=
    by omega
  rw [hPosition]
  exact getElem?_taggedData y i

/-- Locate a request bit within the query field of the outer checking word. -/
theorem getElem?_packedPair_nested_request (request candidate row : BinaryWord)
    {i : Nat} (h : i < request.length) :
    (packedPair (packedPair request candidate) row)[4 * i + 3]? = request[i]? := by
  rw [show 4 * i + 3 = 2 * (2 * i + 1) + 1 from by omega,
    getElem?_packedPair_left _ _ (by rw [length_packedPair]; omega)]
  exact getElem?_packedPair_left _ _ h

/-- Locate a candidate bit within the query field of the outer checking word. -/
theorem getElem?_packedPair_nested_candidate (request candidate row : BinaryWord)
    {i : Nat} (h : i < candidate.length) :
    (packedPair (packedPair request candidate) row)[4 * (request.length + 1 + i) + 3]? =
      candidate[i]? := by
  rw [show 4 * (request.length + 1 + i) + 3 =
      2 * (2 * (request.length + 1) + 2 * i + 1) + 1 from by omega,
    getElem?_packedPair_left _ _ (by rw [length_packedPair]; omega)]
  exact getElem?_packedPair_right _ _ _

/-- Locate a bit in the outer certificate field using the register machine's reverse indexing. -/
theorem getElem?_reverse_packedPair_certificate (query certificate : BinaryWord)
    {i : Nat} (h : i < certificate.length) :
    (packedPair query certificate).reverse[2 * (certificate.length - 1 - i)]? =
      certificate[i]? := by
  let pos := 2 * (query.length + 1) + 2 * i + 1
  have hPos : pos < (packedPair query certificate).length := by
    rw [length_packedPair]
    unfold pos
    omega
  have hRev : (packedPair query certificate).length - 1 - pos =
      2 * (certificate.length - 1 - i) := by
    rw [length_packedPair]
    unfold pos
    omega
  have hRead := List.getElem?_reverse' (l := packedPair query certificate)
    (i := (packedPair query certificate).length - 1 - pos) (j := pos) (by omega)
  rw [← hRev, hRead]
  exact getElem?_packedPair_right _ _ _

/-- The reverse position of the last bit of a forward strided window. -/
@[expose] def reverseWindowStart (wordLength start stride width : Nat) : Nat :=
  wordLength - 1 - (start + stride * (width - 1))

/-- A physical window written in forward order can be read from its last bit
back to its first bit at the same stride. -/
theorem reverseWindowReads_of_forward {word field : BinaryWord} {start stride : Nat}
    (hRead : ∀ i, i < field.length → word[start + stride * i]? = field[i]?) :
    ∀ i, i < field.length →
      word.reverse[reverseWindowStart word.length start stride field.length + stride * i]? =
        field.reverse[i]? := by
  intro i hi
  let last := field.length - 1
  let j := last - i
  have hLast : last < field.length := by dsimp [last]; omega
  have hj : j < field.length := by dsimp [j, last]; omega
  have hLastRaw := hRead last hLast
  rw [List.getElem?_eq_getElem hLast] at hLastRaw
  have hLastRawIn := (List.getElem?_eq_some_iff.mp hLastRaw).choose
  have hSum : i + j = last := by dsimp [j, last]; omega
  have hScale : stride * i + stride * j = stride * last := by rw [← Nat.mul_add, hSum]
  have hIndex : reverseWindowStart word.length start stride field.length + stride * i +
      (start + stride * j) + 1 = word.length := by
    change word.length - 1 - (start + stride * last) + stride * i +
      (start + stride * j) + 1 = word.length
    omega
  have hFieldIndex : i + j + 1 = field.length := by dsimp [last] at hSum; omega
  rw [List.getElem?_reverse' hIndex, List.getElem?_reverse' hFieldIndex]
  exact hRead j hj

end PvsNP
