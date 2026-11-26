module

public import PvsNP.MCSP.RequestLayout
public import PvsNP.Complexity.PackedOffsets

/-! # Physical windows of a parsed merge request -/

public section

namespace PvsNP.MCSP

@[expose] def MergeRequestFields.counterStart (fields : MergeRequestFields) : Nat :=
  fields.arity + fields.cap + 2

@[expose] def MergeRequestFields.oldStart (fields : MergeRequestFields) : Nat :=
  fields.counterStart + fields.arity + 2

@[expose] def MergeRequestFields.prefStart (fields : MergeRequestFields) : Nat :=
  fields.oldStart + fields.oldCode.length

private theorem getElem?_packed_request_segment (first field last candidate cert : BinaryWord)
    {i : Nat} (hi : i < field.length) :
    let word := packedPair (packedPair (first ++ (field ++ last)) candidate) cert
    word[4 * (first.length + i) + 3]? = field[i]? := by
  dsimp only
  rw [getElem?_packedPair_nested_request _ _ _ (by simp only [List.length_append]; omega),
    List.getElem?_append_right (Nat.le_add_right ..), Nat.add_sub_cancel_left,
    List.getElem?_append_left hi]

private def requestHeaders (fields : MergeRequestFields) : BinaryWord :=
  unaryField fields.arity ++ unaryField fields.cap

private theorem length_requestHeaders (fields : MergeRequestFields) :
    (requestHeaders fields).length = fields.counterStart := by
  simp only [requestHeaders, unaryField, MergeRequestFields.counterStart, List.length_append,
    List.length_replicate, List.length_cons, List.length_nil]
  omega

/-- Read the little-endian counter at its ordinary stride-four address. -/
theorem getElem?_packedRequestCounter {request : BinaryWord} {fields : MergeRequestFields}
    (hFields : readMergeRequestFields request = some fields) (candidate cert : BinaryWord)
    {i : Nat} (hi : i < fields.counter.length) :
    (packedPair (packedPair request candidate) cert)[4 * (fields.counterStart + i) + 3]? =
      fields.counter[i]? := by
  have hWord := (readMergeRequestFields_eq_some_iff.mp hFields).2
  have hSplit : fields.word = requestHeaders fields ++ (fields.counter ++
      fields.bit :: (fields.oldCode ++ fields.pref)) := by
    simp only [MergeRequestFields.word, MergeRequestFields.body, requestHeaders, List.append_assoc]
  rw [hWord, hSplit, ← length_requestHeaders]
  exact getElem?_packed_request_segment _ _ _ candidate cert hi

/-- Read the padded old description, including its output and padding fields. -/
theorem getElem?_packedRequestOld {request : BinaryWord} {fields : MergeRequestFields}
    (hFields : readMergeRequestFields request = some fields) (candidate cert : BinaryWord)
    {i : Nat} (hi : i < fields.oldCode.length) :
    (packedPair (packedPair request candidate) cert)[4 * (fields.oldStart + i) + 3]? =
      fields.oldCode[i]? := by
  obtain ⟨hFit, hWord⟩ := readMergeRequestFields_eq_some_iff.mp hFields
  let first := (requestHeaders fields ++ fields.counter) ++ [fields.bit]
  have hSplit : fields.word = first ++ (fields.oldCode ++ fields.pref) := by
    simp only [first, requestHeaders, MergeRequestFields.word, MergeRequestFields.body,
      List.append_assoc, List.singleton_append]
  have hLen : first.length = fields.oldStart := by
    simp only [first, List.length_append, List.length_singleton, length_requestHeaders,
      MergeRequestFields.oldStart, hFit.counter]
    omega
  rw [hWord, hSplit, ← hLen]
  exact getElem?_packed_request_segment _ _ _ candidate cert hi

/-- The final segment of the request is exactly the required candidate prefix. -/
theorem getElem?_packedRequestPref {request : BinaryWord} {fields : MergeRequestFields}
    (hFields : readMergeRequestFields request = some fields) (candidate cert : BinaryWord)
    {i : Nat} (hi : i < fields.pref.length) :
    (packedPair (packedPair request candidate) cert)[4 * (fields.prefStart + i) + 3]? =
      fields.pref[i]? := by
  obtain ⟨hFit, hWord⟩ := readMergeRequestFields_eq_some_iff.mp hFields
  let first := ((requestHeaders fields ++ fields.counter) ++ [fields.bit]) ++ fields.oldCode
  have hSplit : fields.word = first ++ (fields.pref ++ []) := by
    simp only [first, requestHeaders, MergeRequestFields.word, MergeRequestFields.body,
      List.append_assoc, List.append_nil, List.cons_append, List.nil_append]
  have hLen : first.length = fields.prefStart := by
    simp only [first, List.length_append, List.length_singleton, length_requestHeaders,
      MergeRequestFields.prefStart, MergeRequestFields.oldStart, hFit.counter]
    omega
  rw [hWord, hSplit, ← hLen]
  exact getElem?_packed_request_segment _ _ _ candidate cert hi

end PvsNP.MCSP
