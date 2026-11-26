module

public import Init.Data.List.Lemmas

/-! # Short-circuit traversal of assignments to a finite list of variables -/

public section

namespace PvsNP.SATAssignment

private def assignBit (initial : Nat → Bool) (index : Nat) (value : Bool) : Nat → Bool :=
  fun i ↦ if i = index then value else initial i

/-- Visit the false branch first and stop at the first accepting leaf. The second component
counts calls to `check`, including the accepting call if there is one. -/
def searchAssignments (check : (Nat → Bool) → Bool) : List Nat → (Nat → Bool) → Bool × Nat
  | [], initial => (check initial, 1)
  | index :: rest, initial =>
    let left := searchAssignments check rest (assignBit initial index false)
    if left.1 then left else
      let right := searchAssignments check rest (assignBit initial index true)
      (right.1, left.2 + right.2)

private theorem agreement_after_assign {indices : List Nat} {initial σ : Nat → Bool}
    {index : Nat} (h : ∀ i ∉ index :: indices, σ i = initial i) :
    ∀ i ∉ indices, σ i = assignBit initial index (σ index) i := by
  intro i hi
  by_cases he : i = index
  · subst i
    simp [assignBit]
  · simpa [assignBit, he] using h i (by simp [he, hi])

private theorem agreement_before_assign {indices : List Nat} {initial σ : Nat → Bool}
    {index : Nat} {b : Bool} (h : ∀ i ∉ indices, σ i = assignBit initial index b i) :
    ∀ i ∉ index :: indices, σ i = initial i := by
  intro i hi
  have he : i ≠ index := fun eq ↦ hi (List.mem_cons.mpr (Or.inl eq))
  have ht : i ∉ indices := fun hm ↦ hi (List.mem_cons_of_mem _ hm)
  simpa [assignBit, he] using h i ht

/-- Search succeeds exactly when an accepting assignment agrees with the initial values
outside the visited indices. -/
theorem searchAssignments_accepts_iff (check : (Nat → Bool) → Bool)
    (indices : List Nat) (initial : Nat → Bool) :
    (searchAssignments check indices initial).1 = true ↔
      ∃ σ, (∀ i ∉ indices, σ i = initial i) ∧ check σ = true := by
  induction indices generalizing initial with
  | nil =>
    simp only [searchAssignments, List.not_mem_nil, not_false_eq_true, true_implies]
    exact ⟨fun h ↦ ⟨initial, fun _ ↦ rfl, h⟩,
      fun ⟨σ, hAgree, hCheck⟩ ↦ (funext hAgree : σ = initial) ▸ hCheck⟩
  | cons index rest ih =>
    have verdict : (searchAssignments check (index :: rest) initial).1 = true ↔
        (searchAssignments check rest (assignBit initial index false)).1 = true ∨
          (searchAssignments check rest (assignBit initial index true)).1 = true := by
      cases h : (searchAssignments check rest (assignBit initial index false)).1 <;>
        simp [searchAssignments, h]
    rw [verdict, ih, ih]
    constructor
    · rintro (⟨σ, h, hs⟩ | ⟨σ, h, hs⟩) <;>
        exact ⟨σ, agreement_before_assign h, hs⟩
    · rintro ⟨σ, h, hs⟩
      have agrees := agreement_after_assign h
      cases hb : σ index
      · exact Or.inl ⟨σ, by simpa only [hb] using agrees, hs⟩
      · exact Or.inr ⟨σ, by simpa only [hb] using agrees, hs⟩

/-- A traversal with `k` levels checks at most `2^k` assignments. -/
theorem searchAssignments_checks_le (check : (Nat → Bool) → Bool)
    (indices : List Nat) (initial : Nat → Bool) :
    (searchAssignments check indices initial).2 ≤ 2 ^ indices.length := by
  induction indices generalizing initial with
  | nil => simp [searchAssignments]
  | cons i rest ih =>
    rw [searchAssignments, List.length_cons, Nat.pow_succ, Nat.mul_two]
    split
    · exact Nat.le_trans (ih _) (Nat.le_add_right ..)
    · exact Nat.add_le_add (ih _) (ih _)

/-- If every visited assignment is rejected, the search checks all `2^k` leaves. -/
theorem searchAssignments_checks_eq_of_rejected (check : (Nat → Bool) → Bool)
    (indices : List Nat) (initial : Nat → Bool)
    (h : (searchAssignments check indices initial).1 = false) :
    (searchAssignments check indices initial).2 = 2 ^ indices.length := by
  induction indices generalizing initial with
  | nil => simp [searchAssignments]
  | cons i rest ih =>
    cases hLeft : (searchAssignments check rest (assignBit initial i false)).1 with
    | false =>
      have hRight : (searchAssignments check rest (assignBit initial i true)).1 = false := by
        simpa only [searchAssignments, hLeft, Bool.false_eq_true, ite_false] using h
      simp only [searchAssignments, hLeft, Bool.false_eq_true, ite_false, ih _ hLeft, ih _ hRight,
        List.length_cons, Nat.pow_succ, Nat.mul_two]
    | true => simp [searchAssignments, hLeft] at h

end PvsNP.SATAssignment
