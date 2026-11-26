module

public import PvsNP.SAT.CrossingFamily

/-! # Crossing construction with multiple bits per address

A row carries one choice for each payload slot. A shared header allows at
most one payload variable to be true. At the selected address, both rows
must allow that same payload, so the two tables must differ in some slot.
-/

public section

namespace PvsNP.SATCrossing.Palette

open AssignmentQueryTree (allAssignments mem_allAssignments length_allAssignments)

abbrev Table (r : Nat) := Address r → Fin r → Bool

@[expose] def signedLiteral (i : Nat) (value : Bool) : CNF.Literal Nat :=
  if value then .pos i else .neg i

@[simp] theorem literalIndex_signedLiteral (i : Nat) (value : Bool) :
    CNFCode.literalIndex (signedLiteral i value) = i := by
  cases value <;> rfl

private theorem signedLiteral_sat (σ : Nat → Bool) (i : Nat) (value : Bool) :
    (signedLiteral i value).Sat σ ↔ σ i = value := by
  cases value <;> simp [signedLiteral]

@[expose] def payloadIndex (r : Nat) (s : Fin r) (bit : Bool) : Nat :=
  r + 2 * s.val + bit.toNat

@[expose] def header (r : Nat) : CNF.Formula Nat :=
  (List.range (2 * r)).flatMap fun p ↦ (List.range p).map fun q ↦
    [.neg (r + q), .neg (r + p)]

@[expose] def rowClause (r : Nat) (address : Address r) (values : Fin r → Bool) : CNF.Clause Nat :=
  (List.ofFn fun i : Fin r ↦ signedLiteral i.val (!(address i))) ++
    List.ofFn fun s : Fin r ↦ .pos (payloadIndex r s (values s))

@[expose] def side (r : Nat) (values : Table r) : CNF.Formula Nat :=
  (allAssignments r).map fun address ↦ rowClause r address (values address)

private theorem three_mul_gt_payloadIndex (r : Nat) (s : Fin r) (bit : Bool) :
    payloadIndex r s bit < 3 * r := by
  have hs := s.isLt
  have hb := Bool.toNat_le bit
  unfold payloadIndex
  omega

private theorem le_payloadIndex (r : Nat) (s : Fin r) (bit : Bool) :
    r ≤ payloadIndex r s bit := by
  unfold payloadIndex
  omega

private theorem payloadIndex_injective (r : Nat) {s t : Fin r} {a b : Bool}
    (h : payloadIndex r s a = payloadIndex r t b) : s = t ∧ a = b := by
  unfold payloadIndex at h
  cases a <;> cases b <;> simp [Bool.toNat] at h
  · exact ⟨Fin.ext (by omega), rfl⟩
  · omega
  · omega
  · exact ⟨Fin.ext (by omega), rfl⟩

private theorem header_sat (r : Nat) (σ : Nat → Bool) :
    CNF.Sat σ (header r) ↔
      ∀ p, p < 2 * r → ∀ q, q < p → σ (r + q) = false ∨ σ (r + p) = false := by
  simp [header, CNF.sat_flatMap, CNF.sat_map]

private theorem header_unique (r : Nat) (σ : Nat → Bool) (h : CNF.Sat σ (header r))
    (i j : Nat) (hi : r ≤ i) (hi' : i < 3 * r) (hj : r ≤ j) (hj' : j < 3 * r)
    (hsi : σ i = true) (hsj : σ j = true) : i = j := by
  have hPairs := (header_sat r σ).mp h
  rcases lt_trichotomy i j with hij | hij | hij
  · have hPair := hPairs (j - r) (by omega) (i - r) (by omega)
    rw [show r + (i - r) = i by omega, show r + (j - r) = j by omega, hsi, hsj] at hPair
    simp at hPair
  · exact hij
  · have hPair := hPairs (i - r) (by omega) (j - r) (by omega)
    rw [show r + (j - r) = j by omega, show r + (i - r) = i by omega, hsi, hsj] at hPair
    simp at hPair

private theorem rowClause_sat (r : Nat) (σ : Nat → Bool)
    (address : Address r) (values : Fin r → Bool) :
    CNF.Clause.Sat σ (rowClause r address values) ↔
      ((fun i : Fin r ↦ σ i.val) = address →
        ∃ s : Fin r, σ (payloadIndex r s (values s)) = true) := by
  rw [rowClause, CNF.Clause.sat_append]
  simp only [CNF.Clause.Sat, List.mem_ofFn]
  constructor
  · rintro (⟨literal, ⟨i, rfl⟩, hSat⟩ | ⟨literal, ⟨s, rfl⟩, hSat⟩) hAddr
    · have hDifferent := (signedLiteral_sat σ i.val (!(address i))).mp hSat
      have hi : σ i.val = address i := congrFun hAddr i
      rw [hi] at hDifferent
      cases address i <;> simp at hDifferent
    · exact ⟨s, hSat⟩
  · intro hRow
    by_cases hAddr : (fun i : Fin r ↦ σ i.val) = address
    · obtain ⟨s, hs⟩ := hRow hAddr
      exact Or.inr ⟨_, ⟨s, rfl⟩, hs⟩
    · obtain ⟨i, hi⟩ : ∃ i : Fin r, σ i.val ≠ address i := by
        by_contra! hall
        exact hAddr (funext hall)
      refine Or.inl ⟨_, ⟨i, rfl⟩, (signedLiteral_sat _ _ _).mpr ?_⟩
      cases hBit : address i <;> simpa [hBit] using hi

private theorem side_sat (r : Nat) (σ : Nat → Bool)
    (values : Table r) :
    CNF.Sat σ (side r values) ↔ ∃ s : Fin r,
      σ (payloadIndex r s (values (fun i : Fin r ↦ σ i.val) s)) = true := by
  rw [side, CNF.sat_map]
  constructor
  · intro hSide
    exact (rowClause_sat r σ _ _).mp (hSide _ (mem_allAssignments _)) rfl
  · intro hPayload address _
    exact (rowClause_sat r σ address _).mpr (fun hEqual ↦ hEqual ▸ hPayload)

/-- The combined clauses are satisfiable exactly when the tables differ. -/
theorem satisfiable_iff_ne (r : Nat) (a b : Table r) :
    CNF.Satisfiable (header r ++ side r a ++ side r (fun j s ↦ !(b j s))) ↔ a ≠ b := by
  simp only [CNF.Satisfiable, CNF.sat_append]
  constructor
  · rintro ⟨σ, ⟨hHead, hLeft⟩, hRight⟩ hEqual
    subst b
    obtain ⟨s, hs⟩ := (side_sat r σ a).mp hLeft
    obtain ⟨t, ht⟩ := (side_sat r σ (fun j s ↦ !(a j s))).mp hRight
    let j : Address r := fun i ↦ σ i.val
    have hIndex := header_unique r σ hHead _ _ (le_payloadIndex r s (a j s))
      (three_mul_gt_payloadIndex r s (a j s)) (le_payloadIndex r t (!(a j t)))
      (three_mul_gt_payloadIndex r t (!(a j t))) hs ht
    obtain ⟨rfl, hBit⟩ := payloadIndex_injective r hIndex
    cases a j s <;> simp at hBit
  · intro hDifferent
    obtain ⟨j, s, hs⟩ : ∃ j : Address r, ∃ s : Fin r, a j s ≠ b j s := by
      by_contra! hall
      exact hDifferent (funext fun j ↦ funext (hall j))
    let p := payloadIndex r s (a j s)
    let σ (i : Nat) : Bool := if h : i < r then j ⟨i, h⟩ else decide (i = p)
    have hAddress : (fun i : Fin r ↦ σ i.val) = j := by
      funext i
      simp only [σ, dite_eq_left i.isLt]
    have hPayload : σ p = true := by
      have hge := le_payloadIndex r s (a j s)
      simp [σ, p, Nat.not_lt.mpr hge]
    have hAfter (i : Nat) (hi : r ≤ i) : σ i = decide (i = p) := by
      exact dite_eq_right (Nat.not_lt.mpr hi)
    have hHead : CNF.Sat σ (header r) := (header_sat r σ).mpr fun u _ v hv ↦ by
      by_cases hEq : r + v = p
      · right
        rw [hAfter (r + u) (by omega), decide_eq_false_iff_not]
        omega
      · left
        rw [hAfter (r + v) (by omega), decide_eq_false_iff_not]
        exact hEq
    have hBit : a j s = !(b j s) := by
      cases hb : b j s <;> simpa [hb] using hs
    refine ⟨σ, ⟨hHead, (side_sat r σ a).mpr ?_⟩,
      (side_sat r σ (fun j s ↦ !(b j s))).mpr ?_⟩
    · rw [hAddress]
      exact ⟨s, hPayload⟩
    · rw [hAddress]
      exact ⟨s, by simpa only [← hBit] using hPayload⟩

@[simp] theorem length_side (r : Nat) (a : Table r) : (side r a).length = 2 ^ r := by
  simp only [side, List.length_map, length_allAssignments]

theorem side_clause_bounds (r : Nat) (a : Table r) (c : CNF.Clause Nat) (hc : c ∈ side r a) :
    c.length ≤ 2 * r ∧ ∀ l ∈ c, CNFCode.literalIndex l < 3 * r := by
  obtain ⟨address, _, rfl⟩ := List.mem_map.mp hc
  constructor
  · simp only [rowClause, List.length_append, List.length_ofFn]
    omega
  · intro l hl
    rcases List.mem_append.mp hl with hAddress | hPayload
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hAddress
      rw [literalIndex_signedLiteral]
      have hi := i.isLt
      omega
    · obtain ⟨s, rfl⟩ := List.mem_ofFn.mp hPayload
      exact three_mul_gt_payloadIndex r s _

theorem length_header_le (r : Nat) : (header r).length ≤ (2 * r) ^ 2 := by
  suffices (header r).length ≤ (List.range (2 * r)).length * (2 * r) by
    simpa only [List.length_range, pow_two] using this
  unfold header
  generalize hRange : List.range (2 * r) = xs
  have hEntries (p : Nat) (hp : p ∈ xs) : p ≤ 2 * r := by
    rw [← hRange, List.mem_range] at hp
    omega
  clear hRange
  induction xs with
  | nil => simp
  | cons p xs ih =>
    have hp := hEntries p (List.mem_cons_self ..)
    have hTail := ih (fun q hq ↦ hEntries q (List.mem_cons_of_mem _ hq))
    simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_range,
      List.length_cons]
    rw [Nat.succ_mul, Nat.add_comm (xs.length * (2 * r)) (2 * r)]
    exact Nat.add_le_add hp hTail

theorem header_clause_bounds (r : Nat) (c : CNF.Clause Nat) (hc : c ∈ header r) :
    c.length ≤ 2 ∧ ∀ l ∈ c, CNFCode.literalIndex l < 3 * r := by
  obtain ⟨p, hp, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hc
  simp only [List.mem_range] at hp hq
  refine ⟨by simp, ?_⟩
  intro l hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl <;> change r + _ < 3 * r <;> omega

end PvsNP.SATCrossing.Palette
