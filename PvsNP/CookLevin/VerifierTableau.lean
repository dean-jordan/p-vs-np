module

public import PvsNP.Complexity.Classes
public import PvsNP.CookLevin.Size
public import PvsNP.CookLevin.InitialTape
public import PvsNP.CookLevin.TapeWindow

/-! # Satisfiability of a verifier tableau

The first row has a fixed instance and separator, followed by certificate
symbols and then blanks. The final row must be accepting. The machine rule
between these rows is the restriction of Cook's machine to a finite window.
-/

@[expose] public section

namespace PvsNP.CookLevin

open Tableau TableauInput

variable {A : CheckingAlphabet} (M : Machine A.Symbol)

/-- Common upper bound on the encoded length for all allowed certificates. -/
def inputBound (n certificateExponent : Nat) : Nat := n + 1 + n ^ certificateExponent

/-- Enough ticks to halt on all allowed witnesses, and enough cells to store
every initial tape in one centered window. -/
def horizon (n certificateExponent timeExponent : Nat) : Nat :=
  let maxInput := inputBound n certificateExponent
  maxInput ^ timeExponent + timeExponent + maxInput

abbrev Var (width : Nat) := Atom (M.State ⊕ Bool) M.Symbol width

/-- Constraint on the initial contents of one tape cell. -/
def initialCell {width : Nat} (x : BinaryWord) (capacity offset : Nat)
    (certs : List A.Certificate) (i : Fin width) : CNF.Formula (Var M width) :=
  if i.val < offset then [[.pos (.cell 0 i M.blank)]]
  else if i.val < offset + x.length + 1 then
    [[.pos (.cell 0 i ((fixedPrefix A M x)[i.val - offset]?.getD M.blank))]]
  else if i.val < offset + x.length + 1 + capacity then
    [.pos (.cell 0 i M.blank) :: certs.map fun c ↦ .pos (.cell 0 i (M.input (A.certificate c)))]
  else [[.pos (.cell 0 i M.blank)]]

/-- A blank certificate cell forces a blank in the next certificate cell. -/
def initialGap {width : Nat} (x : BinaryWord) (capacity offset : Nat)
    (i j : Fin width) : CNF.Formula (Var M width) :=
  if offset + x.length + 1 ≤ i.val ∧ j.val = i.val + 1 ∧
      j.val < offset + x.length + 1 + capacity then
    [[.neg (.cell 0 i M.blank), .pos (.cell 0 j M.blank)]]
  else []

/-- Initial state and head, permitted certificate cells, and adjacent padding. -/
def initialClauses {width : Nat} (head : Fin width) (x : BinaryWord) (capacity : Nat)
    (certs : List A.Certificate) : CNF.Formula (Var M width) :=
  [[.pos (.state 0 (.inl M.initial))], [.pos (.head 0 head)]] ++
  (List.finRange width).flatMap (initialCell M x capacity head.val certs) ++
  (List.finRange width).flatMap fun i ↦
    (List.finRange width).flatMap (initialGap M x capacity head.val i)

private theorem sat_certificateCell {width : Nat} (certs : List A.Certificate)
    (complete : ∀ c, c ∈ certs) {σ : Var M width → Bool} {r : Row (M.State ⊕ Bool) M.Symbol width}
    (hr : EncodesRow σ 0 r) (i : Fin width) :
    CNF.Clause.Sat σ (.pos (.cell 0 i M.blank) ::
      certs.map fun c ↦ .pos (.cell 0 i (M.input (A.certificate c)))) ↔
      ∃ s : Option A.Certificate, r.cells i = certificateSymbol A M s := by
  rw [CNF.Clause.sat_cons, CNF.Literal.sat_pos, hr.2.2]
  constructor
  · rintro (hb | ⟨lit, hmem, hsat⟩)
    · exact ⟨none, hb⟩
    · obtain ⟨c, _, rfl⟩ := List.mem_map.mp hmem
      exact ⟨some c, (hr.2.2 i _).mp hsat⟩
  · rintro ⟨s, h⟩
    cases s with
    | none => exact Or.inl h
    | some c =>
      exact Or.inr ⟨_, List.mem_map_of_mem (complete c), (hr.2.2 i _).mpr h⟩

private theorem sat_initialCell_iff {width : Nat} (x : BinaryWord) (capacity offset : Nat)
    (certs : List A.Certificate) (complete : ∀ c, c ∈ certs) {σ : Var M width → Bool}
    {r : Row (M.State ⊕ Bool) M.Symbol width} (hr : EncodesRow σ 0 r) (i : Fin width) :
    CNF.Sat σ (initialCell M x capacity offset certs i) ↔
      (if i.val < offset then r.cells i = M.blank
       else if i.val < offset + x.length + 1 then
        r.cells i = (fixedPrefix A M x)[i.val - offset]?.getD M.blank
       else if i.val < offset + x.length + 1 + capacity then
        ∃ s : Option A.Certificate, r.cells i = certificateSymbol A M s
       else r.cells i = M.blank) := by
  unfold initialCell
  split <;> rename_i hLeft
  · exact (CNF.sat_unit _ _).trans (hr.2.2 _ _)
  · split <;> rename_i hPrefix
    · exact (CNF.sat_unit _ _).trans (hr.2.2 _ _)
    · split
      · simpa only [CNF.sat_cons, CNF.sat_nil, and_true] using
          sat_certificateCell M certs complete hr i
      · exact (CNF.sat_unit _ _).trans (hr.2.2 _ _)

private theorem sat_initialGap_iff {width : Nat} (x : BinaryWord) (capacity offset : Nat)
    {σ : Var M width → Bool} {r : Row (M.State ⊕ Bool) M.Symbol width}
    (hr : EncodesRow σ 0 r) (i j : Fin width) : CNF.Sat σ (initialGap M x capacity offset i j) ↔
      (offset + x.length + 1 ≤ i.val → j.val = i.val + 1 →
       j.val < offset + x.length + 1 + capacity → r.cells i = M.blank → r.cells j = M.blank) := by
  unfold initialGap
  split <;> rename_i h
  · have hfalse : σ (.cell 0 i M.blank) = false ↔ r.cells i ≠ M.blank := by
      constructor
      · intro hσ hi
        have ht := (hr.2.2 i M.blank).mpr hi
        rw [hσ] at ht
        cases ht
      · intro hi
        cases hσ : σ (.cell 0 i M.blank)
        · rfl
        · exact (hi ((hr.2.2 i M.blank).mp hσ)).elim
    have hRange : i.val + 1 < offset + x.length + 1 + capacity := h.2.1 ▸ h.2.2
    simp only [CNF.sat_cons, CNF.sat_nil, and_true, CNF.Clause.sat_cons, CNF.Clause.sat_nil,
      or_false, CNF.Literal.sat_neg, CNF.Literal.sat_pos, hr.2.2, hfalse, h.1, h.2.1, hRange,
      true_implies]
    simp only [Classical.or_iff_not_imp_left, not_not]
  · refine ⟨fun _ hi hj hb _ ↦ (h ⟨hi, hj, hb⟩).elim, fun _ ↦ CNF.sat_nil _⟩

/-- The clauses recognize exactly the specified initial state, head, and tape block. -/
theorem sat_initialClauses_iff {width : Nat} (head : Fin width) (x : BinaryWord) (capacity : Nat)
    (certs : List A.Certificate) (complete : ∀ c, c ∈ certs) {σ : Var M width → Bool}
    {r : Row (M.State ⊕ Bool) M.Symbol width} (hr : EncodesRow σ 0 r) :
    CNF.Sat σ (initialClauses M head x capacity certs) ↔
      r.state = .inl M.initial ∧ r.head = head ∧
        IsInitialCellBlock A M x capacity head.val r.cells := by
  simp only [initialClauses, CNF.sat_append, CNF.sat_flatMap, CNF.sat_cons, CNF.sat_nil, and_true,
    CNF.Clause.sat_singleton, CNF.Literal.sat_pos, hr.1, hr.2.1,
    sat_initialCell_iff M x capacity head.val certs complete hr,
    sat_initialGap_iff M x capacity head.val hr]
  unfold IsInitialCellBlock
  constructor
  · rintro ⟨⟨⟨hq, hh⟩, hc⟩, hg⟩
    have field i := hc i (List.mem_finRange i)
    refine ⟨hq, hh, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      simpa only [ite_eq_left hi] using field i
    · intro i hlo hhi
      simpa only [ite_eq_right (Nat.not_lt.mpr hlo), ite_eq_left hhi] using field i
    · intro i hlo hhi
      have hLeft : ¬ i.val < head.val := by omega
      simpa only [ite_eq_right hLeft, ite_eq_right (Nat.not_lt.mpr hlo), ite_eq_left hhi] using
        field i
    · intro i j hj hi hRange
      exact hg i (List.mem_finRange i) j (List.mem_finRange j) hi hj hRange
    · intro i hi
      have hLeft : ¬ i.val < head.val := by omega
      have hPrefix : ¬ i.val < head.val + x.length + 1 := by omega
      simpa only [ite_eq_right hLeft, ite_eq_right hPrefix, ite_eq_right (Nat.not_lt.mpr hi)] using
        field i
  · rintro ⟨hq, hh, hLeft, hPre, hCert, hAdj, hAfter⟩
    refine ⟨⟨⟨hq, hh⟩, ?_⟩, fun i _ j _ hi hj hj' ↦ hAdj i j hj hi hj'⟩
    intro i _
    split <;> rename_i hLeft'
    · exact hLeft i hLeft'
    · split <;> rename_i hPre'
      · exact hPre i (Nat.le_of_not_gt hLeft') hPre'
      · split <;> rename_i hCert'
        · exact hCert i (Nat.le_of_not_gt hPre') hCert'
        · exact hAfter i (Nat.le_of_not_gt hCert')

private def windowOf {width : Nat} (r : Row (M.State ⊕ Bool) M.Symbol width) :
    M.WindowConfig width :=
  ⟨r.state, r.head, r.cells⟩

private theorem windowOf_run {width : Nat} (r : Row (M.State ⊕ Bool) M.Symbol width) (t : Nat) :
    windowOf M (r.run (M.windowAdvance width) t) = M.windowRun t (windowOf M r) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change M.windowTick (windowOf M (r.run (M.windowAdvance width) t)) = _
    rw [ih, Machine.windowRun_succ]

private theorem windowOf_eq_start {width : Nat} (r : Row (M.State ⊕ Bool) M.Symbol width)
    (head : Fin width) (z : List A.Symbol) (hq : r.state = .inl M.initial) (hh : r.head = head)
    (hc : ∀ i, r.cells i = (M.windowStart head z).cells i) :
    windowOf M r = M.windowStart head z := by
  obtain ⟨q, i, cells⟩ := r
  change q = .inl M.initial at hq
  change i = head at hh
  change ∀ j, cells j = (M.windowStart head z).cells j at hc
  cases hq
  cases hh
  have hCells := funext hc
  subst cells
  rfl

/-- The tableau's finite size is determined by the largest permitted certificate. -/
def verifierFormula [DecidableEq M.State] [DecidableEq M.Symbol]
    (qs : List (M.State ⊕ Bool)) (symbols : List M.Symbol) (certs : List A.Certificate)
    (x : BinaryWord) (k d : Nat) : CNF.Formula (Var M (2 * horizon x.length k d + 1)) :=
  let t := horizon x.length k d
  acceptingClauses qs symbols (M.windowAdvance (2 * t + 1)) t (.inr true)
    (initialClauses M (Machine.windowCenter t) x (x.length ^ k) certs)

/-- Correctness of the tableau for the bounded acceptance of any verifier. -/
theorem satisfiable_verifierFormula_iff [DecidableEq M.State] [DecidableEq M.Symbol]
    (qs : List (M.State ⊕ Bool)) (symbols : List M.Symbol) (certs : List A.Certificate)
    (hq : ∀ q, q ∈ qs) (hs : ∀ a, a ∈ symbols) (hc : ∀ c, c ∈ certs)
    (x : BinaryWord) (k d : Nat) (hTime : ∀ z, M.HaltsWithin z (z.length ^ d + d)) :
    CNF.Satisfiable (verifierFormula M qs symbols certs x k d) ↔
      ∃ y : List A.Certificate, y.length ≤ x.length ^ k ∧ M.Accepts (A.encode x y) := by
  let t := horizon x.length k d
  let head := Machine.windowCenter t
  let rule := M.windowAdvance (2 * t + 1)
  let capacity := x.length ^ k
  have hFit : head.val + x.length + 1 + capacity ≤ 2 * t + 1 := by
    dsimp [head, t, Machine.windowCenter, horizon, inputBound, capacity]
    omega
  have hHalt (y : List A.Certificate) (hy : y.length ≤ capacity) :
      M.HaltsWithin (A.encode x y) t := by
    have hInput : (A.encode x y).length ≤ inputBound x.length k := by
      simp only [CheckingAlphabet.length_encode, inputBound]
      change y.length ≤ x.length ^ k at hy
      omega
    obtain ⟨n, hn, b, hb⟩ := hTime (A.encode x y)
    have hPow := Nat.pow_le_pow_left hInput d
    exact ⟨n, by dsimp [t, horizon]; omega, b, hb⟩
  change CNF.Satisfiable (acceptingClauses qs symbols rule t (.inr true)
    (initialClauses M head x capacity certs)) ↔ _
  rw [satisfiable_acceptingClauses_iff qs symbols hq hs rule t (.inr true) _
    (fun r ↦ r.state = .inl M.initial ∧ r.head = head ∧
      IsInitialCellBlock A M x capacity head.val r.cells)
    (fun _ _ hr ↦ sat_initialClauses_iff M head x capacity certs hc hr)]
  constructor
  · rintro ⟨r, ⟨hInit, hHead, hCells⟩, hAccept⟩
    obtain ⟨y, hy, hTape⟩ :=
      (isInitialCellBlock_iff_exists_certificate A M x capacity head.val r.cells hFit).mp hCells
    have start : windowOf M r = M.windowStart head (A.encode x y) :=
      windowOf_eq_start M r head (A.encode x y) hInit hHead hTape
    have final := congrArg Machine.WindowConfig.state (windowOf_run M r t)
    change (r.run rule t).state = (M.windowRun t (windowOf M r)).state at final
    rw [start, M.windowRun_start_state t t (Nat.le_refl _) (A.encode x y)] at final
    exact ⟨y, hy, (M.accepts_iff_at_bound _ (hHalt y hy)).mpr (final.symm.trans hAccept)⟩
  · rintro ⟨y, hy, hAccept⟩
    let start := M.windowStart head (A.encode x y)
    let r : Row (M.State ⊕ Bool) M.Symbol (2 * t + 1) := ⟨start.state, start.head, start.cells⟩
    refine ⟨r, ⟨rfl, rfl, ?_⟩, ?_⟩
    · exact (isInitialCellBlock_iff_exists_certificate A M x capacity head.val r.cells hFit).mpr
        ⟨y, hy, fun _ ↦ rfl⟩
    · have final := congrArg Machine.WindowConfig.state (windowOf_run M r t)
      change (r.run rule t).state = (M.windowRun t start).state at final
      rw [M.windowRun_start_state t t (Nat.le_refl _) (A.encode x y)] at final
      exact final.trans ((M.accepts_iff_at_bound _ (hHalt y hy)).mp hAccept)

/-- Initial constraints use two unit clauses, one clause per cell, and at most
one padding clause per pair of cells. -/
def initialSizeBound (width certificates : Nat) : Nat :=
  4 + width * (certificates + 2) + width * (width * 3)

theorem size_initialClauses_le {width : Nat} (head : Fin width) (x : BinaryWord) (capacity : Nat)
    (certs : List A.Certificate) :
    CNF.size (initialClauses M head x capacity certs) ≤ initialSizeBound width certs.length := by
  simp only [initialClauses, initialSizeBound, CNF.size_append]
  have cellBound (i : Fin width) :
      CNF.size (initialCell M x capacity head.val certs i) ≤ certs.length + 2 := by
    unfold initialCell
    split
    · simp
    · split
      · simp
      · split <;> simp [Nat.add_assoc]
  have gapBound (i j : Fin width) : CNF.size (initialGap M x capacity head.val i j) ≤ 3 := by
    unfold initialGap
    split <;> simp
  have hCells := CNF.size_flatMap_le (List.finRange width) _ _ (fun i _ ↦ cellBound i)
  have hGaps := CNF.size_flatMap_le (List.finRange width)
    (fun i ↦ (List.finRange width).flatMap (initialGap M x capacity head.val i)) (width * 3)
    (fun i _ ↦ by simpa only [List.length_finRange] using
      CNF.size_flatMap_le (List.finRange width) _ 3 (fun j _ ↦ gapBound i j))
  simp only [List.length_finRange] at hCells hGaps
  exact Nat.add_le_add (Nat.add_le_add_left hCells 4) hGaps

/-- Number of literal occurrences and clause delimiters before encoding atom names. -/
def verifierSizeBound (states symbols certificates k d n : Nat) : Nat :=
  let t := horizon n k d
  let width := 2 * t + 1
  initialSizeBound width certificates + traceSizeBound t width states symbols + 2

theorem size_verifierFormula_le [DecidableEq M.State] [DecidableEq M.Symbol]
    (qs : List (M.State ⊕ Bool)) (symbols : List M.Symbol) (certs : List A.Certificate)
    (x : BinaryWord) (k d : Nat) : CNF.size (verifierFormula M qs symbols certs x k d) ≤
      verifierSizeBound qs.length symbols.length certs.length k d x.length := by
  unfold verifierFormula verifierSizeBound
  exact Nat.le_trans (size_acceptingClauses_le ..)
    (Nat.add_le_add_right (Nat.add_le_add_right (size_initialClauses_le M ..) _) 2)

theorem horizon_polynomiallyBounded (k d : Nat) : PolynomiallyBounded (fun n ↦ horizon n k d) := by
  let hInput : PolynomiallyBounded (fun n ↦ inputBound n k) :=
    (PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)).add (PolynomiallyBounded.id.pow k)
  exact ((hInput.pow d).add (PolynomiallyBounded.const d)).add hInput

theorem verifierSizeBound_polynomiallyBounded (states symbols certificates k d : Nat) :
    PolynomiallyBounded (verifierSizeBound states symbols certificates k d) := by
  have ht := horizon_polynomiallyBounded k d
  have hw := ((PolynomiallyBounded.const 2).mul ht).add (PolynomiallyBounded.const 1)
  have hHot {f : Nat → Nat} (hf : PolynomiallyBounded f) :
      PolynomiallyBounded (fun n ↦ oneHotSize (f n)) :=
    (hf.add (PolynomiallyBounded.const 1)).add ((PolynomiallyBounded.const 3).mul (hf.pow 2))
  have hInitial := ((PolynomiallyBounded.const 4).add
    (hw.mul (PolynomiallyBounded.const (certificates + 2)))).add
    (hw.mul (hw.mul (PolynomiallyBounded.const 3)))
  have hRow := ((PolynomiallyBounded.const (oneHotSize states)).add (hHot hw)).add
    (hw.mul (PolynomiallyBounded.const (oneHotSize symbols)))
  have hStep := ((PolynomiallyBounded.const states).mul
    (hw.mul (PolynomiallyBounded.const (symbols * 15)))).add
    (hw.mul (hw.mul (PolynomiallyBounded.const (symbols * 4))))
  have hTrace := ((ht.add (PolynomiallyBounded.const 1)).mul hRow).add (ht.mul hStep)
  exact (hInitial.add hTrace).add (PolynomiallyBounded.const 2)

end PvsNP.CookLevin
