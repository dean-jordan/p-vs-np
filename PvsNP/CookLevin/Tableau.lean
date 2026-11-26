module

public import PvsNP.SAT.CNF

/-! # CNF constraints for a bounded computation

Each row describes a control state, a head position, and the contents of the
finite tape window. The clauses force one value in each field and impose a
single table transition between consecutive rows.
-/

@[expose] public section

namespace PvsNP.Tableau

variable {Q Γ : Type} {width : Nat}

/-- A deterministic rule reads the old state, head, and symbol. It specifies
the new state and head, and the symbol to write at the old head. -/
abbrev Rule (Q Γ : Type) (width : Nat) :=
  Q → Fin width → Γ → Q × Fin width × Γ

structure Row (Q Γ : Type) (width : Nat) where
  state : Q
  head : Fin width
  cells : Fin width → Γ

theorem Row.eq_of_fields {r s : Row Q Γ width} (hq : r.state = s.state)
    (hi : r.head = s.head) (ha : ∀ i, r.cells i = s.cells i) : r = s := by
  have hCells := funext ha
  cases r
  cases s
  simp_all

/-- Update every component of a row according to the table rule. -/
def Row.step (rule : Rule Q Γ width) (row : Row Q Γ width) : Row Q Γ width :=
  let next := rule row.state row.head (row.cells row.head)
  ⟨next.1, next.2.1, fun i ↦ if i = row.head then next.2.2 else row.cells i⟩

/-- Clock values past the time horizon can be used to define a total assignment. -/
def Row.run (rule : Rule Q Γ width) (start : Row Q Γ width) : Nat → Row Q Γ width
  | 0 => start
  | t + 1 => (run rule start t).step rule

/-- Each variable asserts a value of one field at a given clock tick. -/
inductive Atom (Q Γ : Type) (width : Nat) where
  | state (time : Nat) (q : Q)
  | head (time : Nat) (i : Fin width)
  | cell (time : Nat) (i : Fin width) (a : Γ)
  deriving DecidableEq

/-- An assignment encodes a row when its true atoms select exactly its field values. -/
def EncodesRow (σ : Atom Q Γ width → Bool) (t : Nat) (row : Row Q Γ width) : Prop :=
  (∀ q, σ (.state t q) = true ↔ row.state = q) ∧
  (∀ i, σ (.head t i) = true ↔ row.head = i) ∧
  (∀ i a, σ (.cell t i a) = true ↔ row.cells i = a)

/-- The assignment determined by a sequence of concrete rows. -/
def assignmentOf [DecidableEq Q] [DecidableEq Γ] (rows : Nat → Row Q Γ width) :
    Atom Q Γ width → Bool
  | .state t q => decide ((rows t).state = q)
  | .head t i => decide ((rows t).head = i)
  | .cell t i a => decide ((rows t).cells i = a)

theorem assignmentOf_encodes [DecidableEq Q] [DecidableEq Γ]
    (rows : Nat → Row Q Γ width) (t : Nat) : EncodesRow (assignmentOf rows) t (rows t) := by
  simp [EncodesRow, assignmentOf]

theorem EncodesRow.unique {σ : Atom Q Γ width → Bool} {t : Nat} {r s : Row Q Γ width}
    (hr : EncodesRow σ t r) (hs : EncodesRow σ t s) : r = s := by
  have state : r.state = s.state := (hr.1 _).mp ((hs.1 _).mpr rfl)
  have head : r.head = s.head := (hr.2.1 _).mp ((hs.2.1 _).mpr rfl)
  exact Row.eq_of_fields state head fun i ↦ (hr.2.2 i _).mp ((hs.2.2 i _).mpr rfl)

/-- Clauses forcing exactly one field value, using a complete list of candidates. -/
def rowClauses [DecidableEq Q] [DecidableEq Γ] (qs : List Q) (symbols : List Γ) (t : Nat) :
    CNF.Formula (Atom Q Γ width) :=
  CNF.exactlyOne (qs.map (Atom.state t)) ++
  CNF.exactlyOne ((List.finRange width).map (Atom.head t)) ++
  (List.finRange width).flatMap fun i ↦ CNF.exactlyOne (symbols.map (Atom.cell t i))

private theorem sat_oneHot_map_iff {α β : Type} [DecidableEq α] (σ : α → Bool)
    (values : List β) (complete : ∀ b, b ∈ values) (f : β → α) (hf : Function.Injective f) :
    CNF.Sat σ (CNF.exactlyOne (values.map f)) ↔ ∃ a, ∀ b, σ (f b) = true ↔ a = b := by
  rw [CNF.sat_exactlyOne]
  constructor
  · rintro ⟨v, hv, ht, hu⟩
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hv
    refine ⟨a, fun b ↦ ⟨fun h ↦ ?_, fun h ↦ h ▸ ht⟩⟩
    exact (hf (hu (f b) (List.mem_map.mpr ⟨b, complete b, rfl⟩) h)).symm
  · rintro ⟨a, ha⟩
    refine ⟨f a, List.mem_map.mpr ⟨a, complete a, rfl⟩, (ha a).mpr rfl, ?_⟩
    intro v hv ht
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hv
    exact congrArg f ((ha b).mp ht).symm

theorem sat_rowClauses_iff [DecidableEq Q] [DecidableEq Γ] (qs : List Q) (symbols : List Γ)
    (hq : ∀ q, q ∈ qs) (ha : ∀ a, a ∈ symbols) (σ : Atom Q Γ width → Bool) (t : Nat) :
    CNF.Sat σ (rowClauses qs symbols t) ↔ ∃ row, EncodesRow σ t row := by
  have hs := sat_oneHot_map_iff σ qs hq (Atom.state t) (fun _ _ h ↦ (Atom.state.inj h).2)
  have hh := sat_oneHot_map_iff σ (List.finRange width) List.mem_finRange (Atom.head t)
    (fun _ _ h ↦ (Atom.head.inj h).2)
  have hc (i : Fin width) := sat_oneHot_map_iff σ symbols ha (Atom.cell t i)
    (fun _ _ h ↦ (Atom.cell.inj h).2.2)
  simp only [rowClauses, CNF.sat_append, CNF.sat_flatMap, hs, hh, hc]
  constructor
  · rintro ⟨⟨⟨q, hq⟩, ⟨i, hi⟩⟩, cells⟩
    classical
    have hc i := cells i (List.mem_finRange i)
    exact ⟨⟨q, i, fun j ↦ Classical.choose (hc j)⟩, hq, hi, fun j ↦ Classical.choose_spec (hc j)⟩
  · rintro ⟨row, hq', hi', hc'⟩
    exact ⟨⟨⟨row.state, hq'⟩, ⟨row.head, hi'⟩⟩, fun i _ ↦ ⟨row.cells i, hc' i⟩⟩

/-- If a particular state, head, and scanned symbol occur together, the three
new field values must be those specified by the rule. -/
def localUpdate (rule : Rule Q Γ width) (t : Nat) (q : Q) (i : Fin width) (a : Γ) :
    CNF.Formula (Atom Q Γ width) :=
  let next := rule q i a
  CNF.guard [.pos (.state t q), .pos (.head t i), .pos (.cell t i a)]
    [[.pos (.state (t + 1) next.1)], [.pos (.head (t + 1) next.2.1)],
      [.pos (.cell (t + 1) i next.2.2)]]

/-- A cell other than the old head position keeps its symbol. -/
def localCopy (t : Nat) (head cell : Fin width) (a : Γ) : CNF.Formula (Atom Q Γ width) :=
  if head = cell then []
  else CNF.guard [.pos (.head t head), .pos (.cell t cell a)] [[.pos (.cell (t + 1) cell a)]]

/-- One step's clauses enumerate only the rule keys and individual cells. -/
def stepClauses (qs : List Q) (symbols : List Γ) (rule : Rule Q Γ width) (t : Nat) :
    CNF.Formula (Atom Q Γ width) :=
  (qs.flatMap fun q ↦ (List.finRange width).flatMap fun i ↦
    symbols.flatMap (localUpdate rule t q i)) ++
  (List.finRange width).flatMap fun i ↦ (List.finRange width).flatMap fun j ↦
    symbols.flatMap (localCopy t i j)

/-- The shape and step constraints for the computation through time `steps`. -/
def traceClauses [DecidableEq Q] [DecidableEq Γ] (qs : List Q) (symbols : List Γ)
    (rule : Rule Q Γ width) (steps : Nat) : CNF.Formula (Atom Q Γ width) :=
  ((List.range (steps + 1)).flatMap (rowClauses qs symbols)) ++
  ((List.range steps).flatMap (stepClauses qs symbols rule))

private theorem sat_localUpdate_iff (σ : Atom Q Γ width → Bool) (rule : Rule Q Γ width)
    (t : Nat) (q : Q) (i : Fin width) (a : Γ) :
    CNF.Sat σ (localUpdate rule t q i a) ↔
      (σ (.state t q) = true → σ (.head t i) = true → σ (.cell t i a) = true →
        σ (.state (t + 1) (rule q i a).1) = true ∧
        σ (.head (t + 1) (rule q i a).2.1) = true ∧
        σ (.cell (t + 1) i (rule q i a).2.2) = true) := by
  simp [localUpdate, CNF.sat_guard]

private theorem sat_localCopy_iff (σ : Atom Q Γ width → Bool) (t : Nat) (i j : Fin width)
    (a : Γ) (h : i ≠ j) : CNF.Sat σ (localCopy t i j a) ↔
      (σ (.head t i) = true → σ (.cell t j a) = true → σ (.cell (t + 1) j a) = true) := by
  simp [localCopy, h, CNF.sat_guard]

/-- For two already encoded rows, the step clauses are equivalent to executing the rule. -/
theorem sat_stepClauses_iff (qs : List Q) (symbols : List Γ) (rule : Rule Q Γ width)
    (hq : ∀ q, q ∈ qs) (ha : ∀ a, a ∈ symbols) {σ : Atom Q Γ width → Bool} {t : Nat}
    {r s : Row Q Γ width} (hr : EncodesRow σ t r) (hs : EncodesRow σ (t + 1) s) :
    CNF.Sat σ (stepClauses qs symbols rule t) ↔ s = r.step rule := by
  simp only [stepClauses, CNF.sat_append, CNF.sat_flatMap]
  constructor
  · intro ⟨hf, hc⟩
    have update := (sat_localUpdate_iff σ rule t r.state r.head (r.cells r.head)).mp
      (hf r.state (hq _) r.head (List.mem_finRange _) (r.cells r.head) (ha _))
      ((hr.1 _).mpr rfl) ((hr.2.1 _).mpr rfl) ((hr.2.2 _ _).mpr rfl)
    apply Row.eq_of_fields ((hs.1 _).mp update.1) ((hs.2.1 _).mp update.2.1)
    intro j
    by_cases hj : j = r.head
    · subst j
      simpa [Row.step] using (hs.2.2 _ _).mp update.2.2
    · have copy := (sat_localCopy_iff σ t r.head j (r.cells j) (Ne.symm hj)).mp
        (hc r.head (List.mem_finRange _) j (List.mem_finRange _) (r.cells j) (ha _))
        ((hr.2.1 _).mpr rfl) ((hr.2.2 _ _).mpr rfl)
      simpa only [Row.step, ite_eq_right hj] using (hs.2.2 _ _).mp copy
  · rintro rfl
    constructor
    · intro q _ i _ a _
      apply (sat_localUpdate_iff σ rule t q i a).mpr
      intro hq' hi' ha'
      have eqQ := (hr.1 q).mp hq'
      have eqI := (hr.2.1 i).mp hi'
      have eqA := (hr.2.2 i a).mp ha'
      subst q
      subst i
      subst a
      exact ⟨(hs.1 _).mpr rfl, (hs.2.1 _).mpr rfl, (hs.2.2 _ _).mpr (by simp [Row.step])⟩
    · intro i _ j _ a _
      by_cases hij : i = j
      · simp [localCopy, hij, CNF.Sat]
      · apply (sat_localCopy_iff σ t i j a hij).mpr
        intro hi' ha'
        have eqI := (hr.2.1 i).mp hi'
        subst i
        apply (hs.2.2 j a).mpr
        simpa only [Row.step, ite_eq_right (Ne.symm hij)] using (hr.2.2 j a).mp ha'

theorem sat_traceClauses_iff [DecidableEq Q] [DecidableEq Γ] (qs : List Q) (symbols : List Γ)
    (hq : ∀ q, q ∈ qs) (ha : ∀ a, a ∈ symbols) (rule : Rule Q Γ width)
    (steps : Nat) (σ : Atom Q Γ width → Bool) : CNF.Sat σ (traceClauses qs symbols rule steps) ↔
      ∃ rows : Nat → Row Q Γ width,
        (∀ t ≤ steps, EncodesRow σ t (rows t)) ∧ (∀ t < steps, rows (t + 1) = (rows t).step rule) := by
  simp only [traceClauses, CNF.sat_append, CNF.sat_flatMap, List.mem_range, Nat.lt_succ_iff]
  constructor
  · intro ⟨hRows, hSteps⟩
    have getRow t (ht : t ≤ steps) := (sat_rowClauses_iff qs symbols hq ha σ t).mp (hRows t ht)
    classical
    let rows t := if ht : t ≤ steps then Classical.choose (getRow t ht)
      else Classical.choose (getRow 0 (Nat.zero_le _))
    have hRow t (ht : t ≤ steps) : EncodesRow σ t (rows t) := by
      simpa only [rows, dite_eq_left ht] using Classical.choose_spec (getRow t ht)
    refine ⟨rows, hRow, fun t ht ↦ ?_⟩
    exact (sat_stepClauses_iff qs symbols rule hq ha (hRow t (Nat.le_of_lt ht))
      (hRow (t + 1) (Nat.succ_le_of_lt ht))).mp (hSteps t ht)
  · rintro ⟨rows, hRows, hSteps⟩
    refine ⟨fun t ht ↦ (sat_rowClauses_iff qs symbols hq ha σ t).mpr ⟨rows t, hRows t ht⟩, ?_⟩
    intro t ht
    exact (sat_stepClauses_iff qs symbols rule hq ha (hRows t (Nat.le_of_lt ht))
      (hRows (t + 1) (Nat.succ_le_of_lt ht))).mpr (hSteps t ht)

/-- Add the initial constraints and a unit clause requiring the accepting state. -/
def acceptingClauses [DecidableEq Q] [DecidableEq Γ] (qs : List Q) (symbols : List Γ)
    (rule : Rule Q Γ width) (steps : Nat) (accept : Q) (initial : CNF.Formula (Atom Q Γ width)) :
    CNF.Formula (Atom Q Γ width) :=
  initial ++ traceClauses qs symbols rule steps ++ [[.pos (.state steps accept)]]

/-- The generated CNF is satisfiable precisely when a permitted initial row reaches accept. -/
theorem satisfiable_acceptingClauses_iff [DecidableEq Q] [DecidableEq Γ]
    (qs : List Q) (symbols : List Γ) (hq : ∀ q, q ∈ qs) (ha : ∀ a, a ∈ symbols)
    (rule : Rule Q Γ width) (steps : Nat) (accept : Q)
    (initial : CNF.Formula (Atom Q Γ width)) (permitted : Row Q Γ width → Prop)
    (hInit : ∀ σ r, EncodesRow σ 0 r → (CNF.Sat σ initial ↔ permitted r)) :
    CNF.Satisfiable (acceptingClauses qs symbols rule steps accept initial) ↔
      ∃ start, permitted start ∧ (start.run rule steps).state = accept := by
  simp only [CNF.Satisfiable, acceptingClauses, CNF.sat_append,
    sat_traceClauses_iff qs symbols hq ha rule, CNF.sat_unit, CNF.Literal.sat_pos]
  constructor
  · rintro ⟨σ, ⟨hI, ⟨rows, hRows, hSteps⟩⟩, hLast⟩
    have hRun (t : Nat) (ht : t ≤ steps) : rows t = (rows 0).run rule t := by
      induction t with
      | zero => rfl
      | succ t ih =>
        have ht' := Nat.lt_of_succ_le ht
        rw [hSteps t ht', ih (Nat.le_of_lt ht')]
        rfl
    refine ⟨rows 0, (hInit σ _ (hRows 0 (Nat.zero_le _))).mp hI, ?_⟩
    rw [← hRun steps (Nat.le_refl _)]
    exact ((hRows steps (Nat.le_refl _)).1 _).mp hLast
  · rintro ⟨start, hStart, hLast⟩
    let rows := start.run rule
    let σ := assignmentOf rows
    exact ⟨σ, ⟨(hInit σ start (assignmentOf_encodes rows 0)).mpr hStart,
      ⟨rows, fun t _ ↦ assignmentOf_encodes rows t, fun _ _ ↦ rfl⟩⟩,
      ((assignmentOf_encodes rows steps).1 _).mpr hLast⟩

end PvsNP.Tableau
