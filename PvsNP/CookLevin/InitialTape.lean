module

public import PvsNP.Complexity.PairEncoding
public import PvsNP.TuringMachine.Core

/-!
# Initial tape of a bounded-certificate verifier

The instance and separator occupy a fixed prefix. A block of certificate slots
holds the certificate followed by tape blanks, so a single capacity accommodates
every permitted certificate length.
-/

@[expose] public section

namespace PvsNP.TableauInput

/-- A block of certificate slots. `none` represents a tape blank. -/
abbrev Slots (C : Type) (capacity : Nat) := Fin capacity → Option C

/-- A blank slot can only be followed by other blank slots. -/
def NoGaps {C : Type} {capacity : Nat} (slots : Slots C capacity) : Prop :=
  ∀ i j : Fin capacity, i < j → slots i = none → slots j = none

/-- Place the letters of a certificate in the slots, padding with blanks. -/
def ofList {C : Type} (certificate : List C) (capacity : Nat) : Slots C capacity :=
  fun i ↦ certificate[i.val]?

theorem noGaps_ofList {C : Type} (certificate : List C) (capacity : Nat) :
    NoGaps (ofList certificate capacity) := by
  intro i j hij hi
  change certificate[i.val]? = none at hi
  change certificate[j.val]? = none
  exact List.getElem?_eq_none (Nat.le_trans (List.getElem?_eq_none_iff.mp hi) (Nat.le_of_lt hij))

/-- Testing adjacent slots suffices to rule out every gap. -/
theorem noGaps_iff_adjacent {C : Type} {capacity : Nat} (slots : Slots C capacity) :
    NoGaps slots ↔ ∀ i j : Fin capacity, j.val = i.val + 1 → slots i = none → slots j = none := by
  constructor
  · intro h i j hij
    exact h i j (show i.val < j.val by omega)
  · intro h i j hij hi
    have chain : ∀ d (k : Fin capacity), k.val = i.val + d → slots k = none := by
      intro d
      induction d with
      | zero =>
        intro k hk
        have heq : k = i := Fin.ext (by simpa only [Nat.add_zero] using hk)
        exact heq ▸ hi
      | succ d ih =>
        intro k hk
        let prev : Fin capacity := ⟨k.val - 1, by omega⟩
        have hprev : prev.val = i.val + d := by dsimp [prev]; omega
        exact h prev k (by dsimp [prev]; omega) (ih prev hprev)
    exact chain (j.val - i.val) j (by have : i.val < j.val := hij; omega)

/-- A gap-free block is precisely the padding of a certificate that fits. -/
theorem noGaps_iff_exists_list {C : Type} {capacity : Nat} (slots : Slots C capacity) :
    NoGaps slots ↔ ∃ y : List C, y.length ≤ capacity ∧ ofList y capacity = slots := by
  refine ⟨?_, ?_⟩
  · induction capacity with
    | zero => exact fun _ ↦ ⟨[], Nat.le_refl 0, funext (fun i ↦ Fin.elim0 i)⟩
    | succ capacity ih =>
      intro h
      cases h0 : slots 0 with
      | none =>
        refine ⟨[], Nat.zero_le _, funext (fun i ↦ ?_)⟩
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · exact h0.symm
        · exact (h 0 j.succ (show 0 < j.val + 1 by omega) h0).symm
      | some c =>
        let tail : Slots C capacity := fun i ↦ slots i.succ
        have ht : NoGaps tail := fun i j hij ↦ h i.succ j.succ (Fin.succ_lt_succ_iff.mpr hij)
        obtain ⟨y, hy, htail⟩ := ih tail ht
        refine ⟨c :: y, Nat.succ_le_succ hy, funext (fun i ↦ ?_)⟩
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · exact h0.symm
        · exact congrFun htail j
  · rintro ⟨y, _, rfl⟩
    exact noGaps_ofList y capacity

/-- Padded lookup is injective for certificates that fit the capacity. -/
theorem ofList_injective {C : Type} {capacity : Nat} {y z : List C}
    (hy : y.length ≤ capacity) (hz : z.length ≤ capacity)
    (h : ofList y capacity = ofList z capacity) : y = z := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < capacity
  · exact congrFun h ⟨i, hi⟩
  · have hyi : y.length ≤ i := by omega
    have hzi : z.length ≤ i := by omega
    rw [List.getElem?_eq_none hyi, List.getElem?_eq_none hzi]

/-- The fixed prefix of the initial tape, including the separator. -/
def fixedPrefix (A : CheckingAlphabet) (M : Machine A.Symbol) (x : BinaryWord) : List M.Symbol :=
  (A.encode x []).map M.input

@[simp] theorem length_fixedPrefix (A : CheckingAlphabet) (M : Machine A.Symbol) (x : BinaryWord) :
    (fixedPrefix A M x).length = x.length + 1 := by
  simp [fixedPrefix]

/-- Translate a certificate slot to its tape symbol. Padding uses the machine's own blank. -/
def certificateSymbol (A : CheckingAlphabet) (M : Machine A.Symbol) :
    Option A.Certificate → M.Symbol
  | none => M.blank
  | some c => M.input (A.certificate c)

@[simp] theorem certificateSymbol_eq_blank_iff (A : CheckingAlphabet) (M : Machine A.Symbol)
    (slot : Option A.Certificate) : certificateSymbol A M slot = M.blank ↔ slot = none := by
  cases slot <;> simp [certificateSymbol, M.input_ne_blank]

theorem certificateSymbol_injective (A : CheckingAlphabet) (M : Machine A.Symbol) :
    Function.Injective (certificateSymbol A M) := by
  intro a b h
  cases a <;> cases b
  · rfl
  · exact (M.input_ne_blank _ h.symm).elim
  · exact (M.input_ne_blank _ h).elim
  · exact congrArg some (A.certificate.injective (M.input.injective h))

/-- The initial symbol at a nonnegative address, with address zero at the initial head. -/
def atIndex (A : CheckingAlphabet) (M : Machine A.Symbol) (x : BinaryWord)
    {capacity : Nat} (slots : Slots A.Certificate capacity) (i : Nat) : M.Symbol :=
  if i < x.length + 1 then (fixedPrefix A M x)[i]?.getD M.blank
  else if hi : i - (x.length + 1) < capacity then
    certificateSymbol A M (slots ⟨i - (x.length + 1), hi⟩)
  else M.blank

/-- The initial symbol at any absolute address. Cells left of the input start are blank. -/
def atPosition (A : CheckingAlphabet) (M : Machine A.Symbol) (x : BinaryWord)
    {capacity : Nat} (slots : Slots A.Certificate capacity) : Int → M.Symbol
  | .ofNat i => atIndex A M x slots i
  | .negSucc _ => M.blank

theorem atPosition_neg (A : CheckingAlphabet) (M : Machine A.Symbol) (x : BinaryWord)
    {capacity : Nat} (slots : Slots A.Certificate capacity) {i : Int} (hi : i < 0) :
    atPosition A M x slots i = M.blank := by
  cases i with
  | ofNat n => exact (Int.not_lt_of_ge (Int.natCast_nonneg n) hi).elim
  | negSucc n => rfl

theorem atPosition_prefix (A : CheckingAlphabet) (M : Machine A.Symbol) (x : BinaryWord)
    {capacity : Nat} (slots : Slots A.Certificate capacity) {i : Nat} (hi : i < x.length + 1) :
    atPosition A M x slots i = (fixedPrefix A M x)[i]?.getD M.blank := by
  simp [atPosition, atIndex, hi]

theorem atPosition_certificate (A : CheckingAlphabet) (M : Machine A.Symbol) (x : BinaryWord)
    {capacity : Nat} (slots : Slots A.Certificate capacity) (i : Fin capacity) :
    atPosition A M x slots (Int.ofNat (x.length + 1 + i.val)) =
      certificateSymbol A M (slots i) := by
  have h : ¬ x.length + 1 + i.val < x.length + 1 := by omega
  simp [atPosition, atIndex, h, i.isLt]

theorem atPosition_after (A : CheckingAlphabet) (M : Machine A.Symbol) (x : BinaryWord)
    {capacity : Nat} (slots : Slots A.Certificate capacity) {i : Nat}
    (hi : x.length + 1 + capacity ≤ i) : atPosition A M x slots i = M.blank := by
  have hp : ¬ i < x.length + 1 := by omega
  have hc : ¬ i - (x.length + 1) < capacity := by omega
  simp [atPosition, atIndex, hp, hc]

/-- The fixed prefix followed by the certificate uses at most this many cells. -/
theorem length_encode_le_capacity (A : CheckingAlphabet) (x : BinaryWord) (y : List A.Certificate)
    {capacity : Nat} (hy : y.length ≤ capacity) :
    (A.encode x y).length ≤ x.length + 1 + capacity := by
  rw [A.length_encode]
  omega

private theorem input_append (A : CheckingAlphabet) (M : Machine A.Symbol) (x : BinaryWord)
    (y : List A.Certificate) :
    (A.encode x y).map M.input = fixedPrefix A M x ++ y.map (M.input ∘ A.certificate) := by
  simp [fixedPrefix, CheckingAlphabet.encode, List.map_map]

private theorem cert_symbol_eq_getElem {A : CheckingAlphabet} {M : Machine A.Symbol}
    (y : List A.Certificate) (i : Nat) :
    certificateSymbol A M (y[i]?) = ((y.map (M.input ∘ A.certificate))[i]?).getD M.blank := by
  rw [List.getElem?_map]
  cases y[i]? <;> rfl

private theorem atIndex_ofList (A : CheckingAlphabet) (M : Machine A.Symbol) (x : BinaryWord)
    (y : List A.Certificate) {capacity : Nat} (hy : y.length ≤ capacity) (i : Nat) :
    atIndex A M x (ofList y capacity) i = (((A.encode x y).map M.input)[i]?).getD M.blank := by
  rw [input_append]
  by_cases hp : i < x.length + 1
  · have hprefix : i < (fixedPrefix A M x).length := by simpa only [length_fixedPrefix] using hp
    simp only [atIndex, ite_eq_left hp, List.getElem?_append_left hprefix]
  · have hprefix : (fixedPrefix A M x).length ≤ i := by
      simpa only [length_fixedPrefix] using Nat.le_of_not_gt hp
    rw [List.getElem?_append_right hprefix, length_fixedPrefix]
    by_cases hc : i - (x.length + 1) < capacity
    · simpa only [atIndex, ite_eq_right hp, dite_eq_left hc, ofList] using
        cert_symbol_eq_getElem (A := A) (M := M) y (i - (x.length + 1))
    · have hcert : (y.map (M.input ∘ A.certificate)).length ≤ i - (x.length + 1) := by
        rw [List.length_map]
        exact Nat.le_trans hy (Nat.le_of_not_gt hc)
      simp only [atIndex, ite_eq_right hp, dite_eq_right hc, List.getElem?_eq_none hcert,
        Option.getD_none]

/-- Padded certificate slots give exactly Cook's initial tape at every address. -/
theorem atPosition_ofList_eq_start (A : CheckingAlphabet) (M : Machine A.Symbol) (x : BinaryWord)
    (y : List A.Certificate) {capacity : Nat} (hy : y.length ≤ capacity) (i : Int) :
    atPosition A M x (ofList y capacity) i =
      @Turing.Tape.nth _ M.tapeInhabited (M.start (A.encode x y)).tape i := by
  let := M.tapeInhabited
  cases i with
  | ofNat i =>
    rw [atPosition, atIndex_ofList A M x y hy i]
    change _ = @Turing.Tape.nth _ M.tapeInhabited
      (Turing.Tape.mk' (Turing.ListBlank.mk [])
        (Turing.ListBlank.mk ((A.encode x y).map M.input))) i
    rw [Turing.Tape.mk'_nth_nat, Turing.ListBlank.nth_mk, List.getI_eq_getElem?_getD]
    rfl
  | negSucc _ => rfl

/-- Local constraints for an initial row. `offset` is the cell at the initial tape head. -/
def IsInitialCellBlock (A : CheckingAlphabet) (M : Machine A.Symbol) (x : BinaryWord)
    (capacity offset : Nat) {width : Nat} (cells : Fin width → M.Symbol) : Prop :=
  let first := offset + x.length + 1
  (∀ i, i.val < offset → cells i = M.blank) ∧
  (∀ i, offset ≤ i.val → i.val < first →
    cells i = (fixedPrefix A M x)[i.val - offset]?.getD M.blank) ∧
  (∀ i, first ≤ i.val → i.val < first + capacity →
    ∃ slot, cells i = certificateSymbol A M slot) ∧
  (∀ i j, j.val = i.val + 1 → first ≤ i.val → j.val < first + capacity →
    cells i = M.blank → cells j = M.blank) ∧
  (∀ i, first + capacity ≤ i.val → cells i = M.blank)

private theorem atPosition_block_prefix (A : CheckingAlphabet) (M : Machine A.Symbol)
    (x : BinaryWord) {capacity : Nat} (slots : Slots A.Certificate capacity)
    {offset i : Nat} (hlo : offset ≤ i) (hhi : i < offset + x.length + 1) :
    atPosition A M x slots ((i : Int) - (offset : Int)) =
      (fixedPrefix A M x)[i - offset]?.getD M.blank := by
  have hi : (i : Int) - (offset : Int) = ((i - offset : Nat) : Int) := by omega
  rw [hi]
  exact atPosition_prefix A M x slots (by omega)

private theorem atPosition_block_certificate (A : CheckingAlphabet) (M : Machine A.Symbol)
    (x : BinaryWord) {capacity : Nat} (slots : Slots A.Certificate capacity)
    {offset i : Nat} (hlo : offset + x.length + 1 ≤ i)
    (hhi : i < offset + x.length + 1 + capacity) :
    atPosition A M x slots ((i : Int) - (offset : Int)) =
      certificateSymbol A M (slots ⟨i - (offset + x.length + 1), by omega⟩) := by
  have hi : (i : Int) - (offset : Int) =
      ((x.length + 1 + (i - (offset + x.length + 1)) : Nat) : Int) := by omega
  rw [hi]
  exact atPosition_certificate A M x slots ⟨i - (offset + x.length + 1), by omega⟩

private theorem atPosition_block_after (A : CheckingAlphabet) (M : Machine A.Symbol)
    (x : BinaryWord) {capacity : Nat} (slots : Slots A.Certificate capacity)
    {offset i : Nat} (hi : offset + x.length + 1 + capacity ≤ i) :
    atPosition A M x slots ((i : Int) - (offset : Int)) = M.blank := by
  have haddr : (i : Int) - (offset : Int) = ((i - offset : Nat) : Int) := by omega
  rw [haddr]
  exact atPosition_after A M x slots (by omega)

/-- A correctly formed row over a window containing the entire input block is exactly the
initial tape of some certificate within the capacity. -/
theorem isInitialCellBlock_iff_exists_certificate (A : CheckingAlphabet) (M : Machine A.Symbol)
    (x : BinaryWord) (capacity offset : Nat) {width : Nat} (cells : Fin width → M.Symbol)
    (hfit : offset + x.length + 1 + capacity ≤ width) :
    IsInitialCellBlock A M x capacity offset cells ↔
      ∃ y : List A.Certificate, y.length ≤ capacity ∧
        ∀ i : Fin width, cells i = @Turing.Tape.nth _ M.tapeInhabited
          (M.start (A.encode x y)).tape ((i.val : Int) - (offset : Int)) := by
  let first := offset + x.length + 1
  constructor
  · rintro ⟨hleft, hprefix, hblock, hadj, hright⟩
    let toCell (j : Fin capacity) : Fin width := ⟨first + j.val, by dsimp [first]; omega⟩
    have hslot (j : Fin capacity) : ∃ slot, cells (toCell j) = certificateSymbol A M slot :=
      hblock (toCell j) (Nat.le_add_right ..) (Nat.add_lt_add_left j.isLt first)
    let slots : Slots A.Certificate capacity := fun j ↦ (hslot j).choose
    have hread (j : Fin capacity) : cells (toCell j) = certificateSymbol A M (slots j) :=
      (hslot j).choose_spec
    have hgap : NoGaps slots := (noGaps_iff_adjacent slots).mpr fun i j hij hi ↦ by
      apply (certificateSymbol_eq_blank_iff A M (slots j)).mp
      have hblank := (hread i).trans ((certificateSymbol_eq_blank_iff A M (slots i)).mpr hi)
      refine (hread j).symm.trans (hadj (toCell i) (toCell j) ?_ ?_ ?_ hblank)
      · dsimp [toCell]; omega
      · exact Nat.le_add_right ..
      · exact Nat.add_lt_add_left j.isLt first
    obtain ⟨y, hy, hslots⟩ := (noGaps_iff_exists_list slots).mp hgap
    refine ⟨y, hy, fun i ↦ ?_⟩
    rw [← atPosition_ofList_eq_start A M x y hy, hslots]
    by_cases hbefore : i.val < offset
    · exact (hleft _ hbefore).trans ((atPosition_neg A M x slots (by omega)).symm)
    · have hfrom : offset ≤ i.val := Nat.le_of_not_gt hbefore
      by_cases hpart : i.val < first
      · exact (hprefix _ hfrom hpart).trans (atPosition_block_prefix A M x slots hfrom hpart).symm
      · have hfromCert : first ≤ i.val := Nat.le_of_not_gt hpart
        by_cases hins : i.val < first + capacity
        · let j : Fin capacity := ⟨i.val - first, by omega⟩
          have hcell : toCell j = i := Fin.ext (by dsimp [toCell, j]; omega)
          calc
            cells i = cells (toCell j) := congrArg cells hcell.symm
            _ = certificateSymbol A M (slots j) := hread j
            _ = _ := (atPosition_block_certificate A M x slots hfromCert hins).symm
        · have hafter : first + capacity ≤ i.val := Nat.le_of_not_gt hins
          exact (hright _ hafter).trans (atPosition_block_after A M x slots hafter).symm
  · rintro ⟨y, hy, htape⟩
    let slots := ofList y capacity
    have hread (i : Fin width) :
        cells i = atPosition A M x slots ((i.val : Int) - (offset : Int)) :=
      (htape i).trans (atPosition_ofList_eq_start A M x y hy _).symm
    have hcert (i : Fin width) (hlo : first ≤ i.val) (hhi : i.val < first + capacity) :
        cells i = certificateSymbol A M (slots ⟨i.val - first, by omega⟩) :=
      (hread i).trans (atPosition_block_certificate A M x slots hlo hhi)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      exact (hread i).trans (atPosition_neg A M x slots (by omega))
    · intro i hlo hhi
      exact (hread i).trans (atPosition_block_prefix A M x slots hlo hhi)
    · intro i hlo hhi
      exact ⟨_, hcert i hlo hhi⟩
    · intro i j hij hli hhj hi
      have hhi : i.val < first + capacity := by omega
      have hlj : first ≤ j.val := by omega
      let si : Fin capacity := ⟨i.val - first, by omega⟩
      let sj : Fin capacity := ⟨j.val - first, by omega⟩
      have hblank : slots si = none :=
        (certificateSymbol_eq_blank_iff A M _).mp ((hcert i hli hhi).symm.trans hi)
      have hj : slots sj = none :=
        noGaps_ofList y capacity si sj (show si.val < sj.val by dsimp [si, sj]; omega) hblank
      exact (hcert j hlj hhj).trans ((certificateSymbol_eq_blank_iff A M _).mpr hj)
    · intro i hi
      exact (hread i).trans (atPosition_block_after A M x slots hi)

end PvsNP.TableauInput
