module

public import PvsNP.SAT.BinaryLanguage
public import PvsNP.CookLevin.VerifierTableau
public import PvsNP.Complexity.Reductions
public import PvsNP.CookLevin.VariableNames

import Mathlib.Basic.Finite.Sum

/-! # Binary encoding of the verifier tableau

This module proves a satisfiability-preserving map with polynomially bounded
output length. A time bound for a Cook machine producing that output is a
separate obligation.
-/

@[expose] public section

namespace PvsNP.CookLevin

open Tableau

variable {A : CheckingAlphabet} (M : Machine A.Symbol)
variable {qCount symbolCount : Nat}

/-- The Boolean tableau represented as a binary CNF word using dense atom names. -/
def binaryVerifierMap [DecidableEq M.State] [DecidableEq M.Symbol]
    (qIndex : (M.State ⊕ Bool) ↪ Fin qCount) (symbolIndex : M.Symbol ↪ Fin symbolCount)
    (qs : List (M.State ⊕ Bool)) (symbols : List M.Symbol) (certs : List A.Certificate)
    (x : BinaryWord) (k d : Nat) : BinaryWord :=
  CNFCode.encode (CNF.mapAtoms (Atom.name qIndex symbolIndex)
    (verifierFormula M qs symbols certs x k d))

theorem binaryVerifierMap_mem_iff [DecidableEq M.State] [DecidableEq M.Symbol]
    (qIndex : (M.State ⊕ Bool) ↪ Fin qCount) (symbolIndex : M.Symbol ↪ Fin symbolCount)
    (qs : List (M.State ⊕ Bool)) (symbols : List M.Symbol) (certs : List A.Certificate)
    (hq : ∀ q, q ∈ qs) (hs : ∀ a, a ∈ symbols) (hc : ∀ c, c ∈ certs)
    (x : BinaryWord) (k d : Nat) (hTime : ∀ z, M.HaltsWithin z (z.length ^ d + d)) :
    binaryVerifierMap M qIndex symbolIndex qs symbols certs x k d ∈ CNFSAT ↔
      ∃ y : List A.Certificate, y.length ≤ x.length ^ k ∧ M.Accepts (A.encode x y) := by
  unfold binaryVerifierMap
  exact (encode_mem_CNFSAT_iff _).trans
    ((CNF.satisfiable_mapAtoms_iff _ (Atom.name_injective qIndex symbolIndex) _).trans
      (satisfiable_verifierFormula_iff M qs symbols certs hq hs hc x k d hTime))

/-- A uniform bound for the binary encoding, including its unary atom names. -/
def binarySizeBound (qCount symbolCount states symbols certificates k d n : Nat) : Nat :=
  let t := horizon n k d
  let names := (t + 1) * atomStride qCount (2 * t + 1) symbolCount
  1 + (names + 3) * verifierSizeBound states symbols certificates k d n

theorem binarySizeBound_polynomiallyBounded
    (qCount symbolCount states symbols certificates k d : Nat) :
    PolynomiallyBounded (binarySizeBound qCount symbolCount states symbols certificates k d) := by
  have ht := horizon_polynomiallyBounded k d
  have hw := ((PolynomiallyBounded.const 2).mul ht).add (PolynomiallyBounded.const 1)
  have stride := ((PolynomiallyBounded.const qCount).add hw).add
    (hw.mul (PolynomiallyBounded.const symbolCount))
  have names := (ht.add (PolynomiallyBounded.const 1)).mul stride
  exact (PolynomiallyBounded.const 1).add ((names.add (PolynomiallyBounded.const 3)).mul
    (verifierSizeBound_polynomiallyBounded states symbols certificates k d))

private theorem initialClauses_timeBounded {width : Nat} (head : Fin width) (x : BinaryWord)
    (capacity : Nat) (certs : List A.Certificate) :
    TimeBounded 0 (initialClauses M head x capacity certs) := by
  intro c hc l hl
  simp only [initialClauses, List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with ((rfl | rfl) | ⟨i, _, hCell⟩) | ⟨i, _, j, _, hGap⟩
  · obtain rfl := List.mem_singleton.mp hl
    exact Nat.le_refl 0
  · obtain rfl := List.mem_singleton.mp hl
    exact Nat.le_refl 0
  · unfold initialCell at hCell
    split at hCell
    · obtain rfl := List.mem_singleton.mp hCell
      obtain rfl := List.mem_singleton.mp hl
      exact Nat.le_refl 0
    · split at hCell
      · obtain rfl := List.mem_singleton.mp hCell
        obtain rfl := List.mem_singleton.mp hl
        exact Nat.le_refl 0
      · split at hCell
        · obtain rfl := List.mem_singleton.mp hCell
          rcases (List.mem_cons.mp hl) with rfl | hLit
          · exact Nat.le_refl 0
          · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hLit
            exact Nat.le_refl 0
        · obtain rfl := List.mem_singleton.mp hCell
          obtain rfl := List.mem_singleton.mp hl
          exact Nat.le_refl 0
  · unfold initialGap at hGap
    split at hGap
    · obtain rfl := List.mem_singleton.mp hGap
      rcases List.mem_cons.mp hl with rfl | hLit
      · exact Nat.le_refl 0
      · obtain rfl := List.mem_singleton.mp hLit
        exact Nat.le_refl 0
    · exact (List.not_mem_nil hGap).elim

private theorem literalIndex_eq_atom (l : CNF.Literal Nat) : CNFCode.literalIndex l = l.atom := by
  cases l <;> rfl

theorem length_binaryVerifierMap_le [DecidableEq M.State] [DecidableEq M.Symbol]
    (qIndex : (M.State ⊕ Bool) ↪ Fin qCount) (symbolIndex : M.Symbol ↪ Fin symbolCount)
    (qs : List (M.State ⊕ Bool)) (symbols : List M.Symbol) (certs : List A.Certificate)
    (x : BinaryWord) (k d : Nat) :
    (binaryVerifierMap M qIndex symbolIndex qs symbols certs x k d).length ≤
      binarySizeBound qCount symbolCount qs.length symbols.length certs.length k d x.length := by
  let t := horizon x.length k d
  let width := 2 * t + 1
  let bound := (t + 1) * atomStride qCount width symbolCount
  let F := verifierFormula M qs symbols certs x k d
  let name : Var M width → Nat := Atom.name qIndex symbolIndex
  have hInitial := initialClauses_timeBounded M (Machine.windowCenter t) x (x.length ^ k) certs
  have hTime : TimeBounded t F := timeBounded_acceptingClauses qs symbols
    (M.windowAdvance width) t (.inr true) _ (hInitial.mono (Nat.zero_le _))
  have hNamed (c : CNF.Clause Nat) (hc : c ∈ CNF.mapAtoms name F) (l : CNF.Literal Nat)
      (hl : l ∈ c) : CNFCode.literalIndex l ≤ bound := by
    rw [literalIndex_eq_atom]
    exact Nat.le_of_lt (hTime.names_lt qIndex symbolIndex c hc l hl)
  have hSize := CNFCode.length_encode_le (CNF.mapAtoms name F) bound hNamed
  rw [CNF.size_mapAtoms] at hSize
  exact Nat.le_trans hSize (Nat.add_le_add_left
    (Nat.mul_le_mul_left (bound + 3) (size_verifierFormula_le M qs symbols certs x k d)) 1)

/-- List a finite alphabet in its chosen index order. -/
def enumerate {α : Type} {n : Nat} (e : α ≃ Fin n) : List α :=
  (List.finRange n).map e.symm

private theorem mem_enumerate {α : Type} {n : Nat} (e : α ≃ Fin n) (a : α) : a ∈ enumerate e :=
  List.mem_map.mpr ⟨e a, List.mem_finRange _, e.symm_apply_apply a⟩

private theorem verifier_tableau_data {L : BinaryLanguage} (hL : L ∈ NP) :
    ∃ (A : CheckingAlphabet) (M : Machine A.Symbol) (k d q s c : Nat)
      (_ : M.State ⊕ Bool ≃ Fin q) (_ : M.Symbol ≃ Fin s) (_ : A.Certificate ≃ Fin c),
      (∀ z, M.HaltsWithin z (z.length ^ d + d)) ∧
        ∀ x, x ∈ L ↔ ∃ y, y.length ≤ x.length ^ k ∧ M.Accepts (A.encode x y) := by
  obtain ⟨A, M, k, ⟨d, hTime⟩, _, hmem⟩ := (mem_NP_iff_exists_verifier L).mp hL
  let _ : Finite M.State := M.stateFinite
  let _ : Finite M.Symbol := M.symbolFinite
  let _ : Finite A.Certificate := A.certificateFinite
  obtain ⟨q, ⟨qIndex⟩⟩ := Finite.exists_equiv_fin (M.State ⊕ Bool)
  obtain ⟨s, ⟨sIndex⟩⟩ := Finite.exists_equiv_fin M.Symbol
  obtain ⟨c, ⟨cIndex⟩⟩ := Finite.exists_equiv_fin A.Certificate
  exact ⟨A, M, k, d, q, s, c, qIndex, sIndex, cIndex, hTime, hmem⟩

/-- Each NP language maps to the binary CNF language with correct membership
and polynomial output length. -/
theorem mem_NP_has_binaryCNF_map {L : BinaryLanguage} (hL : L ∈ NP) :
    ∃ f : BinaryWord → BinaryWord, (∀ x, x ∈ L ↔ f x ∈ CNFSAT) ∧
      ∃ bound : Nat → Nat, PolynomiallyBounded bound ∧ ∀ x, (f x).length ≤ bound x.length := by
  classical
  obtain ⟨A, M, k, d, q, s, _, qIndex, sIndex, cIndex, hTime, hmem⟩ := verifier_tableau_data hL
  let qs := enumerate qIndex
  let syms := enumerate sIndex
  let certs := enumerate cIndex
  let f x := binaryVerifierMap M qIndex.toEmbedding sIndex.toEmbedding qs syms certs x k d
  refine ⟨f, ?_, binarySizeBound q s qs.length syms.length certs.length k d,
    binarySizeBound_polynomiallyBounded q s qs.length syms.length certs.length k d, ?_⟩
  · intro x
    exact (hmem x).trans (binaryVerifierMap_mem_iff M qIndex.toEmbedding sIndex.toEmbedding
      qs syms certs (mem_enumerate qIndex) (mem_enumerate sIndex) (mem_enumerate cIndex)
      x k d hTime).symm
  · intro x
    exact length_binaryVerifierMap_le M qIndex.toEmbedding sIndex.toEmbedding qs syms certs x k d

/-- The machine-generation obligation for the checked tableau map. The finite
transition table and its enumerations are fixed when constructing the transducer. -/
def BinaryTableauxPolyTime : Prop :=
  ∀ (A : CheckingAlphabet) (M : Machine A.Symbol) (k d q s c : Nat)
    [DecidableEq M.State] [DecidableEq M.Symbol]
    (qIndex : M.State ⊕ Bool ≃ Fin q) (sIndex : M.Symbol ≃ Fin s)
    (cIndex : A.Certificate ≃ Fin c),
    PolynomialTimeMap (fun x ↦ binaryVerifierMap M qIndex.toEmbedding sIndex.toEmbedding
      (enumerate qIndex) (enumerate sIndex) (enumerate cIndex) x k d)

theorem mem_NP_reduces_to_CNFSAT {L : BinaryLanguage} (hCompile : BinaryTableauxPolyTime)
    (hL : L ∈ NP) : PolynomiallyReducesTo L CNFSAT := by
  classical
  obtain ⟨A, M, k, d, q, s, c, qIndex, sIndex, cIndex, hTime, hmem⟩ := verifier_tableau_data hL
  refine ⟨_, hCompile A M k d q s c qIndex sIndex cIndex, fun x ↦ ?_⟩
  exact (hmem x).trans (binaryVerifierMap_mem_iff M qIndex.toEmbedding sIndex.toEmbedding
    (enumerate qIndex) (enumerate sIndex) (enumerate cIndex)
    (mem_enumerate qIndex) (mem_enumerate sIndex) (mem_enumerate cIndex) x k d hTime).symm

end PvsNP.CookLevin
