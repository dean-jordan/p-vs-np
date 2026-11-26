module

public import PvsNP.Complexity.PairEncoding
public import PvsNP.SAT.AssignmentQueryTree

import Init.Data.List.Nat.Pairwise

/-! # Executable Boolean truth tables -/

public section

namespace PvsNP.Circuits

open AssignmentQueryTree
  (allAssignments length_allAssignments mem_allAssignments nodup_allAssignments)

private def assignmentWords (n : Nat) : List BinaryWord := (allAssignments n).map List.ofFn

/-- Evaluate a Boolean function on the ordered enumeration of its inputs. -/
@[expose] def truthTable (n : Nat) (f : (Fin n → Bool) → Bool) : BinaryWord :=
  (allAssignments n).map f

/-- Read the table entry indexed by the input word. Missing entries default to false. -/
def tableLookup (n : Nat) (table word : BinaryWord) : Bool :=
  (table[(assignmentWords n).idxOf word]?).getD false

/-- Enumerate all binary truth tables of the given arity. -/
def allTruthTables (n : Nat) : List BinaryWord := assignmentWords (2 ^ n)

@[simp] theorem length_truthTable (n : Nat) (f : (Fin n → Bool) → Bool) :
    (truthTable n f).length = 2 ^ n := by
  simp only [truthTable, List.length_map, length_allAssignments]

private theorem wordOfFn_injective (n : Nat) :
    Function.Injective (List.ofFn : (Fin n → Bool) → BinaryWord) := by
  intro f g eq
  funext i
  simpa only [List.getElem?_ofFn, dite_eq_left i.isLt, Option.some.injEq] using
    congrArg (fun word : BinaryWord ↦ word[i.val]?) eq

private theorem assignmentWords_nodup (n : Nat) : (assignmentWords n).Nodup := by
  apply List.Pairwise.map _ ?_ (nodup_allAssignments n)
  intro f g h eq
  exact h (wordOfFn_injective n eq)

private theorem idxOf_assignmentWords_at (n i : Nat) (hi : i < (allAssignments n).length) :
    (assignmentWords n).idxOf (List.ofFn ((allAssignments n)[i]'hi)) = i := by
  have hj : i < (assignmentWords n).length := by
    simpa only [assignmentWords, List.length_map] using hi
  simpa only [assignmentWords, List.getElem_map] using (assignmentWords_nodup n).idxOf_getElem i hj

/-- Reading each assignment from a full-size table reconstructs the original table. -/
theorem truthTable_tableLookup (n : Nat) (table : BinaryWord) (h : table.length = 2 ^ n) :
    truthTable n (fun x ↦ tableLookup n table (List.ofFn x)) = table := by
  apply List.ext_getElem
  · rw [length_truthTable, h]
  · intro i hi hj
    have hIndex : i < (allAssignments n).length := by
      simpa only [truthTable, List.length_map] using hi
    simp only [truthTable, List.getElem_map, tableLookup, idxOf_assignmentWords_at n i hIndex,
      List.getElem?_eq_getElem hj, Option.getD_some]

/-- Looking up the truth table of a function gives its value on that input. -/
theorem tableLookup_truthTable (n : Nat) (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    tableLookup n (truthTable n f) (List.ofFn x) = f x := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp (mem_allAssignments x)
  have hIndex : i < ((allAssignments n).map f).length := by
    simpa only [List.length_map] using hi
  simp only [tableLookup, idxOf_assignmentWords_at n i hi, List.getElem?_eq_getElem hIndex,
    Option.getD_some, truthTable, List.getElem_map]

@[simp] theorem allTruthTables_length (n : Nat) : (allTruthTables n).length = 2 ^ (2 ^ n) := by
  simp only [allTruthTables, assignmentWords, List.length_map, length_allAssignments]

theorem allTruthTables_nodup (n : Nat) : (allTruthTables n).Nodup :=
  assignmentWords_nodup (2 ^ n)

theorem mem_allTruthTables_iff {n : Nat} {table : BinaryWord} :
    table ∈ allTruthTables n ↔ table.length = 2 ^ n := by
  constructor
  · intro h
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp h
    exact List.length_ofFn
  · intro h
    let f (i : Fin (2 ^ n)) : Bool := table[i.val]'(by simpa only [h] using i.isLt)
    have hTable : List.ofFn f = table := by
      apply List.ext_getElem
      · simp only [List.length_ofFn, h]
      · intro _ _ _
        simp only [List.getElem_ofFn, f]
    exact hTable ▸ List.mem_map_of_mem (mem_allAssignments f)

theorem length_of_mem_allTruthTables {n : Nat} {table : BinaryWord}
    (h : table ∈ allTruthTables n) : table.length = 2 ^ n := mem_allTruthTables_iff.mp h

end PvsNP.Circuits
