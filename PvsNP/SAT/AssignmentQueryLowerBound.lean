module

public import PvsNP.SAT.AssignmentQueryFamily
public import PvsNP.SAT.AssignmentQueryTree

/-! # A query lower bound for SAT with length and variable names visible -/

public section

namespace PvsNP.AssignmentQueryFamily

open CNFCode (encode occurringIndices)

/-- A tree may depend on the binary input length and the ordered list of distinct names.
For inputs sharing those data, it receives formula information through complete assignment
checks. This profile contains the dense names `0, …, k`. -/
def DecidesOnProfile {k : Nat} (tree : AssignmentQueryTree (Fin (k + 1) → Bool))
    (length : Nat) (indices : List Nat) : Prop :=
  ∀ F : CNF.Formula Nat, (encode F).length = length → occurringIndices F = indices →
    (tree.run (fun assignment ↦ SATAssignment.checkWord (encode F) (assignmentWord assignment)) =
      true ↔ encode F ∈ CNFSAT)

/-- Trying every assignment gives a correct tree for this profile. -/
theorem firstSuccess_decidesOnProfile (k : Nat) :
    DecidesOnProfile (AssignmentQueryTree.firstSuccess (AssignmentQueryTree.allAssignments (k + 1)))
      (impossibleWord k).length (occurringIndices (AssignmentSearch.unsatFamily k)) := by
  intro F _ hIndices
  rw [AssignmentQueryTree.run_firstSuccess_eq_true_iff, encode_mem_CNFSAT_iff]
  constructor
  · rintro ⟨u, _, hu⟩
    exact ⟨SATAssignment.lookup (assignmentWord u), by
      simpa only [SATAssignment.checkWord, CNFCode.decode_encode,
        SATAssignment.checkFormula_eq_true_iff] using hu⟩
  · rintro ⟨σ, hSat⟩
    let u : Fin (k + 1) → Bool := fun i ↦ σ i.val
    refine ⟨u, AssignmentQueryTree.mem_allAssignments u, ?_⟩
    simp only [SATAssignment.checkWord, CNFCode.decode_encode,
      SATAssignment.checkFormula_eq_true_iff]
    refine (SATAssignment.sat_congr_on_occurringIndices F ?_).mp hSat
    intro i hi
    rw [hIndices] at hi
    have hRange := (AssignmentSearch.unsatFamily_occurs_iff k i).mp
      (CNFCode.mem_occurringIndices_iff.mp hi)
    exact (lookup_assignmentWord u ⟨i, hRange⟩).symm

/-- Even adaptive checking visits every assignment on the contradictory input with this
profile. Each alternative formula is satisfiable by exactly one of the tested assignments. -/
theorem pow_two_le_queries_of_decidesOnProfile {k : Nat}
    (tree : AssignmentQueryTree (Fin (k + 1) → Bool))
    (hDecides : DecidesOnProfile tree (impossibleWord k).length
      (occurringIndices (AssignmentSearch.unsatFamily k))) :
    2 ^ (k + 1) ≤ tree.falseQueries.length := by
  have hImpossible := hDecides (AssignmentSearch.unsatFamily k) rfl rfl
  have hReject : tree.run (fun _ ↦ false) = false := by
    have hOracle : (fun assignment ↦ SATAssignment.checkWord (impossibleWord k)
        (assignmentWord assignment)) = (fun _ ↦ false) :=
      funext (checkWord_impossibleWord k)
    rw [← hOracle]
    exact Bool.eq_false_iff.mpr (fun h ↦ impossibleWord_not_mem_CNFSAT k (hImpossible.mp h))
  refine tree.pow_two_le_falseQueries_length
    (fun σ assignment ↦ SATAssignment.checkWord (uniqueWord σ) (assignmentWord assignment))
    checkWord_uniqueWord_eq_true_iff hReject ?_
  intro σ
  exact (hDecides (uniqueFormula σ) (uniqueWord_length_eq_impossibleWord_length σ)
    (occurringIndices_uniqueFormula_eq_unsatFamily σ)).mpr (uniqueWord_mem_CNFSAT σ)

/-- No polynomial in the encoded bit length bounds the false paths of a correct family
of these adaptive query trees, even if each tree is chosen separately for its profile. -/
theorem no_polynomial_bound_for_adaptive_assignment_queries
    (tree : (k : Nat) → AssignmentQueryTree (Fin (k + 1) → Bool))
    (hDecides : ∀ k, DecidesOnProfile (tree k) (impossibleWord k).length
      (occurringIndices (AssignmentSearch.unsatFamily k))) :
    ¬ ∃ bound : Nat → Nat, PolynomiallyBounded bound ∧
      ∀ k, (tree k).falseQueries.length ≤ bound (impossibleWord k).length := by
  rintro ⟨bound, hBound, hQueries⟩
  exact AssignmentSearch.no_polynomial_bound_for_unsatFamily_trials
    ⟨bound, hBound, fun k ↦ (pow_two_le_queries_of_decidesOnProfile (tree k) (hDecides k)).trans
      (hQueries k)⟩

end PvsNP.AssignmentQueryFamily
