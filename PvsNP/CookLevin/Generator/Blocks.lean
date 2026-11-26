module

public import PvsNP.CookLevin.Generator.Prefix
public import PvsNP.CookLevin.Generator.Rows

/-! # The binary verifier map as a composition of four sections -/

@[expose] public section

namespace PvsNP.CookLevin

variable {states symbols certificates width : Nat}

/-- Prepend the encoded clause and its formula-level marker. -/
def emitIndexedClause (suffix : BinaryWord)
    (clause : CNF.Clause (Tableau.Atom (Fin states) (Fin symbols) width)) : BinaryWord :=
  true :: (CNFCode.encodeClause (clause.map (CNF.Literal.map indexedAtomName)) ++ suffix)

/-- The descending traversal of the transition section. -/
def FiniteTable.transitionOutput (table : FiniteTable states symbols certificates)
    (width steps : Nat) (suffix : BinaryWord) : BinaryWord :=
  Traversal.foldNatDesc
    (table.foldStepClauses (emitIndexedClause (width := width))) suffix steps

private theorem prepend_emitClause (suffix : BinaryWord) (clause : CNF.Clause Nat) :
    Serialization.emitClause (fun acc bit ↦ bit :: acc) suffix clause =
      CNFCode.encodeClause clause ++ suffix := by
  rw [Serialization.emitClause_eq_foldl, List.foldl_flip_cons_eq_append', List.reverse_reverse]

/-- The accepting, transition, row, and initial sections compose to the exact binary map. -/
theorem FiniteTable.binaryVerifierMap_eq_sections (table : FiniteTable states symbols certificates)
    (x : BinaryWord) (k d : Nat) (suffix : BinaryWord) :
    let t := horizon x.length k d
    let width := 2 * t + 1
    let accepted := table.acceptanceCode x.length k d ++ suffix
    let transitions := table.transitionOutput width t accepted
    let rows := tableauRowsOutput states symbols width (Tableau.atomStride states width symbols)
      t transitions
    table.binaryVerifierMap x k d ++ suffix =
      table.foldInitialClauses emitIndexedClause rows (Machine.windowCenter t) x
        (x.length ^ k) := by
  dsimp only
  rw [tableauRowsOutput_eq states symbols _ _ _ _ rfl, ← table.emitVerifier_prepend]
  simp only [FiniteTable.emitVerifier, FiniteTable.foldVerifierClauses, prepend_emitClause]
  simp only [FiniteTable.transitionOutput, FiniteTable.acceptanceCode, FiniteTable.acceptanceName,
    CNFCode.encode_cons, CNFCode.encode_nil, List.cons_append, List.append_assoc,
    List.map_cons, List.map_nil, CNF.Literal.map]
  rfl

end PvsNP.CookLevin
