module

public import PvsNP.CookLevin.Generator.ExactlyOne

/-! # Numeric output of one tableau row -/

@[expose] public section

namespace PvsNP.CookLevin

/-- Emit the cell fields in descending order, then the head and state fields. -/
def tableauRowOutput (states symbols width stride time : Nat) (suffix : BinaryWord) : BinaryWord :=
  let rowBase := time * stride
  let cells := (List.range width).reverse.foldl
    (fun out i ↦ exactlyOneFieldOutput (rowBase + states + width + i * symbols) symbols out)
    suffix
  let head := exactlyOneFieldOutput (rowBase + states) width cells
  exactlyOneFieldOutput rowBase states head

/-- Consecutive numeric intervals emit exactly the named clauses of a tableau row. -/
theorem tableauRowOutput_eq (states symbols width stride time : Nat) (suffix : BinaryWord)
    (hStride : stride = Tableau.atomStride states width symbols) :
    tableauRowOutput states symbols width stride time suffix =
      FiniteTable.foldRowClauses
        (fun acc (clause : CNF.Clause (Tableau.Atom (Fin states) (Fin symbols) width)) ↦
          true :: (CNFCode.encodeClause (clause.map (CNF.Literal.map indexedAtomName)) ++ acc))
        suffix time := by
  subst stride
  let stride := Tableau.atomStride states width symbols
  let emit (acc : BinaryWord)
      (clause : CNF.Clause (Tableau.Atom (Fin states) (Fin symbols) width)) :=
    true :: (CNFCode.encodeClause (clause.map (CNF.Literal.map indexedAtomName)) ++ acc)
  change tableauRowOutput states symbols width stride time suffix =
    FiniteTable.foldRowClauses emit suffix time
  have hCell (i : Fin width) (acc : BinaryWord) :
      Traversal.foldExactlyOne symbols (Tableau.Atom.cell time i) emit acc =
        exactlyOneFieldOutput (time * stride + states + width + i.val * symbols) symbols acc := by
    apply foldExactlyOne_named
    intro s
    simp [stride, indexedAtomName, Tableau.Atom.name, Tableau.Atom.time, Tableau.Atom.offset,
      Nat.add_assoc]
  have hHead (acc : BinaryWord) :
      Traversal.foldExactlyOne width (Tableau.Atom.head time) emit acc =
        exactlyOneFieldOutput (time * stride + states) width acc := by
    apply foldExactlyOne_named
    intro i
    simp [stride, indexedAtomName, Tableau.Atom.name, Tableau.Atom.time, Tableau.Atom.offset,
      Nat.add_assoc]
  have hState (acc : BinaryWord) :
      Traversal.foldExactlyOne states (Tableau.Atom.state time) emit acc =
        exactlyOneFieldOutput (time * stride) states acc := by
    apply foldExactlyOne_named
    intro q
    rfl
  simp only [tableauRowOutput, FiniteTable.foldRowClauses, hCell, hHead, hState]
  rw [foldFinDesc_values width
    (fun out i ↦ exactlyOneFieldOutput (time * stride + states + width + i * symbols) symbols out)
    suffix]

end PvsNP.CookLevin
