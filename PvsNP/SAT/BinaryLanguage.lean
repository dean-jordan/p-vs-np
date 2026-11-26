module

public import PvsNP.Complexity.Classes
public import PvsNP.SAT.BinaryEncoding

/-! # The language of satisfiable binary CNF words -/

@[expose] public section

namespace PvsNP

/-- Binary words that decode completely as a satisfiable CNF. -/
def CNFSAT : BinaryLanguage :=
  {w | ∃ F, CNFCode.decode w = some F ∧ CNF.Satisfiable F}

theorem encode_mem_CNFSAT_iff (F : CNF.Formula Nat) :
    CNFCode.encode F ∈ CNFSAT ↔ CNF.Satisfiable F := by
  change (∃ G, CNFCode.decode (CNFCode.encode F) = some G ∧ CNF.Satisfiable G) ↔ _
  simp [CNFCode.decode_encode]

end PvsNP
