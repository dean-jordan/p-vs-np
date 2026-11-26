module

public import PvsNP.Circuits.ConstantFolding
public import PvsNP.MCSP.Streaming

/-! # Exact gate-basis agreement for truth-table thresholds -/

public section

namespace PvsNP.MCSP

open Circuits

/-- At positive arity and caps of at least two, a correct streaming merge
decides the exact threshold over binary AND, OR, and NOT. -/
theorem searchStream_isSome_iff_constantFree {n cap : Nat} {merge : MergeOracle n}
    (correct : CorrectMerge merge cap) (hArity : 0 < n) (hCap : 2 ≤ cap) (bits : BinaryWord) :
    (searchStream n merge bits).isSome = true ↔
      ∃ c : BooleanCircuit n, c.ConstantFree ∧ c.size ≤ cap ∧ truthTable n c.eval = bits := by
  rw [searchStream_isSome_iff correct bits]
  exact (exists_constantFree_size_le_iff hArity hCap
    (fun eval ↦ truthTable n eval = bits)).symm

end PvsNP.MCSP
