module

public import PvsNP.CookLevin.Generator.FiniteTable
public import PvsNP.TuringMachine.Registers.SimulationBound

/-! # From register programs to the binary tableau reduction -/

@[expose] public section

namespace PvsNP.CookLevin

open RegisterMachine

/-- A polynomially bounded register program for every fixed indexed tableau gives
Cook's polynomial-time binary tableau map. -/
theorem binaryTableauxPolyTime_of_registers
    (generate : ∀ {qCount symbolCount certificateCount : Nat}
      (table : FiniteTable qCount symbolCount certificateCount) (k d : Nat),
      ∃ (R L : Type) (_ : Finite R) (_ : Finite L) (eq : DecidableEq R) (entry : L)
        (program : L → Instruction R L) (bound : Nat → Nat),
        PolynomiallyBounded bound ∧ ∀ x, ∃ steps ≤ bound x.length, ∃ cfg,
          @RegisterMachine.run R L eq program x steps (Config.initial entry) = some cfg ∧
          cfg.pc = none ∧ cfg.output = table.binaryVerifierMap x k d) :
    BinaryTableauxPolyTime := by
  apply binaryTableauxPolyTime_of_indexed
  intro qCount symbolCount certificateCount table k d
  obtain ⟨R, L, hR, hL, eq, entry, program, bound, hBound, hRun⟩ := generate table k d
  exact @polynomialTimeMap_of_run R L hR hL eq entry program _ bound hBound hRun

end PvsNP.CookLevin
