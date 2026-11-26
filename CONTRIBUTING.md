# Contributing

State the Lean declarations that a change establishes and the hypotheses they
require. For a bridge to Cook's problem, identify the reference definitions and
prove preservation of the result and any required time bound. Record unchecked
claims and remaining proof obligations in the project notes. [Cook's specification](https://www.claymath.org/wp-content/uploads/2022/06/pvsnp.pdf)

## Verify locally

Use the versions in `lean-toolchain` and `lake-manifest.json`. Run from the
repository root after installing Elan. [Lean installation instructions](https://lean-lang.org/install/manual/)

```sh
export LEAN_NUM_THREADS=1
lake exe cache get Mathlib.Computability.TuringMachine.Tape \
  Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas \
  Mathlib.Basic.Finite.Prod Mathlib.Basic.Finite.Sum Mathlib.Basic.Finite.Sigma \
  Mathlib.Data.Fin.Embedding Mathlib.Data.Finset.Card \
  Mathlib.Data.Fintype.Option Mathlib.Data.Fintype.Prod Mathlib.Data.Fintype.Sum \
  Mathlib.Data.Fintype.EquivFin Mathlib.Tactic.DeriveFintype
lake clean PvsNP
lake build --wfail
lake env lean PvsNP/Verification/Axioms.lean
lake env leanchecker --fresh PvsNP.Complexity.CircuitReductions
lake env leanchecker --fresh PvsNP.Complexity.CountingVerifierBounds
lake env leanchecker --fresh PvsNP.MCSP.ClockedPrefixOracle
lake env leanchecker --fresh PvsNP.MCSP.NestedPairRegister
lake env leanchecker --fresh PvsNP.MCSP.GateBlockRegister
lake env leanchecker --fresh PvsNP.MCSP.PaddedDescriptionRegister
lake env leanchecker --fresh PvsNP.MCSP.CheckedDescriptionRegister
lake env leanchecker --fresh PvsNP.MCSP.TraceQueryLayout
lake env leanchecker --fresh PvsNP.MCSP.TraceCertificateLayout
lake env leanchecker --fresh PvsNP.MCSP.StructuredVerifier
lake env leanchecker --fresh PvsNP.MCSP.TraceCertificateDispatch
lake env leanchecker --fresh PvsNP.MCSP.TraceInputRegister
lake env leanchecker --fresh PvsNP.MCSP.MagnificationClock
lake env leanchecker --fresh PvsNP.MCSP.VerifierProgram
lake env leanchecker --fresh PvsNP.TuringMachine.OneWayInput
lake env leanchecker --fresh PvsNP.TuringMachine.Registers.PackedPairDecision
lake env leanchecker --fresh PvsNP.MCSP.MergeWitness
lake env leanchecker --fresh PvsNP.MCSP.StreamResources
lake env leanchecker --fresh PvsNP.MCSP.ViolationCNF
lake env leanchecker --fresh PvsNP.SAT.CircuitBinaryBasisSize
lake env leanchecker --fresh PvsNP.SAT.CircuitNegationSize
lake env leanchecker --fresh PvsNP.SAT.CircuitParitySize
lake env leanchecker --fresh PvsNP.SAT.Completeness
lake env leanchecker --fresh PvsNP.SAT.CrossingPaletteWorstCase
lake env leanchecker --fresh PvsNP.SAT.CrossingPowerBound
lake env leanchecker --fresh PvsNP.SAT.CrossingTimeLowerBound
lake env leanchecker --fresh PvsNP.SAT.VerifierMachine
lake env leanchecker --fresh PvsNP.SAT.AssignmentQueryLowerBound
lake env leanchecker --fresh PvsNP.SAT.PigeonholeLowerBound
lake env leanchecker --fresh PvsNP.SAT.SearchCircuits
lake env leanchecker --fresh PvsNP.SAT.OracleCalls
lake env leanchecker --fresh PvsNP.SAT.OracleWorkspace
lake env leanchecker --fresh PvsNP.SAT.QueryLoopProgram
lake env leanchecker --fresh PvsNP
```

When adding a result or bridge, add `#print axioms` for its fully qualified name
to the audit file. The audit allows `propext`, `Classical.choice`, and
`Quot.sound`. Run `lake env leanchecker --fresh` on each new result module and
include the commands and outcomes in the pull request.
