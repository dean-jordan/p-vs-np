# P vs. NP

A Lean 4 and Mathlib formalization of Stephen Cook's P vs. NP problem over
finite binary strings. The project uses Cook's single-tape machine model and
verifier definition. [Cook's official problem description](https://www.claymath.org/wp-content/uploads/2022/06/pvsnp.pdf)

## Status

**P vs. NP remains unresolved.** Lean proves `P ⊆ NP` and that binary CNF-SAT
is NP-complete under polynomial-time many-one reductions in Cook's machine
model. The resulting equivalences are `P = NP ↔ CNFSAT ∈ P` and
`P ≠ NP ↔ CNFSAT ∉ P`. The remaining question is whether a deterministic Cook
machine decides binary CNF-SAT and halts in polynomial time on every binary
input. [Containment](PvsNP/Complexity/Containment.lean) · [Completeness and equivalences](PvsNP/SAT/Completeness.lean)

The Cook–Levin reduction uses a finite register program that emits the exact
binary tableau word within a polynomial instruction bound for each fixed
verifier. The register-to-tape simulation yields a single-tape Cook transducer
that halts with that word in canonical tape position. The CNF-SAT certificate
checker is a separate Cook machine with a quadratic bound on all pair inputs.
[Tableau generator](PvsNP/CookLevin/Generator/VerifierProgram.lean) · [Tape simulation](PvsNP/TuringMachine/Registers/SimulationBound.lean) · [SAT verifier](PvsNP/SAT/VerifierMachine.lean)

Every polynomial-time Cook decider has a polynomial-size family of
fan-in-two Boolean circuits. Polynomial-time reductions preserve membership
in `P/poly`, so binary CNF-SAT has polynomial-size circuits exactly when every
language in `NP` does. A superpolynomial circuit size lower bound for any
language in `NP` would prove separation.
[Cook-to-circuit bridge](PvsNP/Complexity/CircuitLowerBound.lean) · [Closure under reductions](PvsNP/Complexity/CircuitReductions.lean)

Lean defines a binary language by taking the first truth table missed by
circuits with at most `⌊2^n / (8n)⌋` gates. It proves that every circuit
for its length-`n` slice exceeds that budget for `n ≥ 5` and that the
language lies outside `P/poly`. An NP verifier for this language would prove
`P ≠ NP`. The verifier remains open, and using the whole selected truth
table as a certificate exceeds every fixed polynomial length bound on
accepted inputs. [Counting lower bound](PvsNP/Complexity/CountingLowerBound.lean)

A polynomial-time Cook verifier for the counting language would require
at least `2^n / g(n)` distinct certificates that accept some input at each
length `n ≥ 10`, for a polynomially bounded `g`. Over the standard binary
certificate alphabet this requires a length cap of at least `n − O(log n)`.
Unary certificates cannot supply enough candidates.
[Verifier bounds](PvsNP/Complexity/CountingVerifierBounds.lean)

For injective zero padding from length `n` to length `N(n)`, the padded
counting language lies in `P/poly` exactly when `2^n` is polynomially
bounded in `N(n)`. Polynomial padding preserves the counting lower bound.
Padding that makes either full enumeration polynomial, or that brings
full-table certificates within a fixed polynomial length bound on accepted
inputs, gives the padded language polynomial-size circuits.
[Padding criterion](PvsNP/Complexity/CountingPadding.lean)

Every correct circuit over binary AND and OR, NOT, and constants for `n`-bit
binary CNF-SAT has at least `n` gates when `n ≥ 16`. For every `a`, the stronger
bound `n + a` holds whenever
`9 * 2^a + 17 ≤ n`. It counts binary gates from input relevance and NOT gates
from output decreases along increasing input sequences.
[General-circuit lower bound](PvsNP/SAT/CircuitNegationSize.lean)

At every input length, correct CNF-SAT circuits over the same gate basis
also need at least `2n − 44` gates. For every pair of positions
`13 ≤ i < j ≤ n − 30`, a suitable setting of the other bits gives XOR
or XNOR on the pair. The proof tracks those pairs through gates and
counts how often the circuit must reuse a wire.
[Parity-restriction lower bound](PvsNP/SAT/CircuitParitySize.lean)

Allowing all 16 two-input Boolean operations, including XOR, still
requires at least `2n − 46` binary gates. Each interior pair has one
restriction of parity type and another of AND or OR type. The proof
counts binary gates even when constants and NOT gates are free. A
separate equivalence proves that the two gate bases give the same
polynomial-size circuit class.
[Full binary-basis bound](PvsNP/SAT/CircuitBinaryBasisSize.lean) · [Circuit class equivalence](PvsNP/Complexity/BinaryBasisCircuits.lean)

Every total deterministic Cook decider for binary CNF-SAT requires
worst-case time of order at least `n^2 / log n` at every sufficiently
large input length. The proof counts the machine states transmitted
across tape cuts between two encoded tables that store several bits per
address. The exact inequality displays the dependence on the number of
machine states. A separate theorem rules out every fixed rational time
exponent below two on a rejecting input.
[Cook machine time lower bound](PvsNP/SAT/CrossingPaletteWorstCase.lean) · [Rational clock bound](PvsNP/SAT/CrossingPowerBound.lean)

The circuit-minimization route verifies a one-bit-at-a-time search for a circuit
of at most `s` gates that computes a given `n`-input truth table. Each successful
update keeps a bounded circuit for the rows already read. The state has a
reversible binary encoding with an `n + 1` bit row counter and a circuit
description, and the scan makes at most one merge request for each input bit.
A proposed merge is correct exactly when its constructed binary CNF word
is unsatisfiable. Given an exact feasibility oracle for description prefixes,
the search recovers a merge circuit with at most one more query than the
padded description length. A time bound for computing the merge on a work
tape with a separate one-way input tape remains open here.
[Streaming search](PvsNP/MCSP/Streaming.lean) · [State and request counts](PvsNP/MCSP/StreamResources.lean) · [Violation CNF](PvsNP/MCSP/ViolationCNF.lean) · [Merge search](PvsNP/MCSP/MergeSearch.lean)

Merge-prefix feasibility now has a canonical binary request format. Under
`P = NP`, a polynomial-time Cook implementation of one binary counterexample
checker puts this feasibility language in `P`. The proof uses a paired-tape
simulation to turn a binary decider into a checker on Cook's `x#y` alphabet
with at most twice as many transitions on the packed input. The register
fragments verify packed-pair scanning and fixed-width field operations. A
complete Cook decider checks packed-pair syntax. Given a feasibility decider,
each recorded query made from a retained streaming state runs within one fixed
polynomial in the arity and gate cap.
The same counterexample language has certificates containing both circuits'
wire values, each certificate at most as long as its query. The executable
checker is exact on all words. Counted fragments now parse nested framing,
read both unary headers, compute gate-field widths, compare strided row
fields, and check a prepared block of serialized gates against supplied wire
values.
[Executable checker](PvsNP/MCSP/TraceChecker.lean) · [Counted gate loop](PvsNP/MCSP/GateBlockRegister.lean) · [Query clock](PvsNP/MCSP/ClockedPrefixOracle.lean) · [Remaining verifier program](PvsNP/MCSP/VerifierProgram.lean)

An empty certificate tests only the packed query's structure. Lean proves
that count, output, gate-record, and zero-padding checks characterize the
canonical padded circuit codec. A counted fragment runs the output, gate,
and padding checks on either packed circuit once its lengths and cursors
are prepared. Separate counted scans check prefix agreement and the row
counter bound directly in binary. For a valid query, the trace certificate
has an exact size and a checked decomposition into row, trace, and output
fields.
[Empty certificate](PvsNP/MCSP/TraceQueryLayout.lean) · [Padded description checks](PvsNP/MCSP/PaddedDescriptionRegister.lean) · [Certificate layout](PvsNP/MCSP/TraceCertificateLayout.lean)

The verifier's counted front end starts from blank registers and checks
framing, unary headers, field lengths, both padded circuit descriptions,
the row counter, and the requested prefix. Bad queries go directly to the
specified answer. The continuation receives a valid decoded query with
both gate counts and the measured circuit layout.
[Structural verifier](PvsNP/MCSP/StructuredVerifier.lean) · [Raw circuit checker](PvsNP/MCSP/CheckedDescriptionRegister.lean)

Constant folding gives the exact truth-table threshold over binary AND,
OR, and NOT for positive arity and gate budgets of at least two. Lean also
defines a one-way read-only input tape with a separate writable work tape.
The Cook-machine adapter loads the blank work tape in exactly `2N + 2`
steps and then simulates each Cook step in one step.
[Exact gate basis](PvsNP/MCSP/ConstantFreeThreshold.lean) · [One-way input adapter](PvsNP/TuringMachine/OneWayInput.lean)

Lean uses integer roots for the exact gate threshold `⌊2^(n/k)⌋` and
the time threshold `⌊N^(101/100)⌋`. Every fixed polynomial charge per
row fits the time threshold eventually when `k` is sufficiently large.
A separation by this route still needs a one-way implementation with
that row bound under `P = NP` and a matching lower bound for the same
gate thresholds.
[Exact magnification clock](PvsNP/MCSP/MagnificationClock.lean)

The assignment-search analysis proves a superpolynomial worst-case lower
bound on complete-assignment queries for deterministic solvers whose inputs
are the word length, the occurring names, and the answers to those queries.
The class question concerns Cook machines that read the full formula.
[Query lower bound](PvsNP/SAT/AssignmentQueryLowerBound.lean)

The pigeonhole instances require superpolynomially many events in refutations
that use variable decisions and input-clause unit propagation. The bound holds
for every branching order and uses the same binary CNF encoding as the
completeness theorem. [Branching lower bound](PvsNP/SAT/PigeonholeLowerBound.lean)

Adding unit clauses lets a binary CNF-SAT decision oracle recover a
satisfying assignment on an `n`-bit input with at most `n + 1` queries of
length at most `n + n * (n + 5)`. The clocked version uses exact Cook
machine runs for the recorded calls. Polynomial-size SAT decision circuits
are equivalent to polynomial-size circuits that output a success bit and
a satisfying assignment on success.
[Witness search](PvsNP/SAT/OracleSearch.lean) · [Witness circuits](PvsNP/SAT/SearchCircuits.lean)

Given a polynomial-time CNF-SAT decider, a finite single-tape Cook controller
processes a satisfiable formula from a prepared layout. Each stage appends a
false trial clause, copies the query to scratch, calls the decider, and commits
the sign implied by its answer. After `n` stages on an `n`-bit formula, the
protected query encodes a checked satisfying assignment. The proof bounds
these stages by a fixed polynomial and uses the same workspace and unary-stop
marks throughout. Initializing the layout from raw input, handling rejected
inputs, and halting with the assignment in canonical output position remain
to be verified.
[Workspace proof](PvsNP/SAT/OracleWorkspace.lean) · [Prepared search run](PvsNP/SAT/QueryLoopProgram.lean)

## Repository map

| Area | Contents |
| --- | --- |
| [Turing machines](PvsNP/TuringMachine) | Cook semantics, output bounds, transducers, and counted single-tape register operations |
| [Complexity classes](PvsNP/Complexity) | Pair encoding, polynomial bounds, `P`, `NP`, containment, and reductions |
| [Boolean circuits](PvsNP/Circuits) | Fan-in-two circuits, bounded Cook machine simulation, and circuit and truth-table counts |
| [Circuit minimization](PvsNP/MCSP) | Size-bounded agreement, binary merge witnesses, and one-pass truth-table search with a merge oracle |
| [SAT](PvsNP/SAT) | CNF semantics, binary encoding, single-tape verifier, completeness, and assignment queries |
| [Cook–Levin](PvsNP/CookLevin) | Finite tape windows, certificate initialization, bounded binary tableaux, and exact indexed generation |
| [Verification](PvsNP/Verification) | Axiom audits for the main theorems and bridges |

The [proof guide](docs/ProofGuide.md) maps the arguments to Lean declarations.
The [research log](docs/ResearchLog.md) records design decisions, checked results,
and the open question.

See the [contributor guide](CONTRIBUTING.md) for proof and review conventions.
[Citation metadata](CITATION.cff) identifies the repository and Cook's specification.

## Reproduce the checks

Install Elan and run the following from the repository root. The toolchain and
dependency revisions are pinned by `lean-toolchain` and `lake-manifest.json`.
[Elan installation](https://lean-lang.org/install/manual/)

```sh
export LEAN_NUM_THREADS=1
lake exe cache get Mathlib.Computability.TuringMachine.Tape \
  Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas \
  Mathlib.Algebra.BigOperators.Group.Finset.Piecewise \
  Mathlib.Basic.Finite.Prod Mathlib.Basic.Finite.Sum Mathlib.Basic.Finite.Sigma \
  Mathlib.Data.Fin.Embedding Mathlib.Data.Finset.Card Mathlib.Data.Finset.Max \
  Mathlib.Data.Fintype.BigOperators Mathlib.Data.Fintype.Option \
  Mathlib.Data.Fintype.Prod Mathlib.Data.Fintype.Sum Mathlib.Data.Fintype.EquivFin \
  Mathlib.SetTheory.Cardinal.Finite Mathlib.Tactic.DeriveFintype
lake clean PvsNP
lake build --wfail
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
lake env lean PvsNP/Verification/Axioms.lean
```

The targeted cache fetches precompiled artifacts for the listed Mathlib
modules and their dependencies. `lake clean PvsNP` clears project build
outputs while retaining dependency artifacts. The axiom audit permits
`propext`, `Classical.choice`, and `Quot.sound`.
