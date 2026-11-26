# Research log

The [proof guide](ProofGuide.md) records the theorem chain. This log records
the design decisions, checked results, and open P vs. NP question.

## Reference model

- Mathlib's `TM0` separates writing from moving, so its transition count
  differs from Cook's. `appendixTick_toConfig` proves a one-for-one
  correspondence for the machine that writes and moves in a single
  transition. `appendixRun_toConfig` lifts this correspondence to runs.
  [Core](../PvsNP/TuringMachine/Core.lean)
- Mathlib's stack-machine emulator establishes reachability in the tape model.
  Its use here would require a quantitative simulation theorem and a bridge
  to Cook's transitions. The current proofs use Cook's transitions directly.
- The equivalence between polynomial conventions treats input lengths zero
  and one separately. Increasing the exponent alone leaves `1^k` unchanged.
  [Time bounds](../PvsNP/Complexity/TimeBounds.lean)

## Containment and reductions

- The empty-certificate verifier checks the whole input language. A proof
  about valid pairs alone leaves rejection of malformed inputs unproved.
  `verifier_decides` checks the case split and `verifier_polyTime` supplies
  a bound for every input. [Containment](../PvsNP/Complexity/Containment.lean)
- Exhaustive certificate search has no polynomial worst-case bound from the
  certificate length bound alone. `NP_subset_P_iff_verifierProjection`
  retains the obligation to construct a polynomial decision machine for
  every bounded existential projection. [Classes](../PvsNP/Complexity/Classes.lean)
- A direct tape handoff needs both machines to agree on blank and on the two
  input bits. `leftPointed_map_start` and `rightPointed_map_start` prove
  this agreement while the machines' work symbols remain separate.
  [Shared alphabet](../PvsNP/TuringMachine/SharedAlphabet.lean)
- `outputsAt_firstHalt` and the two run simulations ensure that the handoff
  happens once. The physical output bound `output_length_le` supplies the
  output-size estimate needed to compose the machines' time bounds.
  [Transducer](../PvsNP/TuringMachine/Transducer.lean) · [Output bound](../PvsNP/TuringMachine/OutputBound.lean) · [Reductions](../PvsNP/Complexity/Reductions.lean)

## SAT route

- The finite run observes a window of radius `T`. The initial CNF constraints
  also need every possible certificate slot, so the chosen horizon covers
  the largest encoded input length as well as the verifier time bound.
  [Tape window](../PvsNP/CookLevin/TapeWindow.lean) · [Verifier tableau](../PvsNP/CookLevin/VerifierTableau.lean)
- Counting clauses without bounding variable names leaves binary output size
  undetermined. Dense naming and the unary encoding bound both costs.
  `mem_NP_has_binaryCNF_map` records the resulting membership and output
  length guarantees. The machine proof separately counts the work needed to
  produce these bits.
  [Variable names](../PvsNP/CookLevin/VariableNames.lean) · [Binary reduction](../PvsNP/CookLevin/BinaryReduction.lean)
- `mem_CNFSAT_iff_exists_assignment` and `checkEncoded_eq_true_iff` verify
  certificate semantics, the linear certificate bound, and rejection of
  malformed words. `checkWord_eq` and `cursor_run_le` verify streaming
  correctness and the cursor bound. [Assignment](../PvsNP/SAT/Assignment.lean) · [Stream](../PvsNP/SAT/Stream.lean)
- Counting one abstract update per formula bit leaves the distance between
  the formula and certificate cursors unaccounted for. `run_seek` and
  `run_restore` count the physical sweeps. Clamping the certificate marker
  at the end blank bounds the traversed region even for a unary index longer
  than the supplied certificate. `read_saturated` proves the clamped and
  abstract reads return the same value.
  [Cursor program](../PvsNP/SAT/CursorProgram.lean) · [Shuttles](../PvsNP/SAT/VerifierSweeps.lean)
- `verifierMachine_halt` proves a quadratic bound for the explicit Cook
  verifier on all pair words, including early rejection of malformed pairs.
  `cnfSAT_mem_NP` establishes NP membership using this verifier.
  [Machine correctness](../PvsNP/SAT/VerifierMachine.lean)
- The transducer needs to emit the exact encoded word because the existing
  reduction theorem refers to one fixed map. `finiteTable_binaryVerifierMap`
  proves equality after flattening the verifier into fixed numeric tables,
  preserving clause and literal order. `binaryTableauxPolyTime_of_indexed`
  transfers the polynomial transducer proofs for those indexed maps.
  [Finite table](../PvsNP/CookLevin/Generator/FiniteTable.lean)
- The output region grows leftward. `emitFormula_prepend` proves that reverse
  traversal gives the canonical forward word without a final reversal pass.
  `run_emitBit` counts both sweeps for each stored bit and `run_finish` counts
  cleanup of the other tape regions and the move to the start of the output.
  [Serialization](../PvsNP/CookLevin/Generator/Serialization.lean) · [Emission](../PvsNP/TuringMachine/Registers/Output.lean) · [Cleanup](../PvsNP/TuringMachine/Registers/Finish.lean)
- Sharing a tape cell across registers requires updates to preserve all other
  lanes. `Represents.increment` and `Represents.decrement` prove this for unary
  registers. The physical proofs count the sweeps from the boundary and back,
  including increment into a blank and the zero branch of decrement. The
  cursor proofs account for returning to the boundary after each input read.
  [Values](../PvsNP/TuringMachine/Registers/Values.lean) · [Decrement](../PvsNP/TuringMachine/Registers/DecrementCorrectness.lean) · [Cursor](../PvsNP/TuringMachine/Registers/InputLayout.lean)
- A valid instruction increases the stored register extent and output length
  by at most one. `Matches.run` uses these bounds to sum the counted sweeps
  through the entire run. `outputsAt_of_run` includes framing and cleanup in
  the tape bound, so the generator proof can count finite register
  instructions. [Simulation bound](../PvsNP/TuringMachine/Registers/SimulationBound.lean)
- `run_copy` restores its source and scratch registers after copying into an
  initially zero target. `run_inputLength` counts the input using a single
  register and clears the input mark at the end. `run_add_register` permits a
  nonzero target, and `run_multiply` iterates addition while consuming the
  multiplier. These operations support the computations of the tableau
  horizon and dense variable indices.
  [Copy](../PvsNP/TuringMachine/Registers/Copy.lean) · [Length](../PvsNP/TuringMachine/Registers/InputLength.lean) · [Addition](../PvsNP/TuringMachine/Registers/Add.lean) · [Multiplication](../PvsNP/TuringMachine/Registers/Multiply.lean)
- `emitVerifier_prepend` proves that the descending loop traversal and bit
  emission rebuild the indexed verifier word. It specifies the result of the
  abstract traversal. The finite register proofs separately count loop
  control, input lookups, and arithmetic. `run_emitLiteral` implements one
  framed literal once its numeric index is in a register.
  [Traversal](../PvsNP/CookLevin/Generator/Traversal.lean) · [Literal emission](../PvsNP/CookLevin/Generator/EmitLiteral.lean)
- Each fragment has a finite internal control and a normal exit. `run_link`
  proves that relocating the labels preserves a valid run and its length.
  `run_seq` joins two fragments without spending an instruction between
  them. `run_countdown_model` links a repeated body and preserves a stated
  invariant through descending counter values, including empty loop bodies.
  [Linking](../PvsNP/TuringMachine/Registers/Fragments.lean) · [Countdown](../PvsNP/TuringMachine/Registers/Countdown.lean)
- `run_inputAt` returns a reverse-indexed bit, handles an out-of-range index,
  and clears the mark and index. `run_compare` preserves its operands and
  returns all scratch lanes to zero. These primitives support input and
  boundary tests inside initial tape and transition clauses.
  [Input lookup](../PvsNP/TuringMachine/Registers/InputAt.lean) · [Comparison](../PvsNP/TuringMachine/Registers/Compare.lean)
- `run_power` uses one finite control block per multiplication for each
  fixed exponent. `run_parameterPrelude` links these powers with input
  length, arithmetic on the window dimensions, and stride initialization.
  The proof identifies the final registers and proves an exact instruction
  count with a polynomial bound. `run_accumulateName` implements the shared
  `time * stride + offset` calculation with two reusable work registers.
  [Fixed powers](../PvsNP/TuringMachine/Registers/Power.lean) · [Prelude](../PvsNP/CookLevin/Generator/Parameters.lean) · [Name calculation](../PvsNP/CookLevin/Generator/NameRegister.lean)
- `run_generatorPrefix` links the computed horizon and stride to the first
  output block, which contains the last clause and the formula terminator.
  `binaryVerifierMap_acceptance_suffix` checks where this block belongs in the
  exact word. `acceptanceCode_polynomialTime` applies the Cook tape simulation
  to the linked prefix with an explicit halt.
  [Generator prefix](../PvsNP/CookLevin/Generator/Prefix.lean)
- Exactly-one constraints include both orders of every distinct pair. The
  two countdown loops retain that order, and the equality branch emits no
  diagonal clause. The positive clause follows the pair block in emission
  order. `tableauRowsOutput_eq` identifies the resulting serialized section
  with the original indexed rows. `run_rowsFragment` implements it with a
  single uniform row budget evaluated at the horizon.
  `binaryTableauRows_polynomialTimeMap` closes the linked row program into
  a Cook transducer after computing the parameters from the original word.
  [Exactly-one field](../PvsNP/CookLevin/Generator/ExactlyOne.lean) · [Rows](../PvsNP/CookLevin/Generator/Rows.lean) · [Row transducer](../PvsNP/CookLevin/Generator/RowProgram.lean)
- Transition preparation computes separate name bases for the old and new
  rows. The copy traversal excludes the scanned cell. The update traversal
  enumerates the fixed state and symbol indices and applies the table's head
  movement with the same window boundary convention as `windowAdvance`.
  The body budget accounts for name preparation and clearing temporary lanes
  as well as clause emission. The bound grows monotonically with the current
  time, so `run_stepsFragment` uses the bound at the horizon for every body.
  [Preparation](../PvsNP/CookLevin/Generator/StepPreparation.lean) · [Copies](../PvsNP/CookLevin/Generator/StepCopies.lean) · [Updates](../PvsNP/CookLevin/Generator/StepUpdates.lean) · [Transition pass](../PvsNP/CookLevin/Generator/Steps.lean)
- Forward lookup converts an in-range position to a reverse index and clears
  the work registers before selecting a branch. The initial cell pass tests
  the left blank region, the instance and separator, and the certificate
  interval. Its final branch handles the right blank region. Every cell uses
  a numeric base in the row-zero name range. The gap pass emits a constraint
  only for adjacent certificate positions. `run_initialSectionWindow` links
  both passes with boundary setup and the head and state clauses.
  [Forward lookup](../PvsNP/TuringMachine/Registers/ForwardLookup.lean) · [Cell pass](../PvsNP/CookLevin/Generator/InitialCells.lean) · [Gap pass](../PvsNP/CookLevin/Generator/InitialGaps.lean) · [Initial section](../PvsNP/CookLevin/Generator/InitialSection.lean)
- `FiniteTable.binaryVerifierMap_eq_sections` checks the section boundaries
  and the exact output suffix throughout emission. It connects the four
  independently specified sections to the word used by the reduction.
  `runsOutput_verifierProgram` then joins the sections using a finite layout
  that shares the initialized dimensions and gives each stage its required
  empty work registers. `run_verifierProgram` includes the halt, and
  `binaryTableauxPolyTime_verified` transfers the polynomial register bound
  and exact output to Cook's single-tape machine model.
  [Section order](../PvsNP/CookLevin/Generator/Blocks.lean) · [Complete generator](../PvsNP/CookLevin/Generator/VerifierProgram.lean)
- `mem_NP_polynomiallyReducesTo_CNFSAT` and `npComplete_CNFSAT` close the
  reduction and completeness proofs unconditionally. The generator may depend
  on the fixed verifier, its finite alphabets, and its exponents. Its time
  bound is uniform over all instance words for that verifier.
  [Completeness](../PvsNP/SAT/Completeness.lean) · [Complete generator](../PvsNP/CookLevin/Generator/VerifierProgram.lean)

The clean Lean 4.36.0 build passed with warnings treated as errors. Fresh
kernel replay passed for `PvsNP.SAT.Completeness`, `PvsNP.SAT.VerifierMachine`,
and `PvsNP`. The axiom audit covered 460 declarations and found only
`propext`, `Classical.choice`, and `Quot.sound`.
[Verification commands](../README.md#reproduce-the-checks) · [Axiom audit](../PvsNP/Verification/Axioms.lean)

## Complete-assignment search

- Enumerating values only for occurring names saves checks when the unary
  indices are sparse. `searchWord_accepts_iff` proves the resulting search
  decides binary CNF-SAT. The unary index lengths also bound the number of
  distinct names by `⌊√(2n)⌋` on an `n`-bit input, which gives at most
  `2^⌊√(2n)⌋` checks in `searchWord_checks_le`.
  [Distinct names](../PvsNP/SAT/DistinctVariableBound.lean) · [Search](../PvsNP/SAT/AssignmentSearch.lean)
- The contradictory family has exactly `k + 1` names and quadratic word
  length in `k`. `no_polynomial_bound_for_searchWord_checks` rules out a
  polynomial bound for this traversal's worst-case assignment count.
  [Contradictory inputs](../PvsNP/SAT/AssignmentSearchFamily.lean)
- Adaptive query order still leaves a superpolynomial assignment count when
  a solver receives the word's bit length, the ordered list of names, and
  Boolean answers about complete assignments. For each skipped assignment
  on the all-false path, a word with that same length and list can preserve
  the observed answers while making the skipped assignment its only solution.
  `pow_two_le_queries_of_decidesOnProfile` forces `2^(k+1)` queries on that
  path. A Cook machine with access to the formula can read the two conflicting
  unit clauses directly on this family.
  [Matched formulas](../PvsNP/SAT/AssignmentQueryFamily.lean) · [Adaptive query lower bound](../PvsNP/SAT/AssignmentQueryLowerBound.lean)

The clean warning-free build and fresh kernel replays passed for the query
lower bound, completeness theorem, SAT verifier, and root module. The audit
checked 506 public declarations and 17 private supporting declarations for
the assignment proofs against the standard axiom allowlist.
[Verification commands](../README.md#reproduce-the-checks) · [Axiom audit](../PvsNP/Verification/Axioms.lean)

## Branching and unit propagation

- Clause inspection can spot the conflicting units in the complete-assignment
  family. A harder family for clause-based search encodes `n + 1` pigeons and
  `n` holes. The trace model allows arbitrary fresh-variable decisions, early
  input-clause conflicts, and unit propagation justified by an input clause.
  The scoring technique is the symmetric Prover–Delayer game introduced by
  Pudlák and Impagliazzo.
  [Pigeonhole formula](../PvsNP/SAT/PigeonholeFormula.lean) · [Trace rules](../PvsNP/SAT/PropagationRefutation.lean) · [Prover–Delayer background](https://www.cs.umd.edu/~gasarch/TOPICS/resolution/proverdelayerphp.pdf)
- A partial matching tracks true placements. False entries come from the
  matching or from recorded exclusions. Before the count of placements and
  exclusions reaches `n`, at least one slot remains unfalsified in each row
  and no exclusion clause is falsified. This gives the
  `2^n` leaf bound in `formula_refutation_leaves`.
  [Scoring strategy](../PvsNP/SAT/PigeonholeStrategy.lean)
- Each unit step expands to a decision with an immediate conflict on one side.
  The expansion and variable-name pullback transfer the leaf bound to a
  `2^n` trace event bound on the binary encoding. The instances have polynomial
  bit length in `n`, which excludes a uniform polynomial bound on this form
  of refutation. The unresolved machine obligation concerns every possible
  total deterministic Cook decider for binary CNF-SAT.
  [Trace expansion](../PvsNP/SAT/PropagationRefutation.lean) · [Binary rules and bound](../PvsNP/SAT/PigeonholeLowerBound.lean) · [Classes](../PvsNP/Complexity/Classes.lean)

The clean warning-free build and all five fresh kernel replays passed. The
axiom audits checked 543 public declarations and 13 private declarations
supporting the branching proof. All reported axioms are on the allowlist.
[Verification commands](../README.md#reproduce-the-checks) · [Axiom audit](../PvsNP/Verification/Axioms.lean)

## Boolean circuit route

- Substituting an earlier layer's formulas into each use in a later layer can
  duplicate gates. `Layered.toBooleanCircuit` uses wire indices to share the
  earlier outputs. `Layered.eval_toBooleanCircuit` and
  `Layered.size_toBooleanCircuit_le` give the evaluation and size guarantees
  for the resulting fan-in-at-most-two DAG.
  [Circuit compiler](../PvsNP/Circuits/BooleanCircuit.lean)
- A `T`-tick run uses a window of `2 * T + 1` cells. A fixed machine gives a
  linear number of indicator wires in that width and at most a quadratic
  number of expression nodes per transition layer. `machineLayered_eval`
  identifies the accept bit with the actual Cook run, and
  `machineLayered_size_le` gives a cubic bound in `T + 1`.
  [Layered simulation](../PvsNP/Circuits/WindowSimulation.lean)
- `P_subset_PPoly` applies the circuit construction to every polynomial-time
  Cook decider. The pigeonhole proof measures events in branching and
  unit-propagation traces. A circuit lower bound must cover every
  bounded-fan-in circuit that gives the correct membership answer on all
  inputs of the witnessing length.
  [Circuit classes and separation](../PvsNP/Complexity/CircuitLowerBound.lean) · [Branching lower bound](../PvsNP/SAT/PigeonholeLowerBound.lean)

The clean warning-free build and all six fresh kernel replays passed. The
axiom audits checked 578 public declarations and 19 private declarations
supporting the circuit compiler and simulation. All reported axioms are on
the allowlist.
[Verification commands](../README.md#reproduce-the-checks) · [Axiom audit](../PvsNP/Verification/Axioms.lean)

## Circuit reductions with variable output length

- The exact output length can depend on the input even at a fixed input
  length. `decode_encode_append` shows that extra trailing bits cause
  rejection of an otherwise valid binary CNF code. A `wordBuffer` stores
  the bits followed by false padding and records the exact length through
  separate presence bits. The widened tape window retains all positions
  used to form both parts of the buffer.
  [Binary CNF encoding](../PvsNP/SAT/BinaryEncoding.lean) · [Word buffer](../PvsNP/Circuits/WordBuffer.lean) · [Output simulation](../PvsNP/Circuits/TransducerOutput.lean)
- `selectLength_eval` checks the last present position and first absent
  position wherever they exist. This covers empty and full buffers. Wiring
  each possible length into a separate decision circuit costs at most five
  additional gates per candidate length and one constant for the disjunction.
  `PolynomialTimeMap.preimage_mem_PPoly` uses this selection to join the
  output circuit and the decision circuit with polynomial total cost.
  [Length selection](../PvsNP/Circuits/LengthSelection.lean) · [Circuit reductions](../PvsNP/Complexity/CircuitReductions.lean)
- `CNFSAT_mem_PPoly_iff_np_subset` identifies the circuit question for
  binary CNF-SAT with polynomial circuit families for all of `NP`.
  The reduction permits the lower-bound route to start from any `NP`
  language with superpolynomial circuit requirements.
  [Circuit reductions](../PvsNP/Complexity/CircuitReductions.lean)

The clean warning-free build and all six fresh kernel replays passed. The
axiom audits checked 615 public declarations and 18 private declarations
supporting the new circuit reductions. All reported axioms are on the allowlist.
[Verification commands](../README.md#reproduce-the-checks) · [Axiom audit](../PvsNP/Verification/Axioms.lean)

## Input sensitivity and negation counts

- `BooleanCircuit.card_le_binarySize_add_one_of_sensitive` improves the
  support count by charging only two-input gates. Binary CNF-SAT depends
  individually on every input bit for `n ≥ 16`, including markers whose
  change gives an invalid encoding. `cnfsat_binarySize_ge` gives `n - 1`
  binary gates at these lengths. The separate valid-input construction
  exposes one sign per unit clause, giving `m - 1` binary gates on the
  valid encodings of length `5 * m + 6`.
  [Support bound](../PvsNP/Circuits/InputSupport.lean) · [Sensitivity and gate bounds](../PvsNP/SAT/CircuitSize.lean)
- Setting the final zero of a satisfiable encoding to one makes the word
  reject. This forces at least one NOT gate by `cnfsat_negationSize_pos`.
  Because binary and NOT gates are counted separately, `cnfsat_size_ge`
  gives `n` total gates for `n ≥ 16`, proving the degree-zero case of the
  separation criterion in `cnfsat_exceeds_constant_size`.
  [Terminal witness](../PvsNP/SAT/CircuitSuffixSensitivity.lean) · [Gate bounds](../PvsNP/SAT/CircuitSize.lean)
- An alternating chain can reuse the same two variable names. Two unit
  clauses fix their values, each subsequent two-literal clause adds nine
  bits and one acceptance-to-rejection step, and a filler unit brings the
  chain to the required length. `cnfsat_size_ge_add` adds the resulting
  NOT-gate count to the binary gate bound. At every length
  `n ≥ 9 * 2^extra + 17`, the total gate count is at least `n + extra`.
  This excludes size at most `n + C` at sufficiently large lengths for
  each fixed `C`. In particular, `extra = 2` gives at least `n + 2` gates
  for `n ≥ 53`, exceeding the bound `n + 1` at coefficient one and degree
  one. A separation proof still needs witnesses against
  arbitrary coefficients and degrees in the circuit size bound.
  [Chain construction](../PvsNP/SAT/CircuitNegationWitness.lean) · [Negation bound](../PvsNP/Circuits/NegationLowerBound.lean) · [Additive gate bound](../PvsNP/SAT/CircuitNegationSize.lean)
- Input relevance counts at most `n` positions. An increasing input chain
  has at most `n` strict steps, since each changes a bit from zero to one
  permanently.
  These measures yield a linear binary-gate term and a logarithmic
  NOT-gate term in this approach.
  [Input support](../PvsNP/Circuits/InputSupport.lean) · [Negation bound](../PvsNP/Circuits/NegationLowerBound.lean)

The clean warning-free build and fresh kernel replays of
`PvsNP.SAT.CircuitNegationSize` and `PvsNP` passed. The axiom audit checked
661 public declarations. Individual checks of the supporting private
lemmas also passed the standard allowlist.
[Verification commands](../README.md#reproduce-the-checks) · [Axiom audit](../PvsNP/Verification/Axioms.lean)

## Parity restrictions on pairs of input bits

- Distinguishing pairs by contexts that expose each coordinate individually
  was too weak to force sharing. An AND of `k` terms `(xᵢ OR sᵢ)`
  uses `2k - 1` binary gates on `2k` relevant inputs. Fixing the selectors
  can expose either member of any chosen pair of `x` wires. Requiring
  XOR or XNOR in a single context instead rules out one binary merge
  of the two selected wires.
  [One-gate obstruction](../PvsNP/Circuits/PairRestriction.lean)
- The network proof charges both canonical support and designated wires.
  Ordinary operands retain their positions, shared operands account for
  discarded designations, and an exclusive operand may move to the gate
  output. A pair of exclusive operands with a parity restriction cannot
  share that output. The proof yields `n + k ≤ binarySize + 2` for a
  circuit with `n` sensitive inputs and `k` designated coordinates.
  [Network induction](../PvsNP/Circuits/ParityBinaryLowerBound.lean)
- A first construction used nine-bit blocks with a selector literal,
  giving one designated bit per block. Two same-variable unit clauses
  give XNOR for any separation of at least five bits by choosing the
  unit width or inserting padding. For separations of one to four bits,
  the second selected bit changes the unary index and whether the next
  literal starts a new clause. This gives XOR and fills in the short
  separations, so the designated set covers a consecutive interior
  interval. The resulting total-size bound is `2 * n - 44`, with the
  earlier logarithmic NOT bound available independently.
  [Long gaps](../PvsNP/SAT/CircuitParityRestriction.lean) · [Short gaps](../PvsNP/SAT/CircuitCloseParity.lean) · [Final gate count](../PvsNP/SAT/CircuitParitySize.lean)
- The charge adds at most one designation per input. This proof gives
  a linear binary-gate lower bound. The circuit route to separation still
  requires a lower bound that exceeds every fixed polynomial at some
  input length.
  [Separation obligation](../PvsNP/Complexity/CircuitLowerBound.lean)

The pinned clean warnings-as-errors build and fresh kernel replays of
`PvsNP.SAT.CircuitParitySize` and `PvsNP` passed with `LEAN_NUM_THREADS=1`.
The allowlist audit passed for 1,079 public declarations and 41 private
parity declarations. Smoke checks covered XOR and multiplexer circuits,
and the long-gap encoding at separations of five, ten, and eleven bits.
[Reproduction commands](../README.md#reproduce-the-checks) · [Private audit commands](ProofGuide.md#auditing-private-bridge-lemmas)

## Pair restrictions over the full binary basis

- An arbitrary binary gate can itself be XOR. For the full basis,
  use both a parity restriction and a signed AND restriction on
  each designated pair. If both pins feed one gate exclusively,
  the restrictions compose that gate's one truth table with
  possibly different unary maps. Both maps must be permutations
  since both outputs are nonconstant. The parity table has an even
  number of true rows and signed AND has an odd number. Unary
  permutations preserve this parity and rule out merging the two
  pins. The earlier support balance transfers to this pair
  property with the same `n + k ≤ binarySize + 2` inequality.
  [Full-basis pair certificates](../PvsNP/Circuits/BinaryBasisPair.lean) · [Support balance](../PvsNP/Circuits/ParitySupport.lean) · [Gate lower bound](../PvsNP/Circuits/BinaryBasisLowerBound.lean)
- A fixed positive unit on the target variable turns long-gap
  XNOR into AND on the two sign pins. Changing the last fixed
  unit from negative to positive in the close XOR layout gives
  OR. Together the clauses provide both kinds of restriction
  across `n - 44` consecutive interior positions for `n ≥ 44`.
  The resulting bound is `2 * n - 46` binary gates over all
  sixteen tables.
  [Long-gap restrictions](../PvsNP/SAT/CircuitParityRestriction.lean) · [Close-gap restrictions](../PvsNP/SAT/CircuitCloseParity.lean) · [CNF-SAT bound](../PvsNP/SAT/CircuitBinaryBasisSize.lean)
- The pair certificates can coexist at size `2 * n + O(1)`.
  A forward alternating AND/OR scan `A` and its reverse `B`,
  with independent seeds and the same operation at each bit,
  can expose either selected bit in isolation at their respective
  outputs. Opposite operations permit this by fixing the seeds.
  Equal operations permit it by setting an intermediate opposite
  gate's operand to its absorbing value. The selector output
  `A XOR (s AND B)` then gives parity on the pair. Selecting
  `A` in a context with neutral fixed data gives an AND or OR
  on that same pair. The scan circuits share their data inputs
  and use two extra binary gates to combine outputs.
  [Scan construction and contexts](ProofGuide.md#pair-restrictions-over-the-full-binary-basis)
- Translating into the AND, OR, and NOT basis multiplies size by at
  most four while preserving the function. `mem_PPolyBinaryBasis_iff`
  establishes equality of the polynomial-size classes, so the
  earlier conditional circuit route to separating `P` and `NP`
  applies in the full basis.
  [Basis translation](../PvsNP/Circuits/BinaryBasisBridge.lean) · [Circuit class equivalence](../PvsNP/Complexity/BinaryBasisCircuits.lean)

The pinned clean warnings-as-errors build and fresh kernel replays of
`PvsNP.SAT.CircuitBinaryBasisSize` and `PvsNP` passed with
`LEAN_NUM_THREADS=1`. The allowlist audit passed for 1,127 public
declarations and 63 private declarations in the parity and full-basis
proofs. Executable checks compared both evaluators on all sixteen binary
truth tables and a circuit with a shared intermediate wire. The long-gap
checks exercised both CNF restrictions at separations of five, ten, and
eleven bits.
[Reproduction commands](../README.md#reproduce-the-checks) · [Private audit commands](ProofGuide.md#auditing-private-bridge-lemmas)

## Counting hard truth tables

- The finite counting argument uses an executable choice rule. Enumerate
  circuits at a given gate budget, evaluate them on every input of the
  chosen length, and select the first absent table in the fixed table
  order. Padding smaller circuits with unused constant gates makes the
  exact-size enumeration cover their functions as well. For every
  `n ≥ 5`, the budget `⌊2^n / (8 * n)⌋` leaves at least one table absent.
  [Circuit enumeration](../PvsNP/Circuits/Enumerate.lean) · [Table order](../PvsNP/Circuits/TruthTable.lean) · [Counting construction](../PvsNP/Complexity/CountingLowerBound.lean)
- `countingHardLanguage` uses this selection at each input length. On
  length `2 * m` for `m ≥ 8`, its circuit lower bound exceeds `2^m`,
  which gives `countingHardLanguage_not_mem_PPoly`. The same lengths
  have accepted inputs because the selected table differs from the
  constant false table.
  [Numerical bound](../PvsNP/Circuits/CountingBound.lean) · [Language lower bound](../PvsNP/Complexity/CountingLowerBound.lean)
- Supplying an entire selected truth table as the witness uses `2^n` bits
  for an input of length `n`. `countingHardTable_certificates_too_long`
  shows that for every Cook exponent there is an accepted input whose
  full-table witness exceeds that exponent's length bound.
  [Certificate bound](../PvsNP/Complexity/CountingLowerBound.lean)

The pinned clean build passed with warnings treated as errors. Fresh kernel
replays of `PvsNP.Complexity.CountingLowerBound` and `PvsNP` passed. The
allowlist audit passed for 688 public declarations and 15 private counting
lemmas. The build and replays used `LEAN_NUM_THREADS=1`.
[Reproduction commands](../README.md#reproduce-the-checks) · [Private audit commands](ProofGuide.md#auditing-private-bridge-lemmas)

## Padding the counting language

- For polynomially bounded injective profiles `N` with `n ≤ N n`, zero
  padding preserves `PPoly` membership in both directions. The prefix
  circuit checks the suffix on padded inputs, and the restricted circuit fixes
  the suffix to false when recovering the original inputs. In particular,
  polynomial padding preserves the counting language's circuit hardness.
  [Generic padding theorem](../PvsNP/Complexity/Padding.lean) · [Circuit wiring](../PvsNP/Circuits/InputLayout.lean)
- For general injective profiles `N` with `n ≤ N n`, the exact threshold
  for the padded counting language to be in `PPoly` is a polynomial
  bound on `2^n` in `N n`. The upper direction uses truth-table circuit
  synthesis, which spends at most `5 * 2^n` gates on the original bits,
  plus the suffix test. The lower direction transfers the counting
  bound back through the restriction. The circuit family can choose the
  original length separately for each padded length.
  [Counting and padding](../PvsNP/Complexity/CountingPadding.lean) · [Circuit synthesis](../PvsNP/Circuits/TruthTableUpperBound.lean)
- An eventual polynomial bound on the full circuit list count, or a
  polynomial bound on the truth-table list count, would put the padded
  language in `PPoly`. A polynomial bound on full-table certificates on
  accepted padded words has the same implication, because every original
  length `n ≥ 10` has an accepted word. For polynomially bounded injective
  profiles with `n ≤ N n`, each of these quantities exceeds every fixed
  polynomial bound at some relevant length. The comparison tracks the
  numbers of explicit list entries and certificate bits.
  [Enumeration and certificate bounds](../PvsNP/Complexity/CountingPadding.lean)

The pinned clean build and fresh kernel replays of
`PvsNP.Complexity.CountingPadding` and `PvsNP` passed with
`LEAN_NUM_THREADS=1`. The allowlist audit passed for 729 public
declarations and 11 private padding declarations.
[Reproduction commands](../README.md#reproduce-the-checks) · [Private audit commands](ProofGuide.md#auditing-private-bridge-lemmas)

## Certificate candidates for the counting language

- A fixed certificate supplies constant tape symbols after the separator
  in the exact Cook input. The variable bits of the instance still feed
  the circuit. A common clock based on the longest allowed input pair
  gives a single polynomial circuit bound for all certificates within
  the cap.
  [Mapped input initialization](../PvsNP/Circuits/WindowInput.lean) · [Verifier circuits](../PvsNP/Complexity/VerifierCircuits.lean)
- Disjoining over the candidates for a length costs at most a polynomial
  per list entry plus one gate. For the counting language, a correct
  verifier therefore needs lists with `2^n ≤ |C_n| * g(n)` for one
  polynomially bounded `g` at every `n ≥ 10`. The lists may be chosen
  independently at each length. The bound holds after discarding repeated
  candidates and those rejected on every length-`n` input.
  [Candidate projection](../PvsNP/Complexity/VerifierCircuits.lean) · [Counting verifier bounds](../PvsNP/Complexity/CountingVerifierBounds.lean)
- With all bounded-length certificates available, the number of candidates
  is at most `(cap n + 1) * q^(cap n)` for an alphabet of size `q`. A unary
  alphabet would leave just a polynomial factor to cover `2^n`, which
  rules out that verifier model. With `encodePair`, the cap can fall
  below `n` by at most `C + d * (Nat.log2 (n + 1) + 1)` for fixed constants `C, d`
  at `n ≥ 10`. Cook permits larger polynomial caps and other fixed
  finite certificate alphabets. A relation and verifier that decide the
  counting language within those bounds remain to be established.
  [Certificate length bounds](../PvsNP/Complexity/CountingVerifierBounds.lean) · [Cook's NP definition](../PvsNP/Complexity/Classes.lean)

The pinned clean build and fresh kernel replays of
`PvsNP.Complexity.CountingVerifierBounds` and `PvsNP` passed with
`LEAN_NUM_THREADS=1`. The allowlist audit passed for 763 public
declarations and 19 private window declarations.
[Reproduction commands](../README.md#reproduce-the-checks) · [Private audit commands](ProofGuide.md#auditing-private-bridge-lemmas)

## SAT decision oracles and witness search

- Prepending one unit clause per fixed bit makes the SAT oracle answer
  whether a prefix extends to a satisfying assignment of the original
  word. A malformed word still produces a malformed query. The search
  uses one initial decision followed by at most one query per assignment
  bit, trying false and taking true if false cannot extend. On `n`-bit
  inputs the returned witness has `n` bits, and the run makes at most
  `n + 1` calls on words of length at most `n + n * (n + 5)`.
  [Query encoding](../PvsNP/SAT/SearchOracleQuery.lean) · [Search and bounds](../PvsNP/SAT/OracleSearch.lean)
- If a Cook SAT decider is available, its run at the specified clock
  implements each oracle answer. For fixed clock exponent, the sum of
  query lengths and allotted decider ticks is polynomially bounded.
  The returning-call construction below accounts for physical
  transitions with a prepared query and restores the head to the
  protected origin.
  [Decider clock and charge](../PvsNP/SAT/OracleSearch.lean) · [Returning calls](#returning-cook-calls)
- For nonuniform circuits, the decision family supplies a circuit at
  each query length. A circuit can wire one step's chosen bit into the
  next query and use the decision on the original word for its success
  output. `CNFSAT_mem_PPoly_iff_exists_witnessCircuits` proves that
  polynomial-size decision circuits exist exactly when polynomial-size
  circuits can give the success bit and output a satisfying assignment
  on yes inputs. The reverse direction uses the success output.
  [Query wiring](../PvsNP/Circuits/PrefixQueryWiring.lean) · [Witness circuit equivalence](../PvsNP/SAT/SearchCircuits.lean)

The pinned clean build and fresh kernel replays of
`PvsNP.SAT.SearchCircuits` and `PvsNP` passed with `LEAN_NUM_THREADS=1`.
The allowlist audit passed for 829 public declarations and 24 private
search declarations. Six small executable checks covered assignment
recovery, rejection, malformed input, and the witness-circuit outputs.
[Reproduction commands](../README.md#reproduce-the-checks) · [Private audit commands](ProofGuide.md#auditing-private-bridge-lemmas)

## Returning Cook calls

- One tape with a finite product alphabet carries the child's scratch
  symbols, the controller's protected symbols, and one origin marker.
  The side bit lets the finite control choose the direction back to the
  origin after the child halts. The scratch track simulates the child
  exactly through its first halt, while the protected symbols and
  marker retain their absolute coordinates.
  [Call machine](../PvsNP/TuringMachine/TrackCall/Core.lean) · [Tape tracks](../PvsNP/TuringMachine/TrackCall/Tracks.lean) · [Simulation](../PvsNP/TuringMachine/TrackCall/Simulation.lean)
- After `t` child transitions from the origin, the head is at distance
  at most `t`. Rewinding takes the distance plus two transitions and
  preserves every physical symbol from the child's final tape.
  From a prepared query, a child with a `T`-tick halt bound returns
  in at most `2 * T + 2` transitions. The controller resumes the
  false or true continuation on the marked cell. Including the
  invocation tick gives `2 * T + 3` when that tick leaves the query
  ready at the origin.
  [Rewind](../PvsNP/TuringMachine/TrackCall/Rewind.lean) · [Controller](../PvsNP/TuringMachine/TrackCall/Controller.lean) · [Return bounds](../PvsNP/TuringMachine/TrackCall/Return.lean)
- `search_queries_have_returning_calls` matches each prepared SAT
  query's return label to its exact clocked answer. For `n` input
  bits and `B = n + n * (n + 5)`, the physical calls and returns
  together take at most `(n + 1) * (2 * (B^k + k) + 2)` transitions.
  The bound starts from a separate prepared configuration for each
  query. `prepareTape` computes this tape description outside the
  Cook transition count. The scratch loader below supplies a charged
  preparation step from a protected query layout.
  [Prepared SAT calls](../PvsNP/SAT/OracleCalls.lean) · [Tape preparation](../PvsNP/TuringMachine/TrackCall/Tracks.lean) · [Scratch loader](#loading-scratch-from-a-protected-source)

The pinned clean build and fresh kernel replays of `PvsNP.SAT.OracleCalls`
and `PvsNP` passed with `LEAN_NUM_THREADS=1`. The allowlist audit passed
for 872 public declarations and 17 private returning-call declarations.
Five small executable cases checked halts on both sides of the origin,
returns after crossing it, and a compiled controller's return label.
[Reproduction commands](../README.md#reproduce-the-checks) · [Private audit commands](ProofGuide.md#auditing-private-bridge-lemmas)

## Loading scratch from a protected source

- A protected window gives the loader two boundary marks and one
  target scratch symbol per cell. A concrete finite controller reaches
  the left edge and turns in `L + 2` ticks, copies query symbols and
  writes blanks in `L + R + 1` ticks, then returns to the origin and
  enters the call in `R + 1` ticks. The `2 * (L + R) + 4` transitions
  replace the old scratch contents and preserve the protected track.
  [Loader rules and invariants](../PvsNP/TuringMachine/TrackCall/Loader/Core.lean) · [Concrete controller](../PvsNP/TuringMachine/TrackCall/Loader/Program.lean) · [Loader composition](../PvsNP/TuringMachine/TrackCall/Loader/Load.lean)
- A child that takes at most `T` ticks from the origin leaves scratch
  cells at distance at least `T` intact, and the return preserves
  all symbols. When the query has at most `R + 1` symbols, the
  child clock fits both sides of the window, and scratch starts blank
  outside it, `run_load_call` returns the correct answer at the
  origin in at most `2 * (L + R) + 2 * T + 6` ticks. The protected
  track and blank exterior remain ready for reuse.
  [Simulation](../PvsNP/TuringMachine/TrackCall/Simulation.lean) · [Return and exterior preservation](../PvsNP/TuringMachine/TrackCall/Return.lean) · [Workspace reuse](../PvsNP/TuringMachine/TrackCall/Loader/Load.lean)
- With `B = n + n * (n + 5)`, a symmetric workspace of radius
  `B + (B^k + k) + 1` fits every recorded SAT query and the
  decider's clock. `search_query_has_loaded_call` verifies the
  load and return for each supplied protected layout.
  `loadedSearchCalls_polynomiallyBounded` budgets up to `n + 1`
  such calls for fixed `k`. In-place query edits supply the next
  protected word for each trial.
  [SAT workspace bounds](../PvsNP/SAT/OracleWorkspace.lean) · [Query iterations](#editing-and-reusing-the-sat-query-buffer)

The pinned clean build and fresh kernel replays of
`PvsNP.SAT.OracleWorkspace` and `PvsNP` passed with `LEAN_NUM_THREADS=1`.
The allowlist audit passed for 897 public declarations and 10 private
workspace declarations. Four small executable checks covered the initial
copy, the correct return label, and a second load that cleared scratch
data left by the first call.
[Reproduction commands](../README.md#reproduce-the-checks) · [Private audit commands](ProofGuide.md#auditing-private-bridge-lemmas)

## Editing and reusing the SAT query buffer

- On a well-formed formula word, appending the prefix clauses preserves
  the SAT answer and length of the earlier prepended queries. The editor
  changes only the new unit clause's sign when committing an answer.
  `QueryBuffer` verifies the exact bits and marker positions after
  both edits. `queryTail` depends only on the original length and
  the number of appends, so a fixed schedule of unary stops serves
  every assignment path.
  [Append encoding](../PvsNP/SAT/AppendQuery.lean) · [Buffer invariant](../PvsNP/SAT/QueryBuffer.lean) · [Stop schedule](../PvsNP/SAT/QueryIndices.lean)
- The physical append scans to the old terminator and writes the trial
  clause. The loader transfers the query to scratch, the decider
  returns, and the commit writes the opposite of its answer at the
  pending sign. `run_sat_query_iteration` verifies that the new
  prefix remains feasible and gives a polynomial budget per stage
  for a fixed decider exponent.
  [Physical append](../PvsNP/TuringMachine/TrackCall/QueryEdit/Append.lean) · [Physical commit](../PvsNP/TuringMachine/TrackCall/QueryEdit/Commit.lean) · [SAT iteration](../PvsNP/SAT/QueryIterationSAT.lean)
- The finite cyclic controller returns to its first scan after
  each commit. `run_sat_query_loop` starts from a prepared,
  well-formed SAT source with a feasible prefix, immutable stops
  and workspace boundaries, and a blank scratch exterior.
  One continuing run reaches a stage boundary with an `n`-bit
  satisfying assignment encoded in the query buffer.
  `run_loopIterationProgram` starts the concrete controller with
  an empty prefix on a prepared satisfiable input and observes its
  first scan state after `n` stages. The proof counts those stages
  outside the controller. An end-to-end Cook search transducer still
  needs automatic initialization, a failure path for malformed and
  unsatisfiable inputs, a tape-based stopping test, and canonical
  output and halting.
  [Cyclic controller](../PvsNP/SAT/QueryIterationProgram.lean) · [Continuing run](../PvsNP/SAT/QueryLoop.lean) · [Concrete specialization](../PvsNP/SAT/QueryLoopProgram.lean)

The pinned clean build with warnings as errors and fresh kernel replays
of `PvsNP.SAT.QueryLoopProgram` and `PvsNP` passed with
`LEAN_NUM_THREADS=1`. The allowlist audit passed for 995 public
declarations and 32 private declarations used by the query edits and
controller. Six small executable checks with constant-answer child
machines covered trial append, both sign commits, scratch loading, and
two consecutive stages with unchanged stop marks and blank exterior.
[Reproduction commands](../README.md#reproduce-the-checks) · [Private audit commands](ProofGuide.md#auditing-private-bridge-lemmas)

## Crossing-sequence time lower bound

- Hennie's splicing theorem motivates a direct time argument for
  Cook's single-tape model. The absolute-coordinate tape follows
  the exact Cook start and tick. At a fixed cut, matching crossing
  transcripts of two rejecting runs let their selected left and
  right tape parts replay to a rejecting halt.
  [Hennie, Theorem 1](https://www.eecs.tufts.edu/~aloupis/comp260/lectures/hennie-1965.pdf) · [Cook coordinates](../PvsNP/TuringMachine/Crossing/Absolute.lean) · [Splice proof](../PvsNP/TuringMachine/Crossing/Splice.lean)
- The two CNF blocks encode tables addressed by `r` variables
  and separated by a common run of tautological clauses.
  A satisfying assignment selects an address where the table
  bits differ. The equal-table words reject, so splicing two
  distinct equal-table words forces a different answer. This
  gives one distinct transcript per table at each padding cut.
  Using unit clauses for an accepting-equality test would carry
  only `r` bits in `Θ(r²)` encoded bits because the variable
  names are unary. The table construction carries `2^r` bits
  in blocks of length `O(2^r * (r + 1)^2)`.
  [CNF family and padding](../PvsNP/SAT/CrossingFamily.lean) · [Per-cut distinction](../PvsNP/SAT/CrossingTimeLowerBound.lean)
- Counting short transcripts and averaging over inputs yields
  one equal-table input with large total transcript length.
  Each physical transition crosses at most one selected cut.
  For `n = 10 * blockWidth r + 1`, any common halt bound `t`
  on the rejecting family satisfies
  `n^2 ≤ 121 * (2 + (Nat.log2 n + 1) * (Nat.log2 n + 3)) * (Nat.card M.State + 3) * (t + n)`.
  For each fixed correct decider, this yields a near-quadratic
  lower bound at those lengths. `cnfsat_no_linear_clock` proves that
  each proposed bound `C * (n + 1)` fails on some input.
  The chosen transcript threshold is at most `2^r`, and the cut
  count is at most `n`. The estimate leaves quadratic and higher
  polynomial clocks consistent with the lower bound.
  [Averaging](../PvsNP/TuringMachine/Crossing/Counting.lean) · [Transition budget](../PvsNP/TuringMachine/Crossing/Time.lean) · [Time lower bound](../PvsNP/SAT/CrossingTimeLowerBound.lean)

The pinned clean build with warnings as errors and fresh kernel replays
of `PvsNP.SAT.CrossingTimeLowerBound` and `PvsNP` passed with
`LEAN_NUM_THREADS=1`. The axiom audit passed for 1,047 public declarations
and 33 private crossing declarations. Eighteen executable checks on a
small Cook comparator covered crossing into both halt states, unchanged
transcripts after halting, and mixed input tapes. Separate CNF encoding
checks covered equal and unequal tables and padding cuts at both ends
and in the interior.
[Reproduction commands](../README.md#reproduce-the-checks) · [Private audit commands](ProofGuide.md#auditing-private-bridge-lemmas)

## Crossing-sequence bound with multiple bits per address

- The one-bit construction carries `2^r` bits in a block of width
  `O((r + 1)^2 * 2^r)`. The added construction carries `r * 2^r` bits
  within the same order of width. At each address, the two clauses
  list a choice of payload variable for each of the `r` bit slots.
  The shared at-most-one header requires both clauses at the chosen
  address to use the same true payload variable. With the right table
  complemented, that choice certifies a differing bit. One positive
  unit on a fresh high index normalizes each block width without
  changing the test. The `2^(r * 2^r)` tables now distinguish
  `Θ(n / log n)` bits of information per padding cut, improving
  the earlier `Θ(n / (log n)^2)` from the one-bit family.
  [Payload clauses](../PvsNP/SAT/CrossingPalette.lean) · [Fixed-width blocks](../PvsNP/SAT/CrossingPaletteBlocks.lean)
- `separated_crossing_clock_lower_bound` provides the shared
  splice and averaging argument. At each `n = 10 * width r + 1`,
  with `width r = 48 * (r + 1)^2 * 2^r` and `r ≥ 1`,
  `cnfsat_square_length_le_log_crossing_time` bounds any common
  halting budget on the equal-table words.
  `exists_rejecting_word_with_log_crossing_time` chooses one
  `w ∉ CNFSAT` of length `n` such that every halting budget `t`
  satisfies
  `n^2 ≤ 11616 * (Nat.log2 n + 1) * (Nat.card M.State + 3) * (t + n)`.
  For a fixed machine this gives an `Ω(n² / log n)` worst-case
  bound at those lengths.
  [Generic splice bound](../PvsNP/SAT/CrossingTimeLowerBound.lean) · [One-logarithm bound](../PvsNP/SAT/CrossingPaletteTime.lean)
- `separated_word_crossing_clock_lower_bound` counts cuts in any
  shared middle word. A fresh positive unit fills this region to
  the exact remaining length. Choosing the last palette base length
  up to `N` loses at most a factor of eight in length.
  `exists_rejecting_word_with_log_crossing_time_at_every_length`
  now gives a rejecting input at each exact length `N ≥ 3841`
  and an explicit time inequality for every budget by which it halts.
  [Exact-length construction](../PvsNP/SAT/CrossingPaletteBlocks.lean) · [Worst-case bound](../PvsNP/SAT/CrossingPaletteWorstCase.lean)
- The one-bit family also gives a separate clock statement.
  `cnfsat_no_subquadratic_rational_clock` gives a word outside
  `CNFSAT` for every proposed `C, e, d` with `1 ≤ d` and
  `e < 2 * d`. Each halting budget `t` on that word satisfies
  `C * (w.length + 1)^e < t^d`. A quadratic clock remains
  compatible with these lower bounds.
  [Rational exponent bound](../PvsNP/SAT/CrossingPowerBound.lean)
- An informal counting argument suggests a limit on information
  available from independent counts at clause boundaries. For a
  well-formed prefix of at most `n` bits, remove tautologies and
  duplicates, then sort the remaining literals and clauses. An
  index `i` costs `i + 3` bits when present and can appear positively,
  appear negatively, or be absent in a canonical clause. The weighted
  product `x^(-s) * ∏ᵢ (1 + 2 x^(i+3))` bounds the count of canonical
  clauses of width at most `s`. Taking `x = exp(-1 / √s)` gives
  `2^(O(√s))` candidates.
  A threshold of order `(log n)^2` with a small enough constant
  leaves at most `√n` cheap clauses to record as a subset. There
  are `O(n / (log n)^2)` expensive clauses, each described with
  `O(√s)` bits for its width and rank. Cauchy–Schwarz bounds the
  summed description length by `O(n / log n)`. These descriptions
  preserve satisfiability under every shared continuation at the
  next clause boundary. Formalizing this proposed per-cut bound
  would require canonicalization, weighted partition counting,
  and a connection from continuation equivalence to the crossing
  family count.
  [Unary encoding](../PvsNP/SAT/BinaryEncoding.lean) · [Per-cut splice](../PvsNP/SAT/CrossingTimeLowerBound.lean)

The pinned clean build and fresh kernel replays of
`PvsNP.SAT.CrossingPaletteWorstCase`, `PvsNP.SAT.CrossingPowerBound`, and
`PvsNP` passed with `LEAN_NUM_THREADS=1`. The allowlist audit passed for
1,176 public declarations and 26 private crossing declarations. Concrete
checks covered exact lengths 3841, 3842, 3843, and 3848, including an
equal-table rejection at 3842 and a mixed-table acceptance at 3843.
[Reproduction commands](../README.md#reproduce-the-checks) · [Private audit commands](ProofGuide.md#auditing-private-bridge-lemmas)

## Minimum circuit size and a streaming merge

The construction follows the prefix-circuit invariant of McKay, Murray, and
Williams, using one row per update. The entire prefix is constrained at every
step. A circuit for the full truth table would also satisfy any local merge
request made along the scan. Lean verifies this invariant for circuits over
AND, OR, NOT, and constants, with the requested budget counting all gates.
[McKay, Murray, and Williams, Section 4](https://people.csail.mit.edu/rrw/MCSP-MKTP-stoc19.pdf) · [Streaming proof](../PvsNP/MCSP/Streaming.lean)

The merger's existential witness is a binary circuit description of at most
`2w + s(3 + 2w)` bits, with `w = log₂(n+s) + 1`. Its universal check ranges
over the `n`-bit rows. The violation circuit has size linear in `n` and the
gate counts of the old and candidate circuits. The scanner retains only the
current circuit and row count between requests. Its executable reference
merger enumerates bounded circuits and is used for correctness checks.
[Description and round trip](../PvsNP/Circuits/Description.lean) · [Witness predicate](../PvsNP/MCSP/MergeWitness.lean) · [State and request counts](../PvsNP/MCSP/StreamResources.lean)

The violation circuit now has a Tseitin encoding in the project's exact
binary CNF-SAT language. A satisfying assignment gives a violating row and
vice versa. A separate witness search reduces a merge to at most one more
prefix feasibility query than the padded description length. The feasibility
predicate itself has a bounded binary witness checked against every row.
Under `P = NP`, bounded universal verification yields a Cook decider when
the corresponding polynomial-time Cook verifier for violations is supplied.
[Violation CNF](../PvsNP/MCSP/ViolationCNF.lean) · [Prefix feasibility](../PvsNP/MCSP/MergeWitness.lean) · [Cook complementation](../PvsNP/Complexity/Complement.lean)

The next upper-bound obligation is a uniform Cook implementation of prefix
feasibility under `P = NP`, including the encoding, validity checks, and
bounded witness projection. A candidate request format uses unary `n` and
gate cap, a fixed-width row counter, and the circuit and prefix codes. The
row comparison can scan the counter bits directly. Expanding a row index
to unary could cost `2^n` steps on a short request. The verifier must reject
malformed instance–certificate pairs and the two bounded projections must
use the same binary request representation. The scan currently takes `n` and
the gate cap as parameters. A machine-level theorem must account for how it
obtains these parameters before processing the table. Applying the magnification criterion
of Cheraghchi, Hirahara, Myrisiotis, and Yoshida also requires a charged
simulation with a separate one-way read-only input tape, an exact connection
to the gate basis and threshold in that criterion, and a sufficient lower
bound there. Their nearly quadratic lower bound uses a gate threshold close
to `2^n` in the exponent. The magnification premise needs a sufficiently
small positive exponent in that threshold. The project's CNF-SAT crossing
argument charges communication across cuts of a writable tape holding the
input. [Cook tape bound](../PvsNP/SAT/CrossingPaletteWorstCase.lean) · [Theorems 1–2 and the machine model](https://drops.dagstuhl.de/storage/00lipics/lipics-vol187-stacs2021/LIPIcs.STACS.2021.23/LIPIcs.STACS.2021.23.pdf)

The pinned clean build and fresh kernel replays of `PvsNP.MCSP.MergeWitness`,
`PvsNP.MCSP.StreamResources`, `PvsNP.MCSP.ViolationCNF`, and `PvsNP` passed
with `LEAN_NUM_THREADS=1`. The axiom allowlist held for 1,298 public entries
and 30 private declarations from the new modules. Executable checks matched
streaming and direct enumeration on every truth table of arity zero through
two at gate budgets zero through two. Other checks covered invalid table
lengths, malformed witnesses, prefix violations, and early failure.
[Reproduction commands](../README.md#reproduce-the-checks) · [Private audit commands](ProofGuide.md#auditing-private-bridge-lemmas)

## A binary checker for merge-prefix feasibility

The request encoding fixes the previously unspecified arity, cap, counter,
old circuit, and prefix layout. The row and candidate quantifiers now have
exact Cook certificate bounds. `mergePrefixLanguage_mem_P_of_p_eq_np` reduces
the conditional upper bound to the binary language of
`checkPackedMergePrefixViolation`. The last remaining checker hypothesis
is membership in Cook's `P`. A generic paired-cell simulation provides the
needed transport from binary checking words to the separator alphabet, with
at most two physical transitions per simulated transition on the packed
word. [Cook's verifier definition](https://www.claymath.org/wp-content/uploads/2022/06/pvsnp.pdf) · [Packed pairs](../PvsNP/Complexity/PackedPairs.lean) · [Exact feasibility theorem](../PvsNP/MCSP/PrefixViolationLanguage.lean)

Register proofs now cover scanning a complete packed pair and reading or
comparing fields at prepared offsets. Canonical packed-pair syntax belongs
to `P`, and the included offset theorems locate the request, candidate, and
certificate bits after nesting. The row counter is compared bitwise.
The logarithmic-width gate fields can be converted to bounded unary values
for indexed lookups. The wire-trace proof identifies the exact check for
each gate, including shared references and rejects incorrect trace lengths.
[Packed pair decider](../PvsNP/TuringMachine/Registers/PackedPairDecision.lean) · [Nested offsets](../PvsNP/Complexity/PackedOffsets.lean) · [Fixed-width gate field](../PvsNP/TuringMachine/Registers/BinaryField.lean) · [Binary comparison](../PvsNP/TuringMachine/Registers/BinaryCompare.lean) · [Wire trace](../PvsNP/Circuits/WireTrace.lean)

Evaluating a general circuit from a row can require keeping many wire
values available. A finite number of unary registers grows each value by at
most the instruction count, and the register program can read its input
but cannot read back its output. Storing the whole wire table in one unary
counter can take exponentially many instructions. The trace certificate
stores the wire table in the input for indexed reads. Lean proves that the trace
projection gives exactly the same bad queries and that the entire
certificate is at most as long as the query.
[Register semantics](../PvsNP/TuringMachine/Registers/Program.lean) · [Trace certificate relation](../PvsNP/MCSP/TraceViolationLanguage.lean)

The full trace checker needs a uniform loop over the gate records, reads of
the supplied wire bits, and validation of the unary headers, padding,
prefix, row, and trace layout. In the outer binary word, consecutive
request and candidate data bits are four cells apart. Consecutive
certificate bits are two cells apart. The existing fixed-width register
fragments take contiguous fields, so their use here needs a strided read
or a charged copy. The polynomial register bound must account for
malformed inputs as well. Under `P = NP`, this single checker gives a
Cook feasibility decider. The decider's ticks per recorded stream query
have a proved polynomial bound in the arity and cap. Building and copying
the canonical requests on a physical work tape still needs a clocked
implementation. [Exact trace checker obligation](../PvsNP/MCSP/VerifierProgram.lean) · [Per-query ticks](../PvsNP/MCSP/ClockedPrefixOracle.lean)

The pinned clean build and fresh kernel replays of `PvsNP.MCSP.ClockedPrefixOracle`,
`PvsNP.MCSP.VerifierProgram`, `PvsNP.TuringMachine.Registers.PackedPairDecision`,
and `PvsNP` passed with `LEAN_NUM_THREADS=1`. The axiom allowlist held for
1,422 public entries and 98 private declarations. Executable checks included
121 separator-alphabet words for the paired-input simulation, 125 triples
of packed fields for the nested offsets, and valid and altered wire traces.
[Reproduction commands](../README.md#reproduce-the-checks) · [Private audit commands](ProofGuide.md#auditing-private-bridge-lemmas)

## Counted parsing and gate verification

The exact executable checker `checkPackedMergePrefixTraceViolation` is now
connected to the certificate relation on every binary input. The route
through a counted register program has a fixed Boolean target. The framing
fragment checks the outer and inner pairs on the raw input, with separate
validity flags. The header scanner consumes both unary fields directly
through the packed tags, and the width program computes the same
logarithmic field size as the codec.
[Executable specification](../PvsNP/MCSP/TraceChecker.lean) · [Counted framing](../PvsNP/MCSP/NestedPairRegister.lean) · [Header scans](../PvsNP/MCSP/RequestHeaderRegister.lean) · [Field width](../PvsNP/TuringMachine/Registers/FieldWidth.lean)

Reading the gate records from the last gate to the first keeps a single
reverse cursor. Each iteration reads the two operands and opcode, validates
the record, reads its needed trace bits, and checks its output wire. The
trace carries all gate values, so a gate can be checked at its own position
in any scan order. The loop's count is the number of failed gates and its
instruction bound is polynomial in the input length, width, and gate count.
The layout lemmas locate the actual circuit records and trace bits in
nested packed words, including the old circuit embedded in the request.
For the candidate, the packed setup theorem derives the loop preconditions
from the actual packed input, its checked trace length, and seeded registers.
[Physical layout](../PvsNP/MCSP/TraceLayout.lean) · [Packed setup](../PvsNP/MCSP/PackedGateBlock.lean) · [Counted gate loop](../PvsNP/MCSP/GateBlockRegister.lean)

The remaining register proof must validate the request and candidate sizes,
output fields, padding, requested prefix, seen counter, and certificate
extent. It must connect those checks to the gate loop and the row and
output tests, and emit the expected answer on all rejection paths. Query
validation happens separately from trace validation. A malformed outer
pair rejects. A valid outer pair containing a bad query accepts precisely
the empty certificate. A valid query with a bad trace rejects. The gate
loop starts with prepared counts, offsets, and scratch registers.
[Open whole-program hypothesis](../PvsNP/MCSP/VerifierProgram.lean)

The gate loop uses one failure count for invalid records and inconsistent
trace bits. With an empty certificate, there are no trace bits to read,
and the answer depends only on query validity. The empty-certificate path
therefore needs a structural record check using the opcode and operand
fields. With a nonempty certificate, either kind of failure rejects.
[Malformed-query branch](../PvsNP/MCSP/TraceChecker.lean) · [Gate format](../PvsNP/Circuits/DescriptionLayout.lean)

The pinned clean build and fresh kernel replays of
`PvsNP.MCSP.NestedPairRegister`, `PvsNP.MCSP.GateBlockRegister`,
`PvsNP.MCSP.VerifierProgram`, and `PvsNP` passed with `LEAN_NUM_THREADS=1`.
The axiom audit covered 1,574 public entries and 212 private declarations
and found only `propext`, `Classical.choice`, and `Quot.sound`. Executable
checks covered correct and altered wire traces, an invalid opcode, zero
gates, and malformed pairs with empty or nonempty certificates.
[Reproduction commands](../README.md#reproduce-the-checks) · [Private audit commands](ProofGuide.md#auditing-private-bridge-lemmas)

## Structural validation without a trace

The empty-certificate branch can use the same query validity check as the
nonempty branch. Lean decomposes the request into bounded fields and proves
that successful splitting depends only on the unary header terminators and
two body-length comparisons. The count and width arithmetic uses unary
values bounded by the request length. The counted length check computes
both body bounds and the prefix length. Zero failures is exact for the
request split and the expected candidate length when both headers are
valid. The seen field stays binary. Its highest bit may be set only when
all lower bits are zero.
[Request split](../PvsNP/MCSP/RequestLayout.lean) · [Counted layout arithmetic](../PvsNP/MCSP/CircuitLayoutRegister.lean) · [Counted length check](../PvsNP/MCSP/RequestShapeRegister.lean) · [Counted seen check](../PvsNP/MCSP/SeenFieldRegister.lean)

The circuit decoder now has an exact local characterization on arbitrary
padded words. A structural gate scan validates opcodes, earlier-wire
references, and unused operands without reading a trace. The complete
prepared-description scan combines this loop with output-field decoding
and zero-padding checks. Its final output range and failure counts give
exactly the padded decoder predicate. Count parsing is a separate bounded
scan so a rejected count never needs an output or padding address.
[Padded decoder](../PvsNP/MCSP/DescriptionValidation.lean) · [Gate validation](../PvsNP/MCSP/PackedStructureBlock.lean) · [Prepared scan](../PvsNP/MCSP/PaddedDescriptionRegister.lean)

The empty certificate succeeds precisely for a structurally invalid packed
query. An accepted certificate for a valid query has exactly
`3 * arity + oldCount + newCount + 3` bits. The layout theorem isolates input bits,
gate checks, output claims, and the row comparison so that each can be
connected to counted reads.
[Empty certificate](../PvsNP/MCSP/TraceQueryLayout.lean) · [Certificate layout](../PvsNP/MCSP/TraceCertificateLayout.lean)

The remaining verifier work is to compute the forward and reverse cursors
from the counted headers and lengths, branch before reads that would
exceed the input, sequence the old and candidate checks, and finish the
nonempty-certificate checks and final Boolean output. The separate one-way
input tape model still needs a timed streaming controller and a lower bound
at the smaller gate budget of the magnification premise.
[Whole-program obligation](../PvsNP/MCSP/VerifierProgram.lean) · [Magnification model and threshold](https://drops.dagstuhl.de/storage/00lipics/lipics-vol187-stacs2021/LIPIcs.STACS.2021.23/LIPIcs.STACS.2021.23.pdf)

The three reverse cursors for a checked count `c` can share one subtraction
routine. For field width `w`, record span `S = 3 + 2 * w`, unpadded length
`H = 2 * w + c * S`, and padding width `P`, the logical offsets are `H - 1`,
`w + (c - 1) * S + (S - 1)`, and `H + (P - 1)` in order for the output,
gate, and padding scans. For a raw start `B` and input length `N`, each seed
is `N - 1 - (B + 4 * offset)`. The gate and padding formulas use saturating
subtraction since their zero-width loops make no reads.
[Prepared inputs](../PvsNP/MCSP/PaddedDescriptionRegister.lean) · [Counted subtraction](../PvsNP/TuringMachine/Registers/Subtract.lean)

Section 2.1 of the magnification paper counts AND, OR, and NOT gates. The
current codec also accepts constant gates. For positive arity, simulating
both constants using an input and its negation can add three shared gates.
That conversion leaves an additive gap at the threshold. An exact bridge
could instead propagate each constant through the gates, erasing folded
gates and replacing their outputs by constants or existing wires. This
would preserve the gate budget for nonconstant outputs. At positive arity
the two constant functions each need two gates in the constant-free basis,
so budgets of at least two can handle those inputs separately. This bridge
still needs a Lean proof. Theorem 2 chooses a budget exponent close to one.
Theorem 1 needs a sufficiently small exponent for a polynomial whose
degree comes from the assumed collapse.
[Gate structure](../PvsNP/MCSP/GateStructureRegister.lean) · [Sections 1.1.1 and 2.1](https://drops.dagstuhl.de/storage/00lipics/lipics-vol187-stacs2021/LIPIcs.STACS.2021.23/LIPIcs.STACS.2021.23.pdf)

The one-way input model starts with an empty work tape. The streaming
search currently takes arity and cap as parameters. A time-only simulation
could count the length while copying the input to a protected work-tape
track, then derive arity and cap and process the saved copy. It would need
to prove that the active work area can move along the saved input at a
polynomial cost per row in the local storage and update bounds. The
protected copy uses linear storage and therefore addresses the one-way
machine's time bound.
[Current stream parameters](../PvsNP/MCSP/StreamResources.lean) · [Machine definition and time simulation](https://drops.dagstuhl.de/storage/00lipics/lipics-vol187-stacs2021/LIPIcs.STACS.2021.23/LIPIcs.STACS.2021.23.pdf)

The pinned clean build and fresh replays of `PvsNP.MCSP.PaddedDescriptionRegister`,
`PvsNP.MCSP.TraceQueryLayout`, `PvsNP.MCSP.TraceCertificateLayout`, and `PvsNP`
passed with `LEAN_NUM_THREADS=1`. The audit of 1,725 public and 263 private
declarations found only `propext`, `Classical.choice`, and `Quot.sound`.
The integrated executable cases covered both circuit positions, invalid
opcodes, invalid output wires, nonzero padding, zero gates, truncated
requests, and matching and mismatching prefixes. The codec and certificate
checks also agreed on exhaustive small-word tests and bit mutations.
[Reproduction commands](../README.md#reproduce-the-checks) · [Private audit commands](ProofGuide.md#auditing-private-bridge-lemmas)

## Raw verifier entry and exact model bridges

The trace verifier now has a counted front end starting with empty
registers. It measures the input length, scans both packed pairs, and
scans the request's unary headers when the frames are valid. It then
computes both circuit widths and padded lengths and checks the body and
candidate extents. The emitted answer is already exact for a malformed
outer pair and for every framing, header, and extent failure. For the
remaining branch, the proof supplies a concrete request split and an
exactly sized candidate, with a uniform clock for the front end.
[Raw run](../PvsNP/MCSP/TraceExtentDispatch.lean) · [Conditional Cook consequence](../PvsNP/MCSP/VerifierProgram.lean)

One circuit-description program now performs its own count read, cap
branch, and offset initialization. The count scan reads the fixed header
even when its value exceeds the cap. The branch rejects that case before
any count-dependent read. Within the cap, counted saturating subtraction
sets the reverse addresses for the output, records, and padding, including
zero-gate and zero-padding cases. The final failure test is equivalent to
the exact padded-circuit predicate. The prefix comparison also computes
its own physical cursors from the ordinary lengths. The seen check uses
the measured header cursor and arity to compute its reverse position.
The base calculation links the header and extent results to both packed
circuit starts and the logical start of the requested prefix.
[Guarded padded checker](../PvsNP/MCSP/CheckedDescriptionRegister.lean) · [Description offsets](../PvsNP/MCSP/DescriptionOffsetRegister.lean) · [Prefix cursor setup](../PvsNP/MCSP/PreparedPrefixRegister.lean) · [Counter setup](../PvsNP/MCSP/PreparedSeenRegister.lean) · [Packed addresses](../PvsNP/MCSP/TraceExtentLink.lean)

The proposed constant-folding bridge is now verified. Each source wire
maps to a fixed Boolean or a live target wire. The live result evaluates
to the same function while costing at most the original AND, OR, and NOT
gates. At positive arity, Lean also proves the two-gate upper and lower
bounds for constant outputs. Consequently the exact streaming threshold
agrees with the strict binary basis for every cap at least two.
[Exact gate-basis bridge](../PvsNP/Circuits/ConstantFolding.lean) · [Threshold theorem](../PvsNP/MCSP/ConstantFreeThreshold.lean)

The one-way input model now has counted runs and an exact embedding of
Cook machines. It copies the source into blank work tape and rewinds in
`2N + 2` steps, then runs the original machine without further input
consumption. This closes the input-loading and verdict bridge for that
simulation. A near-linear clock for small circuit thresholds still needs
the local update controller and a bound on moving its work area along the
saved input.
[One-way input model and simulation](../PvsNP/TuringMachine/OneWayInput.lean) · [Magnification premise](https://eccc.weizmann.ac.il/report/2020/103/revision/1/download/)

The remaining counted verifier must link the correctly sized branch to
both raw circuit checks, the prefix and seen checks, and the certificate
row, trace, and output tests. The circuit-threshold route additionally
requires a one-way time bound for the complete streaming process and a
lower bound at the same small threshold.
[Remaining continuation](../PvsNP/MCSP/TraceExtentDispatch.lean) · [Certificate specification](../PvsNP/MCSP/TraceCertificateLayout.lean)

The pinned clean build and fresh kernel replays of
`PvsNP.MCSP.CheckedDescriptionRegister`, `PvsNP.MCSP.VerifierProgram`,
`PvsNP.TuringMachine.OneWayInput`, and `PvsNP` passed with
`LEAN_NUM_THREADS=1`. The axiom audit covered 1,869 public and 354 private
declarations and found only `propext`, `Classical.choice`, and `Quot.sound`.
Thirteen composed-entry and extent cases covered malformed inputs, the
zero cap, exact length bounds, and successful delegation. Independent
execution checks covered guarded circuit reads, the copied input and
simulated work tape, and exact evaluation through constant folding.
[Reproduction commands](../README.md#reproduce-the-checks) · [Private audit commands](ProofGuide.md#auditing-private-bridge-lemmas)

## Counted query structure and threshold arithmetic

The raw verifier now runs both padded circuit checks, the row-counter
range test, and the prefix comparison after framing and extent validation.
The measured dimensions and computed addresses feed the scans directly.
Their bounds yield one polynomial clock in the raw word length, even
when a claimed gate count is out of range. The clock proof maximizes over
the finitely many admissible parameter tuples at each length.
Malformed queries terminate with the exact empty-certificate rule.
A valid query supplies both gate counts and the retained layout.
[Uniform bounds](../PvsNP/Complexity/UniformBounds.lean) · [Raw structural verifier](../PvsNP/MCSP/StructuredVerifier.lean)

The certificate guard checks its exact length before reading the high
row bit. It emits false on invalid layout and preserves the seed values
for a valid layout. A second counted register fragment checks the input
prefix of each trace against the row, including zero arity and opposite
scan directions for the row and the trace fields.
[Certificate dispatch](../PvsNP/MCSP/TraceCertificateDispatch.lean) · [Trace input checks](../PvsNP/MCSP/TraceInputRegister.lean)

The right threshold for the uniform row argument is selected after the
polynomial is fixed. For a row bound of degree `d`, every positive
denominator `k ≥ 200d` admits an arity cutoff beyond which the total
charge fits `⌊N^(101/100)⌋`. The exact cap is `⌊2^(n/k)⌋`, expressed
by an integer root before checking the strict circuit basis.
The arithmetic argument absorbs finite initial lengths and a linear
clock on non-table lengths into the time class constant. The physical
one-way controller still needs a uniform row bound, and the lower bound
must apply to the same small gate thresholds.
[Threshold and clock](../PvsNP/MCSP/MagnificationClock.lean) · [Magnification model](https://eccc.weizmann.ac.il/report/2020/103/revision/1/download/)

The remaining certificate continuation must connect the row and trace
checks to both gate blocks, read the two output wires, compare the row
with the request counter, and emit the violation bit. The unconditional
Cook CNF-SAT time lower bound is still of order `N^2 / log N`.
[Certificate checks](../PvsNP/MCSP/TraceCertificateLayout.lean) · [Cook lower bound](../PvsNP/SAT/CrossingPaletteWorstCase.lean)

## Open question

A total deterministic Cook decider for binary CNF-SAT with a polynomial
worst-case bound would prove `P = NP`. A proof that no such decider exists
would prove `P ≠ NP`. Both directions are recorded as equivalences in
`p_eq_np_iff_CNFSAT_mem_P_verified` and `p_ne_np_iff_CNFSAT_not_mem_P`.
[Completeness](../PvsNP/SAT/Completeness.lean) · [Classes](../PvsNP/Complexity/Classes.lean)

The circuit route gives a sufficient condition for separation. For each pair
of natural numbers `C` and `d`, find an input length `n` at which every
circuit for binary CNF-SAT on `n`-bit words has strictly more than
`C * (n + 1)^d` gates. `not_mem_PPoly_iff` expresses this obligation, and
`p_ne_np_of_CNFSAT_not_mem_PPoly` gives its consequence for Cook's classes.
[Circuit lower-bound obligation](../PvsNP/Complexity/CircuitLowerBound.lean)

For the fixed counting language, the remaining obligation is to give a
certificate relation with a fixed polynomial certificate bound and a
polynomial-time Cook verifier. This would prove `countingHardLanguage ∈ NP`,
and `p_ne_np_of_countingHardLanguage_mem_NP` would then give `P ≠ NP`.
[Conditional separation](../PvsNP/Complexity/CountingLowerBound.lean) · [Cook's NP definition](../PvsNP/Complexity/Classes.lean)

The final resolution requires a fresh build, fresh kernel replay of the result
module, and a `#print axioms` audit of the result and its machine bridges.
The [root README](../README.md) gives the commands for the current milestones.
