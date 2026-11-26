# Proof guide

The reference statement is Cook's P vs. NP problem restricted to languages
over finite binary strings. The Lean development proves `P ⊆ NP`, the
Cook–Levin reduction to binary CNF-SAT, and `NPComplete CNFSAT`. The equality
question remains open. [Cook's official problem description](https://www.claymath.org/wp-content/uploads/2022/06/pvsnp.pdf)

## Reference model and classes

1. `Machine` has finite state and tape alphabets, separate halting states, and
   a two-way infinite tape. A transition writes one symbol and moves one cell.
   `appendixStart_toConfig` matches Cook's initial configuration, including
   empty input. `appendixTick_toConfig` checks the four tape-boundary cases
   and `appendixRun_toConfig` extends this to every finite execution.
   `haltsWithin_iff_firstHalt` identifies the first halting tick. [Core](../PvsNP/TuringMachine/Core.lean)
2. `P` requires acceptance exactly on the language and a halt on every input
   within `n^k + k` transitions for one fixed `k`. `mem_POver_iff_appendix`
   preserves the accepted language and the same bound under Cook's appendix
   representation. `polynomiallyBounded_iff_cook` gives the equivalent bound
   `C * (n + 1)^d`, including input lengths zero and one.
   [Classes](../PvsNP/Complexity/Classes.lean) · [Time bounds](../PvsNP/Complexity/TimeBounds.lean)
3. `NP` uses certificates of length at most `|x|^k` over a finite alphabet.
   The polynomial-time verifier decides the complete language of accepted
   `x#y` words. `splitAtSeparator_encode`, `encode_injective`, and
   `length_encode` give unique delimitation with one added symbol.
   `mem_NP_iff_exists_verifier` gives the corresponding machine formulation,
   including rejection outside the encoding range.
   [Pair encoding](../PvsNP/Complexity/PairEncoding.lean) · [Classes](../PvsNP/Complexity/Classes.lean)

## Deterministic containment

`p_subset_np` constructs a verifier that accepts precisely `x#` when the
original polynomial-time machine accepts `x`. It sweeps to the separator,
erases it, checks that the next cell is blank, and rewinds to the beginning.
The witness is the empty certificate. [Containment](../PvsNP/Complexity/Containment.lean)

- `valid_preparation` bounds this preparation by `2 * |x| + 4` transitions.
  `lift_tick` and `lift_run` simulate the original execution one transition
  at a time.
- `run_missing_separator` and `run_nonempty_certificate` reject inputs outside
  the checking relation. `verifier_decides` identifies the accepted language
  on all inputs.
- `verifier_polyTime` bounds preparation by `2 * n + 4` on an encoded input
  of length `n` and simulation by `n^k + k`. The polynomial-bound bridge
  puts the total in Cook's form.

## Polynomial-time many-one reductions

`PolynomialTimeMap` requires a Cook machine that halts with the output
word on its tape in canonical input position. `outputsAt_firstHalt` finds
the first successful halt with that output. `output_length_le` bounds the
canonical output length by `n + 2 * t` after `t` transitions on input length
`n`. [Transducer](../PvsNP/TuringMachine/Transducer.lean) · [Output bound](../PvsNP/TuringMachine/OutputBound.lean)

The two-machine construction embeds both tape alphabets into one alphabet
that shares the blank and binary input symbols. The first machine's accepting
transition enters the second machine's initial state. `prepend_halt` and
`prepend_output` verify the executions on the shared tape. If the first
machine has bound `A(n)` and the second has bound `m^d + d`,
`prepend_polyTime` bounds the composite by `A(n) + (n + 2 * A(n))^d + d`.
[Shared alphabet](../PvsNP/TuringMachine/SharedAlphabet.lean) · [Reductions](../PvsNP/Complexity/Reductions.lean)

`PolynomialTimeMap.comp` and `PolynomiallyReducesTo.trans` establish
composition. `PolynomiallyReducesTo.mem_P` shows that the preimage of a
language in `P` under a polynomial-time reduction is in `P`.
`NPComplete.of_reduction` and `NPComplete.p_eq_np_iff_mem_P` give the
corresponding completeness consequences. [Reductions](../PvsNP/Complexity/Reductions.lean)

## Verifier tableaux and binary CNF

1. `windowRun_start_state` reproduces the verifier's state through time `T`
   in a finite window of `2 * T + 1` cells. The head starts at the center and
   moves at most one cell per transition. [Tape window](../PvsNP/CookLevin/TapeWindow.lean)
2. `isInitialCellBlock_iff_exists_certificate` and `sat_initialClauses_iff`
   identify the first tableau row. Its tape contains the instance, separator,
   a certificate of permitted length, and blank padding. Adjacent padding
   constraints rule out gaps. [Initial tape](../PvsNP/CookLevin/InitialTape.lean) · [Verifier tableau](../PvsNP/CookLevin/VerifierTableau.lean)
3. `sat_stepClauses_iff` forces each consecutive row to follow the verifier's
   transition. The current state, head, and scanned symbol select the update.
   Other tape cells retain their symbols. `satisfiable_verifierFormula_iff`
   connects a satisfying tableau to a certificate accepted by the verifier.
   [Tableau](../PvsNP/CookLevin/Tableau.lean) · [Verifier tableau](../PvsNP/CookLevin/VerifierTableau.lean)
4. `Atom.name_injective` gives distinct bounded variable indices.
   `decode_eq_some_iff` characterizes complete binary formula words.
   `length_binaryVerifierMap_le` uses the clause and index bounds to count
   the entire output, including names in unary. `mem_NP_has_binaryCNF_map`
   combines membership equivalence with polynomially bounded output length.
   [Variable names](../PvsNP/CookLevin/VariableNames.lean) · [Tableau size](../PvsNP/CookLevin/Size.lean) · [Binary encoding](../PvsNP/SAT/BinaryEncoding.lean) · [Binary reduction](../PvsNP/CookLevin/BinaryReduction.lean)

## Generating the exact binary tableau

1. `finiteTable_verifierFormula` replaces states, tape symbols, and certificate
   letters by indices and checks the resulting clause sequence. The indexed
   machine transition agrees with one window step by
   `finiteTable_windowAdvance`. `finiteTable_binaryVerifierMap` proves equality
   after naming variables and encoding the clauses. The bridge
   `binaryTableauxPolyTime_of_indexed` transfers the polynomial-time machine
   construction for fixed indexed tables to `BinaryTableauxPolyTime`.
   [Finite table](../PvsNP/CookLevin/Generator/FiniteTable.lean)
2. `emitFormula_prepend` produces the canonical formula word when each
   successive emitted bit is prepended to the output. `length_schedule` counts
   one emission per encoded bit. The schedule traverses clauses and literals
   in reverse and emits the unary indices with their delimiters in reverse
   order as well. `foldVerifierClauses_eq` gives the same clause sequence
   through descending loops over the time, state, head, cell, symbol, and
   certificate indices. `emitVerifier_prepend` composes the clause traversal
   with bit emission to produce the exact indexed word.
   [Serialization](../PvsNP/CookLevin/Generator/Serialization.lean) · [Traversal](../PvsNP/CookLevin/Generator/Traversal.lean)
3. `run_setup` frames a binary input in `x.length + 4` ticks and leaves the head
   at the boundary of an empty register area. `Represents` gives each lane a
   run of true bits, followed by false bits. `run_increment` and
   `run_decrement` perform the physical updates. `Represents.increment` and
   `Represents.decrement` check the numerical updates and the preservation of
   all other lanes. [Setup](../PvsNP/TuringMachine/Registers/Setup.lean) · [Increment](../PvsNP/TuringMachine/Registers/Arithmetic.lean) · [Decrement](../PvsNP/TuringMachine/Registers/DecrementCorrectness.lean)
4. `run_cursor_first`, `InputLayout.run_next`, and `InputLayout.run_reset`
   relate the tape mark to a bit index in the reversed input.
   `run_emitBit` preserves the framed input and register region, appending to
   the list of bits stored nearest the sentinel first. `run_finish` erases the
   input, markers, and registers, leaving the reversed emission list on an
   otherwise blank tape with the head at its start.
   [Input layout](../PvsNP/TuringMachine/Registers/InputLayout.lean) · [Emission](../PvsNP/TuringMachine/Registers/Output.lean) · [Cleanup](../PvsNP/TuringMachine/Registers/Finish.lean)
5. `control` compiles a finite register program into a single-tape machine.
   `Matches.step` proves each transition between program labels preserves the
   abstract state. `outputsAt_of_run` composes the tape steps and gives a bound
   of `n + 4 + s * (2 * n + 3 * s + 6)` ticks for an input of length `n` and
   a successful abstract run of `s` instructions, including halt.
   `polynomialTimeMap_of_run` then transfers any worst-case polynomial
   instruction bound. `binaryTableauxPolyTime_of_registers` applies the transfer
   to the complete tableau generator using its register-program correctness
   and polynomial instruction bound.
   [Control](../PvsNP/TuringMachine/Registers/Control.lean) · [Simulation](../PvsNP/TuringMachine/Registers/SimulationBound.lean) · [Register reduction](../PvsNP/CookLevin/Generator/RegisterReduction.lean)
6. The counted program operations include reading the input length, copying,
   adding, and multiplying unary values. `run_emitLiteral` emits the list
   marker, sign, and unary index in the correct final order in `2 * a + 4`
   instructions for a literal with index `a`.
   [Length](../PvsNP/TuringMachine/Registers/InputLength.lean) · [Copy](../PvsNP/TuringMachine/Registers/Copy.lean) · [Addition](../PvsNP/TuringMachine/Registers/Add.lean) · [Multiplication](../PvsNP/TuringMachine/Registers/Multiply.lean) · [Literal emission](../PvsNP/CookLevin/Generator/EmitLiteral.lean)
7. `Fragment.run_link` transports a normal run into a larger finite program.
   `Fragment.run_seq` adds the instruction counts of linked fragments. The
   countdown program tests and decrements its counter before each body,
   matching the descending traversal. `Fragment.run_countdown_model` proves
   that a loop of `m` iterations with body cost at most `b` takes at most
   `m * (b + 1) + 1` instructions.
   [Linking](../PvsNP/TuringMachine/Registers/Fragments.lean) · [Countdown](../PvsNP/TuringMachine/Registers/Countdown.lean)
8. `run_parameterPrelude` checks one linked finite program from zero registers.
   `parameterValues_at` identifies its input length, certificate capacity
   `n^k`, largest pair length, horizon, window width, and dense name stride.
   `parameterTime_polynomiallyBounded` bounds the initialization for fixed
   exponents and verifier alphabet sizes. `run_accumulateName` adds the time
   offset `time * stride` to a literal index register.
   [Prelude](../PvsNP/CookLevin/Generator/Parameters.lean) · [Name calculation](../PvsNP/CookLevin/Generator/NameRegister.lean)
9. `run_generatorPrefix` links the prelude to the accepting assertion at the
   last clock tick. `binaryVerifierMap_acceptance_suffix` identifies this
   output as a suffix of the exact forward formula word. In the right-to-left
   generator it is the first block. `acceptanceCode_polynomialTime` verifies
   the closed prefix as a Cook transducer for this suffix.
   [Accepting block](../PvsNP/CookLevin/Generator/AcceptingBlock.lean) · [Generator prefix](../PvsNP/CookLevin/Generator/Prefix.lean)
10. `run_exactlyOneField` uses nested countdown loops for the negative ordered
    pairs and a separate loop for the positive clause. `foldExactlyOne_named`
    identifies this output with the original field traversal on consecutive
    names. `run_rowFragment` prepares the name ranges for the cells, head,
    and state. `run_rowsFragment` emits this block for every time from the
    horizon down to zero, and `rowsTimeBound_polynomiallyBounded` bounds the
    entire section. `binaryTableauRows_polynomialTimeMap` links the prelude
    and row program and applies the Cook tape simulation.
    [Field](../PvsNP/CookLevin/Generator/ExactlyOne.lean) · [Row](../PvsNP/CookLevin/Generator/Row.lean) · [Row traversal](../PvsNP/CookLevin/Generator/Rows.lean) · [Row transducer](../PvsNP/CookLevin/Generator/RowProgram.lean)
11. `runsValues_stepPreparationFragment` computes the state, head, and cell
    name bases for consecutive rows. `run_stepCopiesFragment` emits the
    guarded copy clauses. `runsOutput_stepUpdatesFragment` selects the fixed
    verifier entry for each state and read symbol, computes the next state,
    head, and written symbol names, and emits the three update implications.
    `stepTimeBound_polynomiallyBounded` supplies a uniform polynomial budget
    for the transition body.
    [Preparation](../PvsNP/CookLevin/Generator/StepPreparation.lean) · [Copies](../PvsNP/CookLevin/Generator/StepCopies.lean) · [Updates](../PvsNP/CookLevin/Generator/StepUpdates.lean) · [Budget](../PvsNP/CookLevin/Generator/StepBudget.lean)
12. `run_stepSectionFragment` links preparation, copies, updates, and cleanup
    for one time. `run_stepsFragment` visits every transition time from the
    horizon minus one down to zero. The loop produces the exact indexed
    transition section and preserves its entry registers. The uniform budget
    bounds each body by its cost bound at the horizon.
    [Step section](../PvsNP/CookLevin/Generator/StepSection.lean) · [Transition pass](../PvsNP/CookLevin/Generator/Steps.lean)
13. `run_forwardLookup` converts an in-range input position into the reverse
    cursor index and enters the selected branch with the work registers and
    cursor cleared. `initialCell_inputNames` and `initialCell_certificateNames`
    identify the input, separator, and certificate-slot clauses with the
    indexed formula. `runsOutput_initialCells` walks the full window from
    right to left and emits the corresponding named cell clauses.
    [Forward lookup](../PvsNP/TuringMachine/Registers/ForwardLookup.lean) · [Input cells](../PvsNP/CookLevin/Generator/InputCell.lean) · [Certificate cells](../PvsNP/CookLevin/Generator/CertificateCell.lean) · [Cell pass](../PvsNP/CookLevin/Generator/InitialCells.lean)
14. `run_initialGapsFragment` emits exactly the adjacent certificate-slot
    constraints. `run_initialSectionWindow` links the boundary setup, gap and
    cell passes, and head and state clauses. Its output is the exact fold of
    `FiniteTable.initialClauses` at the center of the window, with the existing
    output suffix retained. `initialSectionTimeBound_polynomiallyBounded`
    bounds the full initial section.
    [Gap pass](../PvsNP/CookLevin/Generator/InitialGaps.lean) · [Initial section](../PvsNP/CookLevin/Generator/InitialSection.lean)
15. `FiniteTable.binaryVerifierMap_eq_sections` identifies the exact generator
    output after prepending the accepting suffix, transition clauses, row
    constraints, and initial clauses in emission order.
    `runsOutput_verifierProgram` composes the four sections from zero
    registers. `run_verifierProgram` adds the halt and verifies the exact
    binary output. `verifierProgramTimeBound_polynomiallyBounded` bounds the
    entire execution for fixed verifier exponents and alphabets.
    `binaryTableauxPolyTime_verified` instantiates the finite register layout
    and applies the machine bridge.
    [Section order](../PvsNP/CookLevin/Generator/Blocks.lean) · [Complete generator](../PvsNP/CookLevin/Generator/VerifierProgram.lean) · [Register reduction](../PvsNP/CookLevin/Generator/RegisterReduction.lean)

## Assignment checking and SAT completeness

`mem_CNFSAT_iff_exists_assignment` characterizes binary CNF-SAT by a passing
assignment of length at most the formula word length. `checkEncoded_eq_true_iff`
extends this to Cook's complete checking language, with malformed formula
words and malformed instance–certificate pairs rejected.
[Binary language](../PvsNP/SAT/BinaryLanguage.lean) · [Assignment](../PvsNP/SAT/Assignment.lean)

The streaming checker makes one abstract update per formula bit and carries
truth flags and a unary index cursor. `run_finished_iff` characterizes the
finished states, `checkWord_eq` proves equality with the decoded checker, and
`cursor_run_le` bounds cursor growth by the number of bits processed.
[Stream](../PvsNP/SAT/Stream.lean)

1. `SATCursor.step_ofStream` splits the streaming state into finite flags and
   a certificate cursor. The cursor saturates at the end blank, and
   `read_saturated` proves that this preserves the default-false lookup.
   [Cursor program](../PvsNP/SAT/CursorProgram.lean)
2. On a valid encoded pair of length `n`, `withInputSetup_valid` inserts a
   left sentinel and returns to the first formula cell in `2 * n + 4` ticks.
   `withInputSetup_malformed` proves rejection within `n + 3` ticks when
   pair decoding fails. [Input setup](../PvsNP/SAT/InputSetup.lean)
3. `verifierTransition` marks the current formula cell before a certificate
   operation. `run_seek` and `run_restore` follow the actual single-tape
   sweeps and restore the formula bit. `run_reset`, `run_advance`, and
   `run_release` check the respective certificate operations, including an
   empty certificate and a cursor at its end blank.
   [Program](../PvsNP/SAT/VerifierProgram.lean) · [Shuttles](../PvsNP/SAT/VerifierSweeps.lean) · [Reset](../PvsNP/SAT/ResetCursor.lean) · [Advance](../PvsNP/SAT/AdvanceCursor.lean) · [Release](../PvsNP/SAT/ReleaseCursor.lean)
4. `run_bit` relates a parser step to the tape configuration and bounds its
   cost by `2 * n + 7`. `run_parser` composes the steps and accounts for the
   final transition at the delimiter. `verifierMachine_halt` gives a bound
   of `2 * n + 4 + n * (2 * n + 7) + 1` on every input and identifies the
   Boolean result. `checkEncoded_mem_POver` supplies Cook's polynomial-time
   checking relation, and `cnfSAT_mem_NP` combines it with the certificate
   length bound. [Machine correctness](../PvsNP/SAT/VerifierMachine.lean)

`mem_NP_polynomiallyReducesTo_CNFSAT` applies `binaryTableauxPolyTime_verified`
and the tableau membership equivalence to every language in `NP`.
`npComplete_CNFSAT` combines the reduction with `cnfSAT_mem_NP`.
[Binary reduction](../PvsNP/CookLevin/BinaryReduction.lean) · [Completeness](../PvsNP/SAT/Completeness.lean)

`p_eq_np_iff_CNFSAT_mem_P_verified` proves `P = NP ↔ CNFSAT ∈ P`.
`p_ne_np_iff_CNFSAT_not_mem_P` proves `P ≠ NP ↔ CNFSAT ∉ P`. Equality requires
a deterministic Cook decider that accepts exactly binary CNF-SAT and halts on
every binary word within `n^k + k` for some fixed `k`. Separation requires a
proof that no such decider exists. [Completeness](../PvsNP/SAT/Completeness.lean) · [Classes](../PvsNP/Complexity/Classes.lean)

## Complete-assignment search

`sat_congr_on_occurringIndices` shows that only values at occurring variable
names affect satisfaction. `searchAssignments_accepts_iff` proves that the
deterministic traversal covers those choices, and `searchWord_accepts_iff`
identifies its result with binary CNF-SAT on every word, including malformed
input. `occurringIndices_length_sq_le` uses unary name lengths to give
`k^2 ≤ 2 * n` for `k` distinct names in an `n`-bit formula word.
`searchWord_checks_le` then bounds complete-assignment checks by
`2^⌊√(2n)⌋`. The contradictory family has `k + 1` names and quadratic bit
length. `searchWord_checks_encode_unsatFamily` counts exactly `2^(k+1)` checks
on this family, and `no_polynomial_bound_for_searchWord_checks` rules out a
polynomial bound on the count.
[Distinct names](../PvsNP/SAT/DistinctVariableBound.lean) · [Traversal](../PvsNP/SAT/AssignmentTraversal.lean) · [Search](../PvsNP/SAT/AssignmentSearch.lean) · [Contradictory inputs](../PvsNP/SAT/AssignmentSearchFamily.lean)

`DecidesOnProfile` allows an adaptive query tree to depend on the input bit
length and the ordered list of distinct names. It exposes the formula to the
tree through Boolean checks of complete assignments. Each assignment has a
matching formula with that length and those names for which it is the unique
satisfying assignment. `run_eq_of_falseQueries` shows that answers along the
all-false path determine the tree's verdict. `pow_two_le_queries_of_decidesOnProfile`
therefore forces every assignment onto that path. The exhaustive tree attains
this bound by `firstSuccess_decidesOnProfile`, `falseQueries_firstSuccess`, and
`length_allAssignments`. `no_polynomial_bound_for_adaptive_assignment_queries` proves
the resulting obstruction to bounding that path length by a polynomial in
the bit length. A Cook decider can read the formula directly. The remaining
class question concerns its worst-case transition count on all binary input.
[Query trees](../PvsNP/SAT/AssignmentQueryTree.lean) · [Matched formulas](../PvsNP/SAT/AssignmentQueryFamily.lean) · [Adaptive query lower bound](../PvsNP/SAT/AssignmentQueryLowerBound.lean)

## Branching and unit propagation

1. `Refutes` permits the next fresh variable to depend on the formula and
   assignments already made. A branch covers both Boolean values, and a leaf
   requires an input clause whose literals are all false. The exhaustive
   tree branches on every occurring variable, skipping those already assigned.
   `exists_refutation_iff_not_satisfiable` characterizes exactly when a finite
   CNF has a conflict tree starting from the empty assignment.
   [Conflict trees](../PvsNP/SAT/BranchRefutation.lean) · [Branching completeness](../PvsNP/SAT/BranchCompleteness.lean)
2. The functional pigeonhole formula requires each of `n + 1` pigeons to
   occupy a hole and excludes two true entries in any row or column.
   `mem_formula_iff` identifies these clauses, and `formula_not_satisfiable`
   proves unsatisfiability by extracting an injection from the pigeons into
   the `n` holes. [Pigeonhole formula](../PvsNP/SAT/PigeonholeFormula.lean)
3. `formula_refutation_leaves` applies `Strategy.leaves_lower_bound` to a
   strategy that keeps the true entries as a partial matching. A query at
   a pair blocked by the matching can be answered false without increasing
   the score. At an unblocked pair either value adds a point by recording a
   placement or an exclusion. The partial matching rules out pair conflicts.
   A falsified row has no placement and must have every hole covered by a
   placement in another row or an explicit exclusion. This takes at least
   `n` points. Induction on the refutation tree turns each point into a factor
   of two in the leaf bound, yielding `2^n` leaves from an empty assignment.
   [Generic score bound](../PvsNP/SAT/BranchRefutation.lean) · [Pigeonhole strategy](../PvsNP/SAT/PigeonholeStrategy.lean)
4. `Refutes.of_unit` expands a unit step by adding an immediate conflict leaf
   for the opposite value of the variable. `PropagationRefutes.toTree` expands
   the whole trace, and `leaves_toTree_le_nodes` bounds the expanded leaf count
   by the number of decision, unit, and conflict events in the original trace.
   `exists_propagation_refutation_iff_not_satisfiable` checks that every
   unsatisfiable CNF has a trace and every valid trace certifies unsatisfiability.
   [Unit rule](../PvsNP/SAT/BranchRefutation.lean) · [Trace expansion](../PvsNP/SAT/PropagationRefutation.lean)
5. `refutation_pullback` recovers the pigeonhole variables from their natural
   number names and removes queries to names outside their image without
   increasing the leaf count. `encodedFormula_propagation_nodes` gives the
   `2^n` event bound for the binary CNF instances. Their bit lengths are
   polynomially bounded in `n` by `word_length_polynomiallyBounded`, so
   `no_polynomial_bound_for_binary_CNF_propagation_refutations` rules out a
   uniform polynomial size bound for these traces on unsatisfiable binary
   CNFs. The remaining class question quantifies over all Cook deciders and
   measures their machine transitions.
   [Binary encoding](../PvsNP/SAT/PigeonholeEncoding.lean) · [Binary lower bound](../PvsNP/SAT/PigeonholeLowerBound.lean) · [Classes](../PvsNP/Complexity/Classes.lean)

## Crossing-sequence time lower bound

1. `absoluteStart` places the input at nonnegative tape positions with
   the head at zero. `absoluteTick_absoluteAt` and
   `absoluteRun_start_state` bridge this absolute-coordinate
   presentation to Cook's relative tape and exact machine runs.
   A `crossingTranscript` lists the states entered on steps crossing
   a cut, including a crossing into a halt. `spliceConfig_absoluteStart_append`
   identifies the spliced tape with the start of the concatenated
   word when the left fragments have the same positive length.
   [Absolute coordinates](../PvsNP/TuringMachine/Crossing/Absolute.lean) · [Input splice](../PvsNP/TuringMachine/Crossing/Input.lean)
2. `absolute_halts_splice_of_crossingTranscript_eq` proves the halting
   splice for Cook runs. When two computations start on the same side
   of a cut, have the same crossing sequence, and halt with the same
   answer, the left tape of the first and the right tape of the second
   combine into a computation with that answer. The replay follows
   local steps on the corresponding side and matches states at the
   crossings. This is the splicing principle in Hennie's 1965
   *One-Tape, Off-Line Turing Machine Computations*, Theorem 1.
   [Hennie, Theorem 1](https://www.eecs.tufts.edu/~aloupis/comp260/lectures/hennie-1965.pdf) · [Cook splice proof](../PvsNP/TuringMachine/Crossing/Splice.lean)
3. `crossingWord` places two tables on opposite sides of `8 * p` bits
   of tautological padding. Each table has one bit per assignment
   to `r` address variables. At the chosen address, the left block
   prescribes the selector bit and the right block prescribes the
   complement of its table bit. `crossingWord_mem_CNFSAT_iff_ne` proves
   that the word is satisfiable exactly when the tables differ.
   At any cut in the common padding, `splice_crossingWord` joins
   the selected tables. Thus equal-table rejecting runs for distinct
   tables must have distinct transcripts at every such cut. A shared
   transcript would give a rejecting run on a satisfiable splice,
   contradicting correctness and uniqueness of the halt result.
   [Separated CNF family](../PvsNP/SAT/CrossingFamily.lean) · [Per-cut injectivity](../PvsNP/SAT/CrossingTimeLowerBound.lean)
4. With `q = Nat.card M.State + 3`, there are at most `q^ℓ`
   transcripts of length less than `ℓ`, by padding their state
   lists with an extra symbol. Here `q` includes the two halt
   outcomes and the padding symbol. When `2 * q^ℓ ≤ 2^(2^r)`,
   at least half the equal-table inputs have transcripts of
   length at least `ℓ` at each cut. Averaging over tables and
   cuts gives one input with summed lengths at least half
   `8 * p * ℓ` across the chosen padding cuts.
   `sum_crossingTranscript_length_le` charges at most one cut
   per machine transition. `crossing_clock_lower_bound` therefore
   gives `8 * p * ℓ ≤ 2 * t` for a common halt bound `t` on
   the equal-table words.
   [Transcript counting](../PvsNP/TuringMachine/Crossing/Counting.lean) · [Transition budget](../PvsNP/TuringMachine/Crossing/Time.lean) · [Clock lower bound](../PvsNP/SAT/CrossingTimeLowerBound.lean)
5. Set `p = blockWidth r`, so `n = 10 * blockWidth r + 1`.
   Each table's `2^r` bits occupy at most
   `2^r * (2 + (r + 1) * (r + 3))` tape bits. At these explicit
   lengths, `cnfsat_square_length_le_crossing_time` proves
   `n^2 ≤ 121 * (2 + (Nat.log2 n + 1) * (Nat.log2 n + 3)) * (Nat.card M.State + 3) * (t + n)`.
   `cnfsat_no_linear_clock` chooses a transcript threshold depending
   on `C` and a table large enough to meet it. It then proves that
   some input exceeds the proposed `C * (n + 1)` transition budget.
   An accepting-equality family could instead use two blocks of
   unit clauses assigning the same `r` variables. That carries
   `r` bits per block while unary names cost `Θ(r²)` bits,
   giving a weaker estimate from the same counting argument.
   The one-bit truth-table family gives a worst-case lower bound
   of order `n² / (log n)²` at the listed lengths for each fixed
   machine.
   [Binary encoding](../PvsNP/SAT/BinaryEncoding.lean) · [Length arithmetic](../PvsNP/SAT/CrossingScale.lean) · [Squared-length bound](../PvsNP/SAT/CrossingTimeLowerBound.lean)
6. `separated_crossing_clock_lower_bound` abstracts the transcript
   argument to any finite family of fixed-width left blocks, paired
   right blocks, and shared padding, with rejecting matched pairs
   and accepting mixed pairs. `Palette.satisfiable_iff_ne` supplies
   a larger family with `r` payload bits at each of the `2^r` addresses.
   Each payload slot has two variables, one for each bit value. A shared
   header permits at most one payload variable to be true. At the selected
   address, both clauses must admit that same variable. The left clause
   uses the table's bits and the right uses the complemented bits, so a
   common choice exists exactly when the tables differ. `Palette.card_table`
   counts `2^(r * 2^r)` tables.
   [Reusable crossing proof](../PvsNP/SAT/CrossingTimeLowerBound.lean) · [Payload clauses](../PvsNP/SAT/CrossingPalette.lean) · [Table count](../PvsNP/SAT/CrossingPaletteTime.lean)
7. Unary payload indices can vary in width. `padFormula` appends a positive
   unit on an index above those used by the payload clauses. Its unary
   index fills the unused width, and it can be set independently to true.
   `Palette.length_leftBlock` and `Palette.length_rightBlock` make the
   two block lengths `width r` and `width r + 1`, with the extra bit
   terminating the formula. Here `width r = 48 * (r + 1)^2 * 2^r`.
   The common middle padding contributes `8 * width r` bits. For
   `r ≥ 1` and `n = 10 * width r + 1`,
   `Palette.cnfsat_square_length_le_log_crossing_time` gives
   `n^2 ≤ 11616 * (Nat.log2 n + 1) * (Nat.card M.State + 3) * (t + n)`
   for a common halting budget `t` on the equal-table family.
   `Palette.exists_rejecting_word_with_log_crossing_time` finds one
   `n`-bit word outside `CNFSAT` for which every halting budget satisfies
   the same inequality. The resulting fixed-machine lower bound is of
   order `n² / log n` at these lengths.
   [Width normalization](../PvsNP/SAT/CrossingBlockPadding.lean) · [Encoded blocks](../PvsNP/SAT/CrossingPaletteBlocks.lean) · [Halting budget](../PvsNP/SAT/CrossingPaletteTime.lean)
8. For a prescribed length `N`, `Palette.wordAtLength` uses one positive
   unit on a fresh index as the entire common middle block. Its unary
   width gives exactly `N` bits, with at least `8 * width r` middle
   bits when `10 * width r + 1 ≤ N`.
   `separated_word_crossing_clock_lower_bound` counts all the cuts in
   that common word. `Palette.exists_rejecting_word_at_exact_length`
   therefore retains the bound from the base length for a rejecting
   word of length `N`. The base lengths grow by at most a factor of
   eight, so the last base length up to `N` gives
   `Palette.exists_rejecting_word_with_log_crossing_time_at_every_length`.
   For every `N ≥ 3841` it gives a rejecting `N`-bit word with
   `N^2 ≤ 743424 * (Nat.log2 N + 1) * (Nat.card M.State + 3) * (t + N)`
   at every halting budget `t`.
   [Exact-length words](../PvsNP/SAT/CrossingPaletteBlocks.lean) · [Every length](../PvsNP/SAT/CrossingPaletteWorstCase.lean)
9. `cnfsat_no_subquadratic_rational_clock` uses the one-bit family.
   Given a machine with `M.Decides CNFSAT`, natural `C`, and natural
   `e, d` with `1 ≤ d` and `e < 2 * d`, it gives a word `w ∉ CNFSAT`
   such that every halting budget `t` satisfies
   `C * (w.length + 1)^e < t^d`. This rules out a uniform clock of
   any fixed rational exponent below two. The class question still
   concerns the existence of a decider with any fixed polynomial bound.
   [Rational exponent bound](../PvsNP/SAT/CrossingPowerBound.lean)

## Boolean circuits for Cook computations

1. `encodeWindow` assigns one indicator wire per state, head position, and
   position-symbol pair. With `q` states including both halting states, `s`
   tape symbols, and window width `w`, `windowBitCount_eq` counts
   `b = q + w + w * s` wires. `windowStartExpr_eval` initializes the wires
   from the input bits, with blanks filling the rest of the window.
   [Initialization](../PvsNP/Circuits/WindowInput.lean) · [Wire count](../PvsNP/Circuits/WindowSimulation.lean)
2. `windowStep_eval` proves that the current state, head, and scanned symbol
   activate exactly the transition needed for one `windowTick`. The output
   formulas preserve the symbols at every position outside the old head.
   `machineLayered_eval` connects initialization, `T` transition layers,
   and the accept wire to the actual machine state after `T` ticks. The
   window has width `2 * T + 1` and the head starts at its center.
   [Transition formulas](../PvsNP/Circuits/WindowStep.lean) · [Layered simulation](../PvsNP/Circuits/WindowSimulation.lean)
3. `machineLayered_size_le` bounds the expression node count by
   `8 * b + T * b * (6 * q * w * s + 6) + 1`, which grows as
   `O((T + 1)^3)` for a fixed machine. `machineLayered_size_polynomiallyBounded`
   applies the bound to a polynomial clock. `Layered.eval_toBooleanCircuit`
   and `Layered.size_toBooleanCircuit_le` preserve the output and bound when
   flattening to a DAG of fan-in at most two. A later gate can reuse an
   earlier wire through its index.
   [Size bound](../PvsNP/Circuits/WindowSimulation.lean) · [Circuit compiler](../PvsNP/Circuits/BooleanCircuit.lean)
4. `Machine.exists_polynomialSize_circuits` sets `T = n^k + k` and uses the
   halt bound to identify each circuit output with the machine verdict.
   `P_subset_PPoly` places every language in `P` in the class with one circuit
   per input length and a single polynomial bound on their gate counts. By
   `not_mem_PPoly_iff` and `p_ne_np_of_CNFSAT_not_mem_PPoly`, separation would
   follow if for every `C` and `d`, some length `n` required more than
   `C * (n + 1)^d` gates in every circuit deciding binary CNF-SAT on all
   `n`-bit words. That lower bound remains open in this development.
   [Circuit classes and separation](../PvsNP/Complexity/CircuitLowerBound.lean)

## Polynomial-size circuits under reductions

1. `outputsAt_at_bound` preserves the canonical output tape at the chosen
   clock `T`. `windowRun_head_le` bounds the final head position in the
   simulation, which starts at position `T`. A window of `2 * T + B + 1`
   cells fits the `B` output positions read from that head. The bound
   `output_length_le` permits `B = n + 2 * T` on an `n`-bit input.
   [Transducer output](../PvsNP/TuringMachine/Transducer.lean) · [Head bound](../PvsNP/CookLevin/TapeWindow.lean) · [Output length](../PvsNP/TuringMachine/OutputBound.lean)
2. `wordBuffer` uses `B` data wires padded with false and `B` presence wires
   true at exactly the positions of the original word. `machineOutputLayered_eval`
   reads the output tape into this representation by distinguishing the machine's
   input symbols from blank. `machineOutputLayered_size_polynomiallyBounded`
   bounds the gate count when `T` and `B` are polynomial in `n`.
   `PolynomialTimeMap.exists_bufferCircuits` gives a family of these
   multi-output circuits for every polynomial-time transducer.
   [Buffer representation](../PvsNP/Circuits/WordBuffer.lean) · [Output simulation](../PvsNP/Circuits/TransducerOutput.lean) · [Circuit reductions](../PvsNP/Complexity/CircuitReductions.lean)
3. `selectLength_eval` uses the presence bits at the candidate length's
   boundary to pick the circuit for the actual length. `selectLength_size_le`
   bounds the selector by `(B + 1) * (K + 5) + 1` when each candidate uses at
   most `K` gates. `mem_PPoly_iff_bufferCircuits` gives the equivalent
   `PPoly` formulation with one decider per capacity `B` that handles all
   words of length at most `B` in this representation.
   [Length selection](../PvsNP/Circuits/LengthSelection.lean) · [Buffered circuits](../PvsNP/Complexity/BufferedCircuits.lean)
4. `PolynomialTimeMap.preimage_mem_PPoly` composes the transducer's output
   circuit with the buffered decider, adding their gate counts.
   `PolynomiallyReducesTo.mem_PPoly` transfers the resulting polynomial bound
   to the source language. `CNFSAT_mem_PPoly_iff_np_subset` proves
   `CNFSAT ∈ PPoly ↔ NP ⊆ PPoly` using the Cook–Levin reduction, and
   `CNFSAT_not_mem_PPoly_of_mem_NP` transfers a superpolynomial circuit
   lower bound for any language in `NP` to binary CNF-SAT. Such a lower
   bound would prove separation by `p_ne_np_of_CNFSAT_not_mem_PPoly`.
   [Circuit reductions](../PvsNP/Complexity/CircuitReductions.lean) · [Separation](../PvsNP/Complexity/CircuitLowerBound.lean)

## SAT oracle search and witness circuits

1. `prefixQuery` prepends a binary unit clause for each prefix bit, fixing
   variables from index zero. `decode_prefixQuery` identifies the decoded
   clauses and shows that a malformed word still produces a malformed
   query. For a prefix of length at most the input length `n`,
   `mem_prefixQuery_iff_exists_assignment` says a yes
   answer is equivalent to an `n`-bit assignment extending the prefix and
   passing `checkWord` on the original input.
   [Query encoding](../PvsNP/SAT/SearchOracleQuery.lean) · [Assignment equivalence](../PvsNP/SAT/OracleSearch.lean)
2. `searchWithOracle` first asks about the original word. After a yes
   answer, it tries extending the current prefix by false. It appends true
   only when that query returns no, preserving the existence of a
   satisfying completion. `searchWithOracle_sound` verifies the returned
   assignment. `searchWithOracle_success_iff` and
   `searchWithOracle_none_iff` identify exactly which inputs return an
   assignment and which return none. `searchWithOracle_query_count`
   gives `n + 1` calls on satisfiable inputs and one call on rejection.
   `searchWithOracle_query_length_le` bounds each query's length by
   `B = n + n * (n + 5)`.
   [Prefix search](../PvsNP/Complexity/PrefixWitnessSearch.lean) · [SAT oracle search](../PvsNP/SAT/OracleSearch.lean)
3. `clockedOracle_eq_true_iff` reads the exact Cook run of a SAT decider
   on a query `q` after `q.length^k + k` allotted ticks.
   `searchWithClockedOracle_correct` proves the resulting assignment or
   rejection is correct. The charge
   `oracleSearchCharge` sums the length of each query and the ticks
   allotted to it. `searchWithOracle_charge_le` bounds this sum by
   `(n + 1) * (B + (B^k + k))`, and
   `searchWithOracle_charge_polynomiallyBounded` verifies that bound for
   each fixed `k`. A returning Cook call accounts for the physical
   transitions from a prepared query back to the controller at the
   origin.
   [Clock and charge](../PvsNP/SAT/OracleSearch.lean) · [Returning calls](#returning-cook-calls)
4. `witnessCircuit` unrolls the prefix search into a circuit whose accepted
   inputs have an `n`-bit satisfying assignment on the first `n` outputs.
   Each step wires the fixed query bits to two shared constant gates,
   applies the decision circuit for the query's length, and negates the
   answer to obtain the next bit. The last output is the original input's
   decision bit.
   `witnessCircuit_size_le` gives `n * (K + 3) + K` gates when the
   decision circuits through length `B` use at most `K` gates each.
   `CNFSAT_mem_PPoly_iff_exists_witnessCircuits` equates polynomial-size
   SAT decision families with polynomial-size witness families. The
   reverse direction reads the success wire from the witness circuit.
   Whether these polynomial-size families exist remains open.
   [Query wiring](../PvsNP/Circuits/PrefixQueryWiring.lean) · [Witness circuits](../PvsNP/SAT/SearchCircuits.lean)

## Returning Cook calls

1. The call machine uses one tape with a finite product alphabet. Each
   cell stores a scratch symbol, a protected symbol, and an origin marker.
   `FrameAt` relates each physical cell's protected symbol to its
   absolute coordinate and requires exactly one origin marker. The finite
   control records which side of the origin the head is on, and
   `sideAt_advanceSide` updates this bit when moving off the marked cell.
   [Call machine](../PvsNP/TuringMachine/TrackCall/Core.lean) · [Tape tracks](../PvsNP/TuringMachine/TrackCall/Tracks.lean)
2. `simulate_run` follows the child machine one tick at a time through
   its first halt. The scratch projection agrees with the child tape,
   and the protected track and marker stay unchanged at every absolute
   cell. Starting at the origin, the child's first halt after `t`
   transitions leaves the head at distance at most `t`. From position
   `pos`, `rewind_run` reaches the origin in `pos.natAbs + 2` ticks,
   including a final right-left pair of moves. `rewind_run_nth` proves
   that this phase preserves the full symbol at every absolute cell.
   [Scratch simulation](../PvsNP/TuringMachine/TrackCall/Simulation.lean) · [Physical rewind](../PvsNP/TuringMachine/TrackCall/Rewind.lean)
3. `runReturning` returns the child's answer at the origin within
   `2 * T + 2` transitions when the prepared child halts within `T`.
   The compiled controller keeps the false and true return labels in
   finite control. `Controller.run_call` shows that the last move
   resumes the matching label at the origin and retains all protected
   data. `Controller.run_call_prepared` supplies the initial frame
   using `prepareTape`. `Controller.run_call_of_transition` includes
   the invocation tick, for at most `2 * T + 3` transitions when that
   tick leaves the required query on scratch at the origin.
   [Controller](../PvsNP/TuringMachine/TrackCall/Controller.lean) · [Return bounds](../PvsNP/TuringMachine/TrackCall/Return.lean)
4. `search_queries_have_returning_calls` assigns a physical transition
   count to each query in the clocked SAT search trace. From its own
   prepared tape, each call returns the exact clocked answer at the
   origin with the protected data intact. The sum is at most
   `(n + 1) * (2 * (B^k + k) + 2)`, where `B = n + n * (n + 5)`.
   `returningSearchCalls_polynomiallyBounded` verifies the polynomial
   bound for each fixed `k`.
   `prepareTape` is a computable description of a starting tape
   outside the call's transition count. The scratch loader accounts for
   the physical transitions to install a query from a protected source.
   [SAT call budget](../PvsNP/SAT/OracleCalls.lean) · [Tape preparation](../PvsNP/TuringMachine/TrackCall/Tracks.lean) · [Scratch loader](#loading-scratch-from-a-protected-source)

## Loading scratch from a protected source

1. The protected cells of a `WindowSpec` carry the left and right
   boundary marks at `-L` and `R`, with `R > 0`, and the scratch
   symbol to write at each cell of the interval. These symbols include
   the query and the blanks needed to reset the rest of the workspace.
   `Rules` specifies the loader transitions for a finite controller.
   `program_rules` verifies them for the concrete loader.
   `ScratchAt` records agreement with the target on selected absolute
   coordinates as the head moves.
   [Loader rules](../PvsNP/TuringMachine/TrackCall/Loader/Core.lean) · [Concrete controller](../PvsNP/TuringMachine/TrackCall/Loader/Program.lean) · [Window specification](../PvsNP/TuringMachine/TrackCall/Loader/Load.lean)
2. `run_seekLeft` takes `L + 2` ticks to reach the left boundary
   in the writing phase. `run_writeForward` overwrites the interval
   in `L + R + 1` ticks and leaves the head at `R - 1`.
   `run_seekOrigin` takes `R + 1` ticks to return to the origin
   and enter the call. `run_load` composes these phases in exactly
   `2 * (L + R) + 4` physical transitions. At call entry the full
   scratch tape agrees with the target when the exterior agreed at
   the start, and every protected cell has its original value.
   [Travel phases](../PvsNP/TuringMachine/TrackCall/Loader/Travel.lean) · [Writing phase](../PvsNP/TuringMachine/TrackCall/Loader/Write.lean) · [Loader composition](../PvsNP/TuringMachine/TrackCall/Loader/Load.lean)
3. `simulate_run_preserving_outside` keeps scratch cells at distance
   at least `T` from the origin intact when the child starts there
   and halts within `T` ticks. The rewind preserves all symbols.
   `run_load_call` combines this with the loader when the input
   length is at most `R + 1` and `T` fits both `L` and `R`.
   It resumes the correct continuation at the origin within
   `2 * (L + R) + 2 * T + 6` ticks, preserving `FrameAt` and
   `BlankOutside` for reuse of the workspace.
   [Scratch preservation](../PvsNP/TuringMachine/TrackCall/Simulation.lean) · [Call and rewind](../PvsNP/TuringMachine/TrackCall/Return.lean) · [Workspace reuse](../PvsNP/TuringMachine/TrackCall/Loader/Load.lean)
4. `search_query_has_loaded_call` applies the loader and call to
   each recorded SAT query when its protected layout is in place.
   For an `n`-bit input, take `B = n + n * (n + 5)` and symmetric
   radius `W = B + (B^k + k) + 1`. The loaded call returns the
   exact clocked answer within `4 * W + 2 * (B^k + k) + 6` ticks.
   `loadedSearchCalls_polynomiallyBounded` multiplies this budget
   by the maximum of `n + 1` calls and proves a polynomial bound
   for fixed `k`. In-place edits supply the protected source for
   each successive trial query.
   [SAT workspace and bounds](../PvsNP/SAT/OracleWorkspace.lean) · [Query iterations](#editing-and-reusing-the-sat-query-buffer)

## Editing and reusing the SAT query buffer

1. `appendUnitQuery_encode` replaces a valid formula's final terminator
   with an encoded unit clause and a new terminator. For variable `i`
   the block has `i + 6` bits. At an old terminator index `j`,
   `appendUnitQuery_set_sign` sets the sign at `j + 2`.
   `appendPrefixQuery_mem_CNFSAT_iff` and
   `length_appendPrefixQuery_eq_prefixQuery` give the same SAT answer and
   length as prepending the prefix clauses when the original word decodes.
   [Appended queries](../PvsNP/SAT/AppendQuery.lean)
2. `TracksAt` describes the scratch and protected symbols at absolute
   coordinates. `QueryBuffer` relates the protected bits and blanks to
   the current word and locates its terminator and optional pending sign.
   `run_append` scans to index `j`, writes the trial clause for `i`,
   and returns to the origin in `2 * (j + i + 6) + 2` ticks.
   `queryBuffer_append` checks the new word and marks.
   `run_commit` updates the marked sign at `s = j + 2` and
   returns in `2 * s + 2` ticks. `queryBuffer_commit` checks
   that the sign edit clears the pending mark and keeps the terminator
   in place. The append and commit both keep the auxiliary payload
   that stores the scan stops and workspace edges.
   [Track edits](../PvsNP/TuringMachine/TrackCall/QueryEdit/Core.lean) · [Physical append](../PvsNP/TuringMachine/TrackCall/QueryEdit/Append.lean) · [Physical commit](../PvsNP/TuringMachine/TrackCall/QueryEdit/Commit.lean) · [Buffer invariant](../PvsNP/SAT/QueryBuffer.lean)
3. `dropLast_length_appendPrefixQuery` identifies the terminator after
   `i` appends as `queryTail n i`, which depends only on the original
   length `n` and the stage. At stage `i`, the unary scan starts at
   `queryTail n i + 3`. For offsets `a ≤ i`,
   `contains_unaryStopPositions` says the schedule marks that cell
   exactly when `a = i`. One set of preinstalled stops therefore works
   for every assignment path.
   [Stop schedule](../PvsNP/SAT/QueryIndices.lean)
4. `windowSpec_of_tracksAt` turns the trial buffer and its edge marks
   into the layout read by the scratch loader. `run_sat_query_iteration`
   appends a false trial, loads and calls the clocked SAT decider, and
   commits the opposite of its answer. Starting with a feasible prefix
   of a well-formed input, the next prefix remains feasible. The machine
   returns to the origin with the updated buffer and blank scratch
   exterior. `satQueryIterations_polynomiallyBounded` bounds the cost
   of up to `n + 1` stages for fixed clock exponent `k`.
   [Loader bridge](../PvsNP/TuringMachine/TrackCall/QueryEdit/LoaderBridge.lean) · [Physical iteration](../PvsNP/SAT/QueryIteration.lean) · [SAT iteration](../PvsNP/SAT/QueryIterationSAT.lean)
5. `loopIterationProgram_rules` verifies a finite controller that
   jumps back to its first scan after each commit.
   `run_sat_query_loop` composes those stages into one continuing
   machine run. It starts at the origin with a feasible prefix, its
   query buffer, blank scratch outside the workspace, and the full
   stop schedule and workspace edges already installed. After
   `remaining = n - pref.length` stages, the run has used at most
   `remaining * satQueryStepBound k n` transitions. Its buffer holds
   the clauses for an `n`-bit assignment accepted by `checkWord`.
   `run_loopIterationProgram` specializes this to the concrete
   controller and an empty prefix on a prepared satisfiable input.
   It observes the controller at `seekTail` after `n` stages, with
   a bound of `n * satQueryStepBound k n` physical transitions.
   A complete uniform transducer still needs to initialize the
   protected layout from the raw input, handle malformed and
   unsatisfiable inputs, recognize completion on the tape, and
   write the canonical output before halting.
   [Cyclic controller](../PvsNP/SAT/QueryIterationProgram.lean) · [Continuing run](../PvsNP/SAT/QueryLoop.lean) · [Concrete specialization](../PvsNP/SAT/QueryLoopProgram.lean) · [Cook transducers](../PvsNP/TuringMachine/Transducer.lean)

## Gate lower bounds for binary CNF-SAT

1. `Network.exists_inputSupport_binary` traces the wires needed to evaluate
   the output backwards through the network. Replacing a needed wire by
   its inputs can add at most one wire at a binary gate. A NOT gate or
   constant adds none. For a single output this bounds the number of
   needed input wires by `binarySize + 1`. A bit that can change the answer
   on its own must be in this set. The theorem
   `BooleanCircuit.card_le_binarySize_add_one_of_sensitive` counts any
   collection of such bits. [Input support](../PvsNP/Circuits/InputSupport.lean)
2. `cnfsat_all_inputs_sensitive` supplies an accepting and a rejecting word
   differing only at each given coordinate when `n ≥ 16`. In an interior
   coordinate `i`, the encoding starts with positive singleton clauses
   whose variable indices are `i - 5` and `n - i - 6`. Turning off the
   second clause's marker leaves a valid formula prefix followed by trailing
   data. Separate witnesses cover the endpoints. This gives
   `cnfsat_binarySize_ge`, a bound of `n - 1` binary gates. Under the promise
   of a valid formula encoding, `valid_sign_sensitive` uses an initial
   positive unit clause on variable zero and `m` more unit clauses on
   that variable. Each sign is relevant on this family, so
   `cnfsat_binarySize_ge_on_valid_encodings` gives `m - 1` binary gates at
   length `5 * m + 6`.
   [Marker witnesses](../PvsNP/SAT/CircuitSensitivity.lean) · [Sign witnesses](../PvsNP/SAT/CircuitProjection.lean) · [Binary gate bounds](../PvsNP/SAT/CircuitSize.lean)
3. `last_three_sensitive_monotone` gives a positive-unit encoding whose
   final zero can be set to one to change acceptance to rejection. Since
   `Network.eval_mono_of_negationSize_zero` preserves acceptance as input
   bits increase, `cnfsat_negationSize_pos` requires a NOT gate for `n ≥ 6`.
   `cnfsat_size_ge` adds this gate to the binary gates and gives a total
   size of at least `n` for `n ≥ 16`.
   [Terminal bits](../PvsNP/SAT/CircuitSuffixSensitivity.lean) · [Total gate bound](../PvsNP/SAT/CircuitSize.lean)
4. `riseSteps_card_balance` gives `rises + first = falls + last` for a
   Boolean wire along a chain, with endpoint values read as zero or one. In
   `BooleanCircuit.falls_add_one_le_pow_negationSize`, the proof tracks
   all steps at which a computed wire falls. A monotone gate creates no
   new such steps. A NOT gate can add at most the number of rises of its
   operand, which is bounded by one plus the number of its falls. Thus
   one plus the number of tracked steps at most doubles at each NOT gate.
   On a nondecreasing input chain with `k` output falls and `r` NOT gates,
   this gives `k + 1 ≤ 2^r`, the necessity direction of Markov's theorem.
   [Boolean chain counts](../PvsNP/Circuits/BooleanChain.lean) · [Negation bound](../PvsNP/Circuits/NegationLowerBound.lean) · [Markov theorem background](https://arxiv.org/abs/1410.8420)
5. `pairChain_monotone` and `pairChain_mem_iff` give a nondecreasing chain
   of words of length `n` with `k` output falls whenever `9 * k + 17 ≤ n`.
   `pairChain_decodes` gives a valid formula at every step. Two fixed unit
   clauses set variable zero to false and variable one to true. In each of
   `k` two-literal clauses over these variables, the sign on variable zero
   flips before the sign on variable one. The intermediate clause is false
   and the other two versions are true under the fixed values. The fixed
   units take five and six bits, and each two-literal clause takes nine.
   A filler unit uses `p + 5` bits at index `p = n - (9 * k + 17)` and has
   a positive sign exactly when `p ≠ 0`. Its sign agrees with the assignment
   setting variable zero to false and every other variable to true. With
   one final terminator, the total length is `9 * k + 17 + p = n`.
   `cnfsat_pairChain_negationSize_lower` applies the negation bound to this
   chain. With `k = 2^extra`, it requires at least `extra + 1` NOT gates.
   Adding the `n - 1` binary gates gives `cnfsat_size_ge_add`, the bound
   `n + extra ≤ size` when `9 * 2^extra + 17 ≤ n`. The circuit separation
   obligation still quantifies over all polynomial bounds.
   [Chain construction](../PvsNP/SAT/CircuitNegationWitness.lean) · [Additive gate bound](../PvsNP/SAT/CircuitNegationSize.lean) · [Separation obligation](../PvsNP/Complexity/CircuitLowerBound.lean)

## Parity restrictions on pairs of input bits

1. `ParityRestriction` fixes every bit outside a chosen pair and checks
   XOR or XNOR on the four assignments to that pair. `not_parity_of_binary_unaries`
   rules out computing this restriction with one AND or OR surrounded by
   unary maps. A unary map on either varying input must distinguish both
   values. One of those values therefore makes the gate insensitive to
   the other input, contradicting parity.
   [Parity certificates](../PvsNP/Circuits/PairRestriction.lean)
2. `Network.inputSupport` follows needed wires through the gate sequence.
   `inputSupport_card_add_parity_le` counts the needed wires together with
   a set of designated wires that has a parity restriction on every pair.
   When the proof advances through a gate, it discards designated operands
   that are also needed elsewhere. `previousSupport_card_add_inter_le`
   accounts for this sharing in the support count. A designated operand
   used only by the current gate can move to the gate output. Two such
   operands cannot move to the same output, by the one-gate obstruction.
   At the final output, the support is a singleton and at most one
   designated wire remains. For an output that depends on every input,
   `card_le_binarySize_add_two_of_parity` gives `n + k ≤ binarySize + 2`
   when the designated set has `k` wires.
   [Canonical support](../PvsNP/Circuits/InputSupport.lean) · [Sharing count](../PvsNP/Circuits/ParitySupport.lean) · [Binary-gate lower bound](../PvsNP/Circuits/ParityBinaryLowerBound.lean)
3. In `cnfsat_long_pair_xnor`, the two varying bits sign unit clauses
   on the same variable. The prefix and suffix place the sign bits at
   the chosen coordinates. For gaps of five through ten bits, the
   unary variable index sets the unit width. For larger gaps, a unit
   on a different variable fills the space. The formula is satisfiable
   exactly when the signs agree.
   [Long-gap XNOR construction](../PvsNP/SAT/CircuitParityRestriction.lean)
4. `cnfsat_close_pair_xor` handles separations `d` from one to four bits
   by setting `r = d - 1`. The first bit `a` gives the sign of a literal
   and the second bit `b` lies in its unary index. When `b = false`,
   the first clause is a unit on variable `r` and a following positive
   unit enforces `a = true`. When `b = true`, the first variable index
   extends and the following unit joins the first clause as a second
   literal. A fixed negative unit on variable `r + 1` now enforces
   `a = false`. All four words are valid encodings and the accepted
   words are exactly those with `a ≠ b`.
   [Close-gap XOR construction](../PvsNP/SAT/CircuitCloseParity.lean)
5. `cnfsat_interior_pair_parity` combines the two constructions.
   The designated coordinates are consecutive, starting at position 13.
   At input length `n ≥ 43` the proof takes `k = n - 43`, with a
   separate fixed setting of the other bits for each pair.
   `cnfsat_size_ge_twice_sub` adds the required NOT gate and yields
   `2 * n - 44 ≤ size`. `cnfsat_size_ge_twice_add_sub` adds the
   independent logarithmic NOT bound when the input length permits.
   Both allow arbitrary fanout in the AND, OR, and NOT basis.
   [CNF-SAT gate bounds](../PvsNP/SAT/CircuitParitySize.lean) · [Circuit model](../PvsNP/Circuits/BooleanCircuit.lean)

## Pair restrictions over the full binary basis

1. `BinaryBasisCircuit` uses the same topology and assigns any of the
   sixteen Boolean tables to each binary gate. Constants and NOT gates
   keep their original semantics. `ofBooleanCircuit` preserves evaluation
   and size. In the other direction, `eval_toBooleanCircuit` proves
   correctness of the table-by-table translation to AND, OR, and NOT,
   and `size_toBooleanCircuit_le` bounds the resulting size by a factor
   of four. The translation retains computed wires for reuse.
   [Full binary basis](../PvsNP/Circuits/BinaryBasis.lean) · [Basis translation](../PvsNP/Circuits/BinaryBasisBridge.lean)
2. A `BasisPair` gives two restrictions on the same pins, one to
   XOR or XNOR and one to a signed AND table. The fixed inputs
   may differ between restrictions. When both pins reach the rest
   of the network only through the same gate, each output table
   factors through that gate's fixed two-input table followed by
   a unary map. The parity map is nonconstant and therefore
   injective. Since XOR and XNOR agree on complementary input
   pairs, the fixed gate table must agree on them too. Every unary
   map preserves these agreements. A signed AND table distinguishes
   its exceptional row from that row's complement.
   `not_basisPair_of_exclusive_sources` derives the contradiction.
   [Pair certificates](../PvsNP/Circuits/BinaryBasisPair.lean)
3. `exists_next_pair_support` supplies the gate-by-gate balance for
   needed wires and designated wires. Shared operands pay for
   discarded designations, and a surviving exclusive operand
   can be promoted to the gate output. Feeding the full-basis
   pair lemmas into this balance gives
   `card_le_binarySize_add_two_of_basisPair`. With all `n` inputs
   relevant and `k` designated wires, it gives
   `n + k ≤ binarySize + 2`.
   [Support balance](../PvsNP/Circuits/ParitySupport.lean) · [Full-basis lower bound](../PvsNP/Circuits/BinaryBasisLowerBound.lean)
4. For gaps of at least five bits, `cnfsat_long_pair_and` adds a
   fixed positive unit on the same target variable as the two
   selected signs. The formula then requires both signs to be
   true. At gaps of one to four bits, `cnfsat_close_pair_or`
   changes the last fixed unit in the close XOR layout from
   negative to positive. Setting the index bit `b` to true now
   merges the first two clauses into a satisfied clause. With
   `b = false`, the separate units require `a = true`.
   `cnfsat_binaryBasis_interior_pair` combines these AND or OR
   restrictions with the parity restrictions. At `n ≥ 44` the
   designated interval has `n - 44` wires, starting at position 13.
   `cnfsat_binaryBasis_binarySize_ge_twice_sub` gives
   `2 * n - 46 ≤ binarySize` for every correct binary CNF-SAT
   circuit over the full basis.
   [Long AND restriction](../PvsNP/SAT/CircuitParityRestriction.lean) · [Close OR restriction](../PvsNP/SAT/CircuitCloseParity.lean) · [CNF-SAT gate bound](../PvsNP/SAT/CircuitBinaryBasisSize.lean)
5. Two alternating scans give a limit on what the pair certificates
   alone force. Let `A` combine a seed with `m` data bits in
   forward order using alternating AND and OR. Let `B` scan in
   reverse order from a second seed, using the same operation
   at each data bit. With all unselected bits neutral, the scans
   at a pair with opposite operations can use seeds that absorb
   the first selected bit and are neutral for the second. At a
   pair with the same operation, an intermediate bit has the
   opposite operation and can be set to absorb the earlier scan
   value in both directions. Its absorbing value is neutral for
   the selected operation. In either case, `A` returns the
   right selected bit and `B` the left one. The output
   `A XOR (s AND B)` gives XOR with `s = true`. Setting
   `s = false`, all unselected data bits neutral, and the forward
   seed neutral for the left selected operation instead gives
   the right selected operation on the pair. All three extra
   inputs are relevant, as seen by making every data bit neutral.
   This uses `2 * m + 2` binary gates on `m + 3` inputs while
   giving both certificates for every pair of data inputs.
6. `mem_PPolyBinaryBasis_iff` identifies the polynomial-size
   families in the two bases. `P_subset_PPolyBinaryBasis` carries
   over the simulation of polynomial-time Cook machines.
   `p_ne_np_of_CNFSAT_not_mem_PPolyBinaryBasis` gives separation
   if full-basis CNF-SAT circuits fail every polynomial size
   bound. The linear lower bound leaves that obligation open.
   [Circuit classes and conditional separation](../PvsNP/Complexity/BinaryBasisCircuits.lean)

## A language defined by circuit counting

1. `enumerateCircuits n s` lists the circuits with `n` inputs and exactly
   `s` gates. `exists_mem_enumerateCircuits_of_size_le` extends each smaller
   circuit to that size by adding unused constant gates and preserving its
   selected output. `length_enumerateCircuits_le` bounds the list length by
   `(n + s) * (8 * (n + s + 1)^2)^s`.
   [Circuit enumeration](../PvsNP/Circuits/Enumerate.lean)
2. `truthTable` and `tableLookup` use the same ordered enumeration of
   assignments. `truthTable_tableLookup` reconstructs every table of the
   required length `2^n`. The list `allTruthTables n` has `2^(2^n)` distinct
   entries by `allTruthTables_length` and `allTruthTables_nodup`.
   [Truth tables](../PvsNP/Circuits/TruthTable.lean)
3. `countingBudget_circuit_count_lt` shows that for `n ≥ 5` the enumerated
   circuit list is strictly smaller than the truth-table list at the gate
   budget `s = ⌊2^n / (8 * n)⌋`. `hardTruthTable` searches the table list
   for the first table omitted by the circuit list, with an all-zero
   default. `length_hardTruthTable` gives the table length `2^n`.
   `hardTruthTable_mismatch` gives an input on which any circuit within
   budget disagrees with the selected table. The fixed language
   `countingHardLanguage` reads this table at the input's length. Consequently,
   `countingHardLanguage_size_gt` requires more than `s` gates for a
   correct circuit at each `n ≥ 5`. At `n = 2 * m` for `m ≥ 8`,
   `pow_two_le_countingBudget_double` gives `s ≥ 2^m`, and
   `countingHardLanguage_not_mem_PPoly` rules out every polynomial size bound.
   [Numerical bound](../PvsNP/Circuits/CountingBound.lean) · [Counting construction](../PvsNP/Complexity/CountingLowerBound.lean)
4. `exists_countingHardLanguage_even_length` gives an accepted word at
   each length `2 * m` for `m ≥ 8`. The constant false circuit is within
   budget, so disagreement with it forces acceptance on some word.
   `countingHardTable_certificates_too_long` uses these accepted lengths
   to show that the full `2^n`-bit truth table exceeds every fixed Cook
   certificate exponent on some accepted input. The open obligation is
   `countingHardLanguage ∈ NP`, which requires a fixed polynomial bound
   on certificates and a polynomial-time verifier for the bits of the
   selected table. That membership would give `P ≠ NP` by
   `p_ne_np_of_countingHardLanguage_mem_NP`.
   [Certificate bound and conditional separation](../PvsNP/Complexity/CountingLowerBound.lean) · [Cook's NP definition](../PvsNP/Complexity/Classes.lean)

## Zero padding and circuit bounds

1. An injective length profile `N` with `n ≤ N n` pads an `n`-bit word
   with `N n - n` zeros. `mem_zeroPaddedLanguage_iff` characterizes
   membership at a length `N n` by testing the first `n` bits and
   requiring an all-zero suffix. `zeroPad_mem_zeroPaddedLanguage_iff`
   identifies membership of each original word with that of its padded
   word.
   [Padding and membership](../PvsNP/Complexity/Padding.lean)
2. `liftPrefix` rewires a circuit to the corresponding prefix and keeps
   its gate count. `liftPrefixWithFalseSuffix` tests the suffix with at
   most `2 * m + 2` additional gates on `m` input bits, including the
   final AND. `restrictFalseSuffix` fixes all suffix inputs using one
   shared false gate. For polynomially bounded
   `N`, these constructions yield `zeroPaddedLanguage_mem_PPoly_iff`.
   [Circuit wiring](../PvsNP/Circuits/InputLayout.lean) · [Padding equivalence](../PvsNP/Complexity/Padding.lean)
3. `zeroPaddedCountingHard_mem_PPoly_iff` characterizes the padded
   counting language for any injective `N` with `n ≤ N n`. Membership
   in `PPoly` is equivalent to a polynomially bounded function `g`
   satisfying `2^n ≤ g (N n)` for every `n`. Restricting the suffix
   gives back an original-slice circuit. The strict lower bound above
   `⌊2^n / (8 * n)⌋` then bounds `2^n` by a polynomial in `N n`,
   using `n ≤ N n` and a constant to cover the finitely many small
   lengths. `truthTableCircuit` synthesizes any `n`-input Boolean function
   by splitting on the first bit. `truthTableCircuit_eval` proves it computes
   the function, and `truthTableCircuit_size_add_four` gives `5 * 2^n - 4`
   gates. Adding the suffix test proves the polynomial circuit bound in
   the padded length from a polynomial bound on `2^n` at that length.
   [Counting and padding](../PvsNP/Complexity/CountingPadding.lean) · [Truth-table circuit synthesis](../PvsNP/Circuits/TruthTableUpperBound.lean)
4. The full truth-table list has `2^(2^n)` entries. The full circuit
   list at the counting budget has at least `2^n` entries for `n ≥ 10`
   by `pow_two_le_length_countingCircuits`.
   `zeroPaddedCountingHard_mem_PPoly_of_truth_table_count` and
   `zeroPaddedCountingHard_mem_PPoly_of_circuit_count` show how polynomial
   bounds on these list lengths give polynomial-size circuits at padded
   lengths. The circuit-list result allows any finite cutoff below which
   the count is unconstrained. A Cook runtime bound requires a machine
   and a transition-count proof.
   [Padding consequences](../PvsNP/Complexity/CountingPadding.lean) · [Truth tables](../PvsNP/Circuits/TruthTable.lean)
5. `exists_countingHardLanguage_of_one_le_budget` gives an accepted word
   at every original length `n ≥ 10`, where `le_countingBudget` supplies
   the budget condition.
   `zeroPaddedCountingHard_mem_PPoly_of_full_table_certificates` uses
   these words to obtain the same upper bound from a polynomial bound on
   full-table certificate length on accepted padded words. For
   polynomially bounded `N`, `zeroPaddedCountingHard_not_mem_PPoly_of_polynomial`
   retains the original circuit hardness. A Cook NP verifier for that padded
   language would imply separation by `p_ne_np_of_zeroPaddedCountingHard_mem_NP`.
   [Accepted lengths](../PvsNP/Complexity/CountingLowerBound.lean) · [Certificates and separation](../PvsNP/Complexity/CountingPadding.lean)

## Cook verifier circuits and certificate bounds

1. `windowMappedStartExpr_eval` maps variable bits through the checking
   alphabet and hardwires the separator and the certificate symbols in
   the suffix. `Machine.exists_boundedCertificateCircuits` simulates the
   exact input `A.encode (List.ofFn x) y`. For a verifier with Cook exponent
   `k` and a polynomial certificate cap, use the clock
   `T = (n + cap n + 1)^k + k` with a centered `2 * T + 1`-cell window.
   One polynomial bounds the gate count for every `y` of length at most
   `cap n` at each instance length `n`. The lower bound uses correctness on
   encoded pairs. A Cook NP witness also supplies rejection of malformed words.
   [Mapped window input](../PvsNP/Circuits/WindowInput.lean) · [Verifier simulation](../PvsNP/Complexity/VerifierCircuits.lean)
2. `Machine.exists_candidateProjectionCircuits` takes the OR of the
   verifier circuits for the entries of a list `C_n`. Its bound is
   `|C_n| * g(n) + 1` for one polynomially bounded `g`, and the output
   checks whether a candidate is accepted. When these lists characterize
   a language and their lengths are polynomially bounded,
   `mem_PPoly_of_polynomialCertificateCandidates` gives polynomial-size
   circuits. The lists can be chosen separately at each length.
   [Candidate projection](../PvsNP/Complexity/VerifierCircuits.lean)
3. `countingHardLanguage_candidateCount_lower` compares this circuit
   construction to the counting-language gate lower bound. Any correct
   choice of candidate lists with polynomially bounded certificate lengths
   must satisfy `2^n ≤ |C_n| * g(n)` at every `n ≥ 10` for some
   polynomially bounded `g`. `acceptingCertificatesAtLength` keeps
   distinct candidates that the verifier accepts on at least one input
   of length `n`. `countingHardLanguage_acceptingCertificateCount_lower`
   preserves the lower bound with the cardinality of that set.
   [Candidate count lower bound](../PvsNP/Complexity/CountingVerifierBounds.lean)
4. `countingHardLanguage_certificateLength_lower` enumerates all
   certificates up to `cap n` over a `q`-symbol alphabet. Their count is
   at most `(cap n + 1) * q^(cap n)`, giving
   `2^n ≤ q^(cap n) * g(n)` at every `n ≥ 10` for some polynomially
   bounded `g`. The unary case is ruled out for polynomial caps by
   `countingHardLanguage_no_unaryCertificateVerifier`. For the binary
   encoding `encodePair`,
   `countingHardLanguage_binaryCertificateLength_lower` gives constants
   `C, d` such that `n ≤ cap n + C + d * (Nat.log2 (n + 1) + 1)` at
   these lengths. Cook's NP definition permits arbitrary fixed finite
   certificate alphabets and caps `n^k`. The obligation to give a correct
   Cook verifier for `countingHardLanguage` remains open.
   [Certificate enumeration](../PvsNP/Complexity/CertificateEnumeration.lean) · [Length lower bounds](../PvsNP/Complexity/CountingVerifierBounds.lean) · [Cook's NP definition](../PvsNP/Complexity/Classes.lean)

## Circuit minimization by streaming truth-table rows

1. `SizeBounded n s table` asks for an `n`-input circuit of size at most `s`
   computing the table in lexicographic row order. `rank_assignment_at` and
   `assignment_at_rank` prove that a row's big-endian binary value is its
   position. `truthTable_agree_on_take_iff` turns a list-prefix comparison into
   agreement at ranks below the prefix length. [Agreement](../PvsNP/MCSP/Agreement.lean) · [Row order](../PvsNP/MCSP/PrefixOrder.lean)
2. `matchesPrefix_append_bit_iff` identifies the exact local merge contract.
   The candidate must match the retained circuit at earlier ranks and the new
   bit at the next rank. `runStream_sound` preserves the size cap after the
   first successful update, counts the consumed rows, and represents all their
   values. `runStream_complete` uses any full-table witness as a valid candidate
   at each step. `searchStream_isSome_iff` checks the final count and obtains
   exact truth-table equality, including rejection of short and excess input.
   The exhaustive `referenceMerge` satisfies the same contract.
   [Local merge](../PvsNP/MCSP/StreamMerge.lean) · [Streaming search](../PvsNP/MCSP/Streaming.lean)
3. `decodeCircuit_encodeCircuit` proves round trips for a gate list with
   bounded size and valid wire references. With `w = log₂(n + s) + 1`, a
   circuit of `g` gates takes exactly `2w + g(3 + 2w)` bits. In
   `runStream_retained_encoding` use `max 1 s` as the cap to account for the
   initial one-gate seed and add an `n + 1` bit counter. The count can reach
   `2^n` on completion. `runStreamCounted_mergeCalls_le` charges at most one
   request per bit, including a merge that returns failure.
   [Circuit descriptions](../PvsNP/Circuits/Description.lean) · [State encoding and request counts](../PvsNP/MCSP/StreamResources.lean)
4. `ltRankCircuit_eval` computes the threshold predicate with exactly `2n+1`
   gates. `mergeViolationCircuit_eval_eq_true_iff` accepts precisely an earlier
   row with unequal values or the next row with the wrong bit.
   `mergeViolationCircuit_size_le` gives the bound
   `2 * old.size + 3 * candidate.size + 6 * n + 13`.
   `exists_bounded_merge_iff_short_code` gives an existential description of
   bounded length followed by a test for all `n`-bit rows. Its row check
   rejects malformed descriptions. [Rank comparator](../PvsNP/MCSP/RankCircuit.lean) · [Violation circuit](../PvsNP/MCSP/MergeViolation.lean) · [Binary witnesses](../PvsNP/MCSP/MergeWitness.lean)
5. `BooleanCircuit.satisfiable_toCNF_iff` uses clauses for each gate and
   forces the selected output wire to be true. The clauses use the same
   wire name wherever a gate output is reused.
   `mergeAgrees_iff_mergeViolationWord_not_mem_CNFSAT` proves that the ordinary
   binary CNF-SAT language decides whether a proposed merge has a violation.
   If `t` is the violation circuit's size bound, its CNF has size at most
   `10t + 2`, and the binary word with unary indices has length at most
   `1 + (n + t + 3)(10t + 2)`.
   [Circuit clauses](../PvsNP/Circuits/ToCNF.lean) · [Merge CNF](../PvsNP/MCSP/ViolationCNF.lean)
6. `mergePrefixFeasible_iff_checked_rows` handles a partial description
   by checking its extension, canonical padding, and all rows. Given an exact
   feasibility oracle, `mergeByPrefixSearch_correct` queries the empty prefix
   and tries one extension per bit of the padded description. The query count
   is at most `2w + s(3 + 2w) + 1`. `searchStream_prefixOracle_isSome_iff`
   supplies this merger to the stream and proves exact acceptance.
   [Prefix search](../PvsNP/MCSP/MergeSearch.lean) · [Streaming with prefix feasibility](../PvsNP/MCSP/MergeWitness.lean)
7. `Machine.haltsWithin_flipAnswer_iff` keeps the exact running time when
   swapping accept and reject. `mem_P_of_bounded_universal_of_p_eq_np`
   derives a Cook decider under `P = NP` for a bounded universal check given
   a polynomial-time verifier for its violations. Applying this to the
   merge predicates requires a uniform encoding and such a verifier.
   [Cook complementation](../PvsNP/Complexity/Complement.lean)

## Binary merge requests and Cook verifiers

1. `decodeMergeRequest_eq_some_iff` pairs an executable parser with the
   canonical request format. The arity and gate cap are unary and the row
   counter has `n + 1` binary bits. The old circuit takes a fixed padded
   field, and the remainder is the requested witness prefix.
   `mergeWitnessLength_le_of_decodeMergeRequest` bounds each candidate
   description by `11 * (request.length + 1)^2`.
   [Request encoding](../PvsNP/MCSP/Request.lean)
2. `Machine.pairedInput_haltsAt` represents two simulated symbols in each
   physical tape cell. A simulated move out of the cell becomes one physical
   move. A move to the other symbol of the same cell writes and moves right,
   then moves left to resume. The proof expands left and right half-tapes in
   their respective orders and handles the blank blocks in both directions.
   `mem_NP_of_packedCheckingLanguage_mem_P` uses this simulation to obtain
   a Cook checker on the entire `x#y` alphabet, including malformed words.
   [Tape simulation](../PvsNP/TuringMachine/PairedInput.lean) · [Packed checking languages](../PvsNP/Complexity/PackedPairs.lean)
3. `checkPackedMergePrefixViolation_eq_true_iff` connects an executable
   Boolean check to its binary checking language. On a valid inner query,
   a violating row certifies failure. The empty row certifies malformed inner
   queries, so complementation accepts only well-framed passing candidates.
   `mergePrefixLanguage_mem_P_of_p_eq_np` first projects the row certificate
   with bound `|query|`, complements the resulting decider, and projects
   the padded candidate with bound `|request|^9`.
   [Row checking and bounded projections](../PvsNP/MCSP/PrefixViolationLanguage.lean)
4. `runsValues_packedPairScan` recognizes canonical framing on raw binary
   input using at most `2 * input.length + 2` register instructions.
   `packedPairSyntax_mem_P` composes that scan with an answer instruction
   sequence, and the packed-offset lemmas locate data bits after nesting.
   `runsValues_binaryCompare` compares same-width little-endian fields
   without storing the numerical operands in unary. `compare_mergeRowField`
   identifies the comparison with that of the lexicographic row and the
   request counter. `runsValues_binaryField_circuit` does read a gate field
   into unary because its value is below `2 * (n + s + 1)`.
   [Packed pair decider](../PvsNP/TuringMachine/Registers/PackedPairDecision.lean) · [Nested offsets](../PvsNP/Complexity/PackedOffsets.lean) · [Binary comparison](../PvsNP/TuringMachine/Registers/BinaryCompare.lean) · [Gate fields](../PvsNP/TuringMachine/Registers/BinaryField.lean) · [Row comparison](../PvsNP/MCSP/TraceViolation.lean)
5. `BooleanCircuit.checkWireTrace_eq_true_iff` characterizes the exact
   evaluation trace and output bit. `exists_checkMergeTraceViolation_iff`
   characterizes a genuine disagreement on a single row with two traces
   totaling one bit per wire in the two circuits.
   `mem_mergePrefixViolationLanguage_iff_bounded_trace` packages the row,
   traces and answer bits into a certificate at most as long as the query.
   For an invalid query or candidate the empty certificate suffices.
   The checked implication `mergePrefixLanguage_mem_P_of_trace_register_run`
   asks for a total register program that returns the Boolean checker result
   on every word. The checked register simulation and a one-step answer
   read give a Cook decider from such a program.
   [Wire trace](../PvsNP/Circuits/WireTrace.lean) · [Trace certificate relation](../PvsNP/MCSP/TraceViolationLanguage.lean) · [Register decision bridge](../PvsNP/TuringMachine/Registers/Decision.lean) · [Verifier obligation](../PvsNP/MCSP/VerifierProgram.lean)
6. `clockedMergePrefix_query_run` starts the feasibility decider on each
   recorded query's canonical request. If the decider's Cook exponent is
   `k`, the call halts within `(26 * (n + s + 1)^2)^k + k` ticks. The retained
   circuit and query-length bounds select the canonical branch at each call.
   A physical streaming implementation must also construct the requests
   and transfer work-tape control between calls.
   [Clocked feasibility queries](../PvsNP/MCSP/ClockedPrefixOracle.lean)

## Counted trace checks on packed input

1. `checkPackedMergePrefixTraceViolation_eq_true_iff` connects the complete
   executable checker to the certificate relation. The checker rejects
   malformed outer pairs. Within a valid outer pair, a bad query takes the
   empty certificate. A properly formed query needs the exact row field,
   two traces, and two claimed outputs. Re-encoding the split certificate
   checks the high row bit and the full extent.
   [Executable trace checker](../PvsNP/MCSP/TraceChecker.lean)
2. `runsValues_scanNestedPairRegister` checks both packed pairs directly on
   the raw word and returns their lengths. The inner scan starts at reverse
   position `2 * (certificate.length + 1)` and skips one tag bit at a time.
   `runsValues_requestHeaderRegister` consumes both unary headers from
   ordinary position `3` at stride four and leaves the request suffix
   unread. `runsValues_fieldWidthRegister` computes `m.log2 + 1` from the
   unary bound `m` with polynomial cost, including the case `m = 0`.
   [Nested framing](../PvsNP/MCSP/NestedPairRegister.lean) · [Request headers](../PvsNP/MCSP/RequestHeaderRegister.lean) · [Runtime field width](../PvsNP/TuringMachine/Registers/FieldWidth.lean)
3. `runsValues_stridedField_of_reads` decodes each bounded circuit field.
   `runsValues_stridedCompare_of_reads` compares two fields of equal width
   stored at different strides. The comparator's bound depends on the input
   length, strides, and width. It can compare the row counter without putting
   its decoded natural number in a register.
   [Strided reads](../PvsNP/TuringMachine/Registers/StridedField.lean) · [Strided comparison](../PvsNP/TuringMachine/Registers/StridedCompare.lean)
4. `checkDecodedGate_eq_gateFromFields` identifies the numerical dispatch
   with the circuit parser and wire-trace check. The counted record checker
   reads the right operand, left operand, and opcode from right to left. It
   enforces earlier-wire references and checks the output through indexed
   trace reads. `runsValues_checkGateBlockRegister` repeats the same
   fragment over the gate count. `runsValues_checkCircuitGateBlock`
   equates zero failures with the gate-trace checker on the circuit's
   prepared layout. `packedCandidateGateBlockReady` establishes that
   layout for the candidate in the actual packed checker input, given its
   seed registers and exact trace length. The loop preserves unrelated
   registers and the output.
   [Gate decoder](../PvsNP/Circuits/DescriptionLayout.lean) · [Gate checks](../PvsNP/MCSP/GateRegister.lean) · [Record reads](../PvsNP/MCSP/GateRecordRegister.lean) · [Counted block](../PvsNP/MCSP/GateBlockRegister.lean) · [Packed setup](../PvsNP/MCSP/PackedGateBlock.lean)

The remaining hypothesis in `mergePrefixLanguage_mem_P_of_trace_checker_run`
is a polynomial all-input run that emits the exact Boolean checker result.
The bit layout and counted fragments above supply pieces of that run.
[Whole checker obligation](../PvsNP/MCSP/VerifierProgram.lean)

## Structural query and certificate checks

1. `readMergeRequestFields_isSome_iff` identifies the request split from the
   two header flags and the remaining body length. The minimum body length
   is `arity + 2 + oldPaddedLength`. Any excess is the requested prefix,
   whose length is bounded by the candidate's padded length. The old
   circuit uses cap `max 1 cap`, including when the candidate cap is zero.
   `runsValues_circuitLayoutRegister` computes each padded length from its
   unary arity and cap. `RequestShapeRegisterResult.valid_iff_request_fields`
   connects the counted length comparisons to a successful request split
   and the exact candidate length. The offset lemmas locate the stride-four
   windows for the counter, old circuit, and prefix.
   [Request split](../PvsNP/MCSP/RequestLayout.lean) · [Numeric circuit layout](../PvsNP/MCSP/CircuitLayoutRegister.lean) · [Length checks](../PvsNP/MCSP/RequestShapeRegister.lean) · [Packed offsets](../PvsNP/MCSP/PackedRequestLayout.lean)
2. `decodeMergeWitness_eq_some_iff_canonical` and
   `paddedCircuitDescriptionValid_iff_canonical` characterize the padded
   decoder by the claimed count, earlier-wire checks, output-wire bound,
   and zero padding. `runsValues_paddedDescriptionCount` reads the count
   before branching on its validity. `runsValues_paddedDescriptionRegister`
   runs the remaining checks after the count is in range and the windows are
   prepared. Its output bound and two zero failure counts are equivalent
   to the padded codec's validity predicate.
   [Decoder](../PvsNP/MCSP/DescriptionValidation.lean) · [Count read](../PvsNP/MCSP/PaddedFieldRegister.lean) · [Combined register checks](../PvsNP/MCSP/PaddedDescriptionRegister.lean)
3. `runsValues_seenFieldRegister_packed` separates the high counter bit
   from the count of true lower bits. This checks `seen ≤ 2 ^ arity`
   without converting the binary field into a unary register.
   `runsValues_packedRequestPrefix` compares the two promised prefix windows
   in place. `mergeTraceQueryFieldsValid_iff_padded` combines these
   conditions with the shape and decoder checks. For the empty certificate,
   `checkPackedMergePrefixTraceViolation_empty_iff` identifies the exact
   acceptance branch.
   [Counter bound](../PvsNP/MCSP/SeenFieldRegister.lean) · [Prefix scan](../PvsNP/MCSP/PrefixRegister.lean) · [Empty certificate](../PvsNP/MCSP/TraceQueryLayout.lean)
4. `checkPackedMergePrefixTraceViolation_eq_true_iff_certificateChecks`
   gives the other branch once the query is valid. The total certificate
   length, row high bit, input bits in both traces, gate equations, and
   output-wire reads each have a separate check. The row comparison
   distinguishes a changed earlier output from a wrong output at `seen`.
   [Certificate checks](../PvsNP/MCSP/TraceCertificateLayout.lean)

## Counted initialization and the one-way input model

1. `runsValues_traceHeaderRegister` measures the raw input, scans both
   packed frames, and initializes the two unary header reads from the
   measured request length. It preserves the framing flags and reports
   the exact header counts and remaining body length.
   [Header initialization](../PvsNP/MCSP/TraceHeaderRegister.lean)
2. `runsValues_traceExtentRegister_of_headers` reuses the four measured
   values for the extent calculation. It computes both padded lengths and
   circuit widths, using `max 1 cap` for the old circuit, then checks the
   body range and candidate length. Its clock depends only on the raw
   input length. `runsOutput_traceFrontRegister` emits the exact answer
   for all failures in framing, headers, or extents. On success it enters
   the continuation with the exact field split and candidate length.
   `runsValues_traceQueryBaseRegister_of_fields` uses the split lengths
   to compute both ordinary circuit addresses and the prefix start.
   `mergePrefixLanguage_mem_P_of_traceFront_continuation` is the resulting
   bounded-run obligation for the Cook verifier route.
   [Extent calculation](../PvsNP/MCSP/TraceExtentLink.lean) · [Raw dispatch](../PvsNP/MCSP/TraceExtentDispatch.lean) · [Cook verifier obligation](../PvsNP/MCSP/VerifierProgram.lean)
3. `runsValues_reverseWindowRegister` computes a reverse physical address
   by saturating subtraction from the measured input length. The guarded
   `runsValues_checkedDescriptionRegister` reads the gate count from the
   padded word and checks it against the cap before calculating the
   remaining offsets. It then initializes the output, gate, and padding
   scans and returns zero failures exactly for the padded decoder's
   validity predicate. `runsValues_preparedPrefixRegister` computes both
   prefix cursors from the measured lengths before comparing the fields.
   `runsValues_preparedSeenRegister` uses the header cursor and arity to
   initialize the binary counter check.
   [Reverse cursor](../PvsNP/TuringMachine/Registers/ReverseWindow.lean) · [Guarded circuit checker](../PvsNP/MCSP/CheckedDescriptionRegister.lean) · [Prefix setup](../PvsNP/MCSP/PreparedPrefixRegister.lean) · [Counter setup](../PvsNP/MCSP/PreparedSeenRegister.lean)
4. `BooleanCircuit.foldWithConstants_eval` proves the evaluator agrees
   under constant or aliased inputs. The folding algorithm retains only
   live gates and spends at most the original number of AND, OR, and NOT
   gates. `searchStream_isSome_iff_constantFree` gives the exact
   truth-table threshold in that basis for positive arity and cap at
   least two. The constant functions have exact strict-basis size two.
   [Folding](../PvsNP/Circuits/ConstantFolding.lean) · [Streaming threshold](../PvsNP/MCSP/ConstantFreeThreshold.lean)
5. `Machine.withOneWayInput_load` starts with the raw input on the one-way
   tape and a blank work tape. It copies and rewinds in `2N + 2` steps.
   `Machine.withOneWayInput_run` then couples each Cook tick to one work
   tick and `Machine.withOneWayInput_decides` transfers the verdict.
   This adapter retains the given Cook machine's running time. The
   magnification argument still needs a work-tape implementation that
   performs each stream update in a polynomial in the local resources.
   [One-way machine and adapter](../PvsNP/TuringMachine/OneWayInput.lean)

## Raw query dispatch and the magnification clock

1. `runsValues_queryCounterPrefixRegister` reads the high counter bit,
   counts the low ones, and compares the requested prefix. The counter is
   out of range exactly when both the high bit and a low bit are set.
   `runsValues_queryDescriptionsRegister` checks the old and candidate
   circuits directly and accumulates their failure flags. The two checks
   preserve their shared dimensions and addresses.
   [Counter and prefix](../PvsNP/MCSP/QueryCounterPrefixRegister.lean) · [Circuit pair](../PvsNP/MCSP/QueryDescriptionsRegister.lean)
2. `queryStructureReady_fromFront` supplies the seeds directly from the
   framing and extent results. `runsValues_queryStructureRegister` gives
   both counts, the retained layout, and the exact structural predicate.
   `PolynomiallyBounded.exists_uniform` maximizes the instruction charge
   over a finite box of parameter values at each input length. The bound
   applies even when a raw claimed count exceeds the cap.
   [Prepared register map](../PvsNP/MCSP/QueryStructureFront.lean) · [Counted structure](../PvsNP/MCSP/QueryStructureRegister.lean) · [Uniform clock](../PvsNP/Complexity/UniformBounds.lean)
3. `runsOutput_ifRegisterPositive` restores its test register before
   calling either branch. `exists_traceStructuredVerifierClock` then
   connects the raw front end to the structural checks. It emits the
   exact answer on a malformed query and calls the continuation with a
   decoded valid query on the other branch.
   [Restoring branch](../PvsNP/TuringMachine/Registers/PositiveBranch.lean) · [Raw structural verifier](../PvsNP/MCSP/StructuredVerifier.lean)
4. `runsOutput_traceCertificateDispatch` checks the expected certificate
   length before reading the high row bit. A malformed certificate for a
   valid query emits `false`. A valid layout preserves the initial values
   for the continuation. `runsValues_traceInputRegister` checks the two
   trace input prefixes against the raw row, with independent flags for
   the old and candidate circuits.
   [Certificate guard](../PvsNP/MCSP/TraceCertificateDispatch.lean) · [Trace input checks](../PvsNP/MCSP/TraceInputRegister.lean)
5. `le_magnificationGateCap_iff` and `le_magnificationTime_iff` express the
   fractional exponents using integer power inequalities.
   `eventually_magnification_clock` chooses a threshold denominator after
   the polynomial row charge is fixed and before choosing the arity cutoff.
   `mem_oneWayDTIME_magnification_of_rows` adds the bounds for small valid
   lengths and lengths that are not powers of two. The resulting
   separation implication still requires the timed row algorithm under
   `P = NP` and the one-way lower bound at the same thresholds.
   [Exact thresholds and conditional separation](../PvsNP/MCSP/MagnificationClock.lean)

## Auditing private bridge lemmas

The [main audit](../PvsNP/Verification/Axioms.lean) lists the public theorem
dependencies. To print dependencies of the private containment lemmas
individually, run their source and the audit commands together from the
repository root after building.

```sh
export LEAN_NUM_THREADS=1
{
  cat PvsNP/Complexity/Containment.lean
  printf '\n#print axioms PvsNP.%s\n' \
    scan_prefix rewind_prefix valid_preparation lift_tick lift_run lift_start \
    run_valid_verifier run_missing_separator run_nonempty_certificate \
    verifier_valid_halted verifier_accepts verifier_polyTime verifier_decides
} | lake env lean --stdin
```

The verifier's internal simulation lemmas can be audited in the same way.

```sh
{
  cat PvsNP/SAT/VerifierMachine.lean
  printf '\n#print axioms PvsNP.SATMachine.%s\n' \
    cursor_step_le read_cursor advance_assignmentTape run_one run_bit run_delimiter run_parser
} | lake env lean --stdin
```

The pigeonhole strategy keeps its state and invariants private. Their axiom
dependencies can be printed from the strategy's source.

```sh
{
  cat PvsNP/SAT/PigeonholeStrategy.lean
  printf '\n#print axioms PvsNP.Pigeonhole.%s\n' \
    uniqueBy_cons GameState.le_score_of_falsified_row GameState.noConflict \
    GameState.putFalse GameState.putTrue strategy
} | lake env lean --stdin
```

The private initialization, transition, and counting lemmas in the layered
circuit simulation can be checked from their source.

```sh
{
  cat PvsNP/Circuits/WindowInput.lean
  printf '\n#print axioms PvsNP.Circuits.%s\n' \
    inputSymbolExpr inputSymbolExpr_eval 'windowStart_cells_getElem?'
} | lake env lean --stdin

{
  cat PvsNP/Circuits/WindowSimulation.lean
  printf '\n#print axioms PvsNP.Circuits.%s\n' \
    stepGateBound stepGateBound_polynomiallyBounded enumerate mem_enumerate stepLayer acceptLayer \
    stepLayer_eval repeat_stepLayer_eval stepLayer_size_le windowRunFromLayered_size_le \
    windowRunFromLayered_size_polynomiallyBounded acceptLayer_size_le startLayer startLayer_eval \
    startLayer_size_le startLayer_size_polynomiallyBounded
} | lake env lean --stdin
```

The transducer output layer's private read and size lemmas can also be
audited individually.

```sh
{
  cat PvsNP/Circuits/TransducerOutput.lean
  printf '\n#print axioms PvsNP.Circuits.%s\n' \
    readRelative_size_le readRelative_eval outputLayer_size_le
} | lake env lean --stdin
```

The counting lower bound uses private lemmas for enumeration, table
indexing, and growth estimates. Audit them after the clean build.

```sh
audit_counting_private() {
  pvsnp_source_file=$1
  shift
  {
    cat "$pvsnp_source_file"
    printf '\n#print axioms %s\n' "$@"
  } | lake env lean --stdin
}

audit_counting_private PvsNP/Circuits/Enumerate.lean \
  PvsNP.Circuits.length_flatMap_eq_of_length PvsNP.Circuits.mem_binaryGates \
  PvsNP.Circuits.length_binaryGates PvsNP.Circuits.cons_castWires \
  PvsNP.Circuits.castWires_trans PvsNP.Circuits.eval_castWires \
  PvsNP.Circuits.mem_enumerateNetworks_castWires PvsNP.Circuits.size_constantPadding
audit_counting_private PvsNP/Circuits/TruthTable.lean \
  PvsNP.Circuits.wordOfFn_injective PvsNP.Circuits.assignmentWords_nodup \
  PvsNP.Circuits.idxOf_assignmentWords_at
audit_counting_private PvsNP/Circuits/CountingBound.lean \
  PvsNP.Circuits.twice_succ_lt_two_pow PvsNP.Circuits.sixteen_mul_le_two_pow
audit_counting_private PvsNP/Complexity/CountingLowerBound.lean \
  PvsNP.Circuits.hardTruthTable_notMem_circuitTables \
  PvsNP.PolynomiallyBounded.not_eventually_dominates_pow_two
```

Use the same function to audit the private padding declarations.

```sh
audit_counting_private PvsNP/Circuits/InputLayout.lean \
  PvsNP.Circuits.zeroExtension PvsNP.Circuits.eval_zeroExtension \
  PvsNP.Circuits.BooleanCircuit.requireFalse \
  PvsNP.Circuits.BooleanCircuit.eval_requireFalse_eq_true \
  PvsNP.Circuits.BooleanCircuit.size_requireFalse \
  PvsNP.Circuits.BooleanCircuit.suffixIndices PvsNP.Circuits.BooleanCircuit.mem_suffixIndices
audit_counting_private PvsNP/Complexity/Padding.lean \
  PvsNP.take_ofFn_eq PvsNP.drop_ofFn_all_false_iff PvsNP.ofFn_zeroExtend
audit_counting_private PvsNP/Complexity/CountingPadding.lean \
  PvsNP.Circuits.eight_mul_square_le_two_pow
```

The private MCSP proofs and circuit-encoding declarations use the same function.

```sh
audit_counting_private PvsNP/Circuits/Description.lean \
  PvsNP.Circuits.readField PvsNP.Circuits.readField_bits PvsNP.Circuits.gateRecord \
  PvsNP.Circuits.encodeGate PvsNP.Circuits.length_encodeGate PvsNP.Circuits.readBinaryGate \
  PvsNP.Circuits.readGateFields PvsNP.Circuits.readGate_encode \
  PvsNP.Circuits.encodeNetwork PvsNP.Circuits.length_encodeNetwork PvsNP.Circuits.ParsedNetwork \
  PvsNP.Circuits.readNetwork PvsNP.Circuits.readNetwork_encode PvsNP.Circuits.decodeCircuitChecked
audit_counting_private PvsNP/Circuits/ToCNF.lean \
  PvsNP.Circuits.Network.assignment_extend PvsNP.Circuits.BooleanCircuit.literalIndex_lt_of_mem_toCNF \
  PvsNP.Circuits.BooleanCircuit.length_encodeClause_le PvsNP.Circuits.BooleanCircuit.length_encode_le
audit_counting_private PvsNP/MCSP/Agreement.lean PvsNP.MCSP.all_agrees_eq_true_iff
audit_counting_private PvsNP/MCSP/MergeSearch.lean PvsNP.MCSP.prefixSearchOracle_spec
audit_counting_private PvsNP/MCSP/PrefixOrder.lean \
  PvsNP.MCSP.rankFrom PvsNP.MCSP.rankFrom_eq 'PvsNP.MCSP.rank_of_getElem?'
audit_counting_private PvsNP/MCSP/StreamResources.lean \
  PvsNP.MCSP.mergeCharge PvsNP.MCSP.countedPushBit PvsNP.MCSP.mergeCharge_le_one \
  PvsNP.MCSP.mergeCharge_eq_one_of_pushBit_ne_none PvsNP.MCSP.foldl_pushBit_none \
  PvsNP.MCSP.foldl_countedPushBit_spec
```

Audit the private declarations for the binary checker and register proofs with the same function.

```sh
audit_counting_private PvsNP/Circuits/DescriptionLayout.lean PvsNP.Circuits.gateFromFields_of_tag \
  PvsNP.Circuits.readField_append PvsNP.Circuits.encodeGate_eq_encodeGateFields \
  PvsNP.Circuits.encodeNetwork_eq_gateRecords PvsNP.Circuits.take_drop_flatMap_fixed \
  PvsNP.Circuits.gateFields_fit PvsNP.Circuits.traceInstruction_fields_fit
audit_counting_private PvsNP/Circuits/WireTrace.lean PvsNP.Circuits.Gate.some_lookup \
  PvsNP.Circuits.Gate.readEarlier_fin PvsNP.Circuits.BooleanCircuit.lookup_of_trace_prefix \
  PvsNP.Circuits.BooleanCircuit.take_wireTrace
audit_counting_private PvsNP/Complexity/PackedOffsets.lean PvsNP.taggedData \
  PvsNP.length_taggedData 'PvsNP.getElem?_taggedData' PvsNP.packedPair_layout
audit_counting_private PvsNP/Complexity/PackedPairs.lean PvsNP.unpackVerifier \
  PvsNP.unpackVerifier_packInput PvsNP.packInput_of_unpackVerifier
audit_counting_private PvsNP/MCSP/ClockedPrefixOracle.lean PvsNP.MCSP.exhaustivePrefixAnswer \
  PvsNP.MCSP.exhaustivePrefixAnswer_eq_true_iff
audit_counting_private PvsNP/MCSP/GateBlockRegister.lean PvsNP.MCSP.indexedFailure \
  PvsNP.MCSP.gateFailureCount_eq_sum PvsNP.MCSP.foldl_add_indexed \
  PvsNP.MCSP.gateFailureCount_reverse_fold PvsNP.MCSP.GateRecordBits.fields_encode \
  PvsNP.MCSP.withOutputSuffix PvsNP.MCSP.execute_withOutputSuffix PvsNP.MCSP.run_withOutputSuffix
audit_counting_private PvsNP/MCSP/GateRecordRegister.lean PvsNP.MCSP.RecordField \
  PvsNP.MCSP.RecordField.target PvsNP.MCSP.fieldLanes PvsNP.MCSP.fieldLanes_injective \
  PvsNP.MCSP.loadRecordWidth PvsNP.MCSP.readRecordField PvsNP.MCSP.clearRecordOperands \
  PvsNP.MCSP.GateRecordLayout.reverse_eq PvsNP.MCSP.GateRecordLayout.read_right \
  PvsNP.MCSP.GateRecordLayout.read_left PvsNP.MCSP.GateRecordLayout.read_tag \
  PvsNP.MCSP.decodedFieldValues PvsNP.MCSP.runsValues_recordField \
  PvsNP.MCSP.runsValues_loadRecordWidth
audit_counting_private PvsNP/MCSP/GateRegister.lean PvsNP.MCSP.Operand PvsNP.MCSP.Operand.lane \
  PvsNP.MCSP.wireReadLanes PvsNP.MCSP.wireReadLanes_injective PvsNP.MCSP.comparisonLanes \
  PvsNP.MCSP.comparisonLanes_injective PvsNP.MCSP.readWire PvsNP.MCSP.readEarlierWire \
  PvsNP.MCSP.countFailure PvsNP.MCSP.requireZero PvsNP.MCSP.agreesWith PvsNP.MCSP.checkOutput \
  PvsNP.MCSP.checkConstant PvsNP.MCSP.checkNot PvsNP.MCSP.binaryOutput PvsNP.MCSP.checkBinary \
  PvsNP.MCSP.gateBranch PvsNP.MCSP.checkAt_eq_agreesWith PvsNP.MCSP.recordFailure \
  PvsNP.MCSP.BoundedRun PvsNP.MCSP.runCountFailure PvsNP.MCSP.runReadWire \
  PvsNP.MCSP.runCheckOutput PvsNP.MCSP.operandBound PvsNP.MCSP.runReadEarlier \
  PvsNP.MCSP.runRequireZero PvsNP.MCSP.runCheckConstant PvsNP.MCSP.runCheckNot \
  PvsNP.MCSP.runCheckBinary PvsNP.MCSP.runGateBranch PvsNP.MCSP.gateReady_clearOpcode
audit_counting_private PvsNP/MCSP/NestedPairRegister.lean PvsNP.MCSP.comparisonLanes \
  PvsNP.MCSP.comparisonLanes_injective PvsNP.MCSP.innerWindowLanes \
  PvsNP.MCSP.innerWindowLanes_injective PvsNP.MCSP.scanNestedInner \
  PvsNP.MCSP.runsValues_scanNestedInner
audit_counting_private PvsNP/MCSP/PackedGateBlock.lean PvsNP.MCSP.candidateGateFinalBit_lt \
  PvsNP.MCSP.candidateGateFinalBit_add_steps
audit_counting_private PvsNP/MCSP/PrefixViolationLanguage.lean \
  PvsNP.MCSP.packedMergePrefixQuery_unique PvsNP.MCSP.mergeWitnessLength_le_pow_of_decode \
  PvsNP.MCSP.rowInput PvsNP.MCSP.ofFn_rowInput
audit_counting_private PvsNP/MCSP/Request.lean PvsNP.MCSP.old_size_of_decodeMergeWitness \
  PvsNP.MCSP.parseMergeRequest PvsNP.MCSP.parseMergeRequest_encodeMergeRequest \
  PvsNP.MCSP.mergeWitnessLength_le_quadratic
audit_counting_private PvsNP/MCSP/RequestHeaderRegister.lean PvsNP.MCSP.requestUnaryLanes \
  PvsNP.MCSP.requestUnaryLanes_injective
audit_counting_private PvsNP/MCSP/TraceChecker.lean PvsNP.MCSP.DecodedTraceQuery \
  PvsNP.MCSP.decodeTraceQuery PvsNP.MCSP.decodeTraceQuery_eq_some_iff \
  PvsNP.MCSP.rowFromLittleEndian PvsNP.MCSP.rowFromLittleEndian_ofFn PvsNP.MCSP.checkTraceFields \
  PvsNP.MCSP.mergeTraceLengths PvsNP.MCSP.checkTraceFields_eq_true_iff
audit_counting_private PvsNP/MCSP/TraceViolationLanguage.lean \
  PvsNP.MCSP.checkMergePrefixRow_of_validTraceQuery \
  PvsNP.MCSP.checkMergePrefixRow_of_invalidTraceQuery
audit_counting_private PvsNP/TuringMachine/PairedInput.lean PvsNP.Machine.Block \
  PvsNP.Machine.blockInhabited PvsNP.Machine.selectBlock PvsNP.Machine.writeBlock \
  PvsNP.Machine.leavesBlock PvsNP.Machine.PairState PvsNP.Machine.readyState \
  PvsNP.Machine.packedSymbol PvsNP.Machine.blockSymbols PvsNP.Machine.expandBlocks \
  PvsNP.Machine.expandBlocks_cons PvsNP.Machine.projectBlocks PvsNP.Machine.projectBlocks_head \
  PvsNP.Machine.projectBlocks_write PvsNP.Machine.projectBlocks_move_inside \
  PvsNP.Machine.projectBlocks_move_across PvsNP.Machine.readyConfig PvsNP.Machine.virtualConfig \
  PvsNP.Machine.pairedInput_simulates_tick PvsNP.Machine.pairedInput_simulates_run \
  PvsNP.Machine.projectBlocks_first PvsNP.Machine.virtualConfig_start
audit_counting_private PvsNP/TuringMachine/Registers/BinaryCompare.lean \
  PvsNP.RegisterMachine.Fragment.clearLane PvsNP.RegisterMachine.Fragment.writeOrdering \
  PvsNP.RegisterMachine.Fragment.readRight PvsNP.RegisterMachine.Fragment.comparePair \
  PvsNP.RegisterMachine.Fragment.runsValues_clearLane \
  PvsNP.RegisterMachine.Fragment.runsValues_writeOrdering \
  PvsNP.RegisterMachine.Fragment.runsValues_binaryCompare_words
audit_counting_private PvsNP/TuringMachine/Registers/BinaryField.lean \
  PvsNP.RegisterMachine.Fragment.clearTemporary PvsNP.RegisterMachine.Fragment.fieldIteration \
  PvsNP.RegisterMachine.Fragment.runsValues_clearTemporary \
  PvsNP.RegisterMachine.Fragment.iterationValues \
  PvsNP.RegisterMachine.Fragment.runsValues_fieldIteration \
  PvsNP.RegisterMachine.Fragment.runsValues_binaryField_word
audit_counting_private PvsNP/TuringMachine/Registers/Decision.lean \
  PvsNP.RegisterMachine.readAnswer PvsNP.RegisterMachine.readAnswer_halt \
  PvsNP.RegisterMachine.readAnswer_polyTime PvsNP.RegisterMachine.readAnswer_decides
audit_counting_private PvsNP/TuringMachine/Registers/FieldWidth.lean \
  PvsNP.RegisterMachine.Fragment.widthCompareLanes \
  PvsNP.RegisterMachine.Fragment.widthCompareLanes_injective \
  PvsNP.RegisterMachine.Fragment.prepareWidth PvsNP.RegisterMachine.Fragment.growWidth \
  PvsNP.RegisterMachine.Fragment.widthIteration PvsNP.RegisterMachine.Fragment.clearPower \
  PvsNP.RegisterMachine.Fragment.pow_width_le PvsNP.RegisterMachine.Fragment.guarded_width_eq_min \
  PvsNP.RegisterMachine.Fragment.widthValues \
  PvsNP.RegisterMachine.Fragment.runsValues_prepareWidth \
  PvsNP.RegisterMachine.Fragment.runsValues_widthIteration \
  PvsNP.RegisterMachine.Fragment.runsValues_widthCountdown \
  PvsNP.RegisterMachine.Fragment.runsValues_clearPower
audit_counting_private PvsNP/TuringMachine/Registers/LessThan.lean \
  PvsNP.RegisterMachine.Fragment.orderingCompareRules \
  PvsNP.RegisterMachine.Fragment.run_ifOrdering_test
audit_counting_private PvsNP/TuringMachine/Registers/PackedPairDecision.lean \
  PvsNP.emitPackedValidity PvsNP.run_emitPackedValidity PvsNP.packedSyntaxProgram \
  PvsNP.run_packedSyntaxProgram
audit_counting_private PvsNP/TuringMachine/Registers/PackedPairScan.lean \
  PvsNP.RegisterMachine.Fragment.reverseData PvsNP.RegisterMachine.Fragment.scanReverse_data \
  PvsNP.RegisterMachine.Fragment.reverse_packedPair \
  PvsNP.RegisterMachine.Fragment.scanReverse_sound \
  PvsNP.RegisterMachine.Fragment.packedScanPhaseCode PvsNP.RegisterMachine.Fragment.scanReadConfig \
  PvsNP.RegisterMachine.Fragment.scanCounts PvsNP.RegisterMachine.Fragment.scanCounts_data \
  PvsNP.RegisterMachine.Fragment.run_scanRead
audit_counting_private PvsNP/TuringMachine/Registers/PackedPairWindow.lean \
  PvsNP.RegisterMachine.Fragment.boundary PvsNP.RegisterMachine.Fragment.windowTransition \
  PvsNP.RegisterMachine.Fragment.WindowProgress PvsNP.RegisterMachine.Fragment.windowStep \
  PvsNP.RegisterMachine.Fragment.foldl_windowStep_sink PvsNP.RegisterMachine.Fragment.windowCounts \
  PvsNP.RegisterMachine.Fragment.windowStep_data PvsNP.RegisterMachine.Fragment.windowCounts_data \
  PvsNP.RegisterMachine.Fragment.foldl_windowStep_counts \
  PvsNP.RegisterMachine.Fragment.countSymbol PvsNP.RegisterMachine.Fragment.recordWindowStep \
  PvsNP.RegisterMachine.Fragment.windowBody PvsNP.RegisterMachine.Fragment.windowFinish \
  PvsNP.RegisterMachine.Fragment.countedValues PvsNP.RegisterMachine.Fragment.recordValues \
  PvsNP.RegisterMachine.Fragment.runsValues_recordWindowStep \
  PvsNP.RegisterMachine.Fragment.runsValues_dispatchKey PvsNP.RegisterMachine.Fragment.bodyValues \
  PvsNP.RegisterMachine.Fragment.runsValues_windowBody \
  PvsNP.RegisterMachine.Fragment.windowLoopCost \
  PvsNP.RegisterMachine.Fragment.runsValues_windowLoop \
  PvsNP.RegisterMachine.Fragment.runsValues_windowFinish
audit_counting_private PvsNP/TuringMachine/Registers/StridedCompare.lean \
  PvsNP.RegisterMachine.Fragment.decrementBy \
  PvsNP.RegisterMachine.Fragment.stridedCompareIteration \
  PvsNP.RegisterMachine.Fragment.runsValues_decrementBy \
  PvsNP.RegisterMachine.Fragment.stridedCompareIterationValues \
  PvsNP.RegisterMachine.Fragment.runsValues_stridedCompareIteration \
  PvsNP.RegisterMachine.Fragment.runsValues_stridedCompare_words
audit_counting_private PvsNP/TuringMachine/Registers/StridedField.lean \
  PvsNP.RegisterMachine.Fragment.stridedIteration \
  PvsNP.RegisterMachine.Fragment.stridedIterationValues \
  PvsNP.RegisterMachine.Fragment.runsValues_stridedIteration \
  PvsNP.RegisterMachine.Fragment.runsValues_stridedField_word
audit_counting_private PvsNP/TuringMachine/Registers/UnaryFieldWindow.lean \
  PvsNP.RegisterMachine.Fragment.unaryReadBranch PvsNP.RegisterMachine.Fragment.unaryWindowRead \
  PvsNP.RegisterMachine.Fragment.unaryWindowLink PvsNP.RegisterMachine.Fragment.unaryReadValues \
  PvsNP.RegisterMachine.Fragment.runsValues_unaryReadBranch \
  PvsNP.RegisterMachine.Fragment.runsValues_unaryWindowRead \
  PvsNP.RegisterMachine.Fragment.run_unaryWindow_read \
  PvsNP.RegisterMachine.Fragment.run_unaryWindow_stop \
  PvsNP.RegisterMachine.Fragment.run_unaryWindow_resume
# Private checks behind raw request and trace certificate validation.
audit_counting_private PvsNP/Circuits/DescriptionValidation.lean \
  PvsNP.Circuits.gateWindow \
  PvsNP.Circuits.take_gate_subfields \
  PvsNP.Circuits.readField_eq_window \
  PvsNP.Circuits.readGate_eq_window \
  PvsNP.Circuits.readGate_eq_none_of_short \
  PvsNP.Circuits.fields_of_gateFromFields \
  PvsNP.Circuits.fieldValue_lt \
  PvsNP.Circuits.readGate_sound \
  PvsNP.Circuits.readNetwork_sound \
  PvsNP.Circuits.readField_sound \
  PvsNP.Circuits.readNetwork_of_windows \
  PvsNP.Circuits.slice_take_of_le \
  PvsNP.Circuits.circuitDescriptionLength_mono \
  PvsNP.Circuits.eq_replicate_false_of_all_not
audit_counting_private PvsNP/MCSP/CircuitLayoutRegister.lean \
  PvsNP.MCSP.layoutWidthLanes \
  PvsNP.MCSP.layoutWidthLanes_injective
audit_counting_private PvsNP/MCSP/GateStructureRegister.lean \
  PvsNP.MCSP.requireEarlier \
  PvsNP.MCSP.structureBranch \
  PvsNP.MCSP.structureOperandBound \
  PvsNP.MCSP.runStructureRequireEarlier \
  PvsNP.MCSP.runStructureRequireZero \
  PvsNP.MCSP.runStructureBranch \
  PvsNP.MCSP.indexedStructureFailure
audit_counting_private PvsNP/MCSP/PackedRequestLayout.lean \
  PvsNP.MCSP.getElem?_packed_request_segment \
  PvsNP.MCSP.requestHeaders \
  PvsNP.MCSP.length_requestHeaders
audit_counting_private PvsNP/MCSP/PackedStructureBlock.lean \
  PvsNP.MCSP.descriptionGateRecord_fits \
  PvsNP.MCSP.descriptionGateReversePosition_step
audit_counting_private PvsNP/MCSP/PaddedFieldRegister.lean \
  PvsNP.MCSP.packedRequestLength_ge \
  PvsNP.MCSP.PaddedDescriptionWindow.read_suffix
audit_counting_private PvsNP/MCSP/PrefixRegister.lean \
  PvsNP.MCSP.getElem?_reverse_of_forward
audit_counting_private PvsNP/MCSP/RequestLayout.lean \
  PvsNP.MCSP.readMergeRequestBody \
  PvsNP.MCSP.readMergeRequestBody_eq_some_iff \
  PvsNP.MCSP.readMergeRequestBody_isSome_iff \
  PvsNP.MCSP.fieldValue_eq_zero_iff
audit_counting_private PvsNP/MCSP/RequestShapeRegister.lean \
  PvsNP.MCSP.addShapePair \
  PvsNP.MCSP.countShapeLess \
  PvsNP.MCSP.countCandidateMismatch \
  PvsNP.MCSP.runsValues_addShapePair \
  PvsNP.MCSP.shapeCompareLanes \
  PvsNP.MCSP.runsValues_countShapeLess \
  PvsNP.MCSP.runsValues_countCandidateMismatch
audit_counting_private PvsNP/MCSP/SeenFieldRegister.lean \
  PvsNP.MCSP.seenLowLanes \
  PvsNP.MCSP.seenLowLanes_injective \
  PvsNP.MCSP.readSeenHigh \
  PvsNP.MCSP.countTrue_eq_zero_iff_all_not
audit_counting_private PvsNP/MCSP/TraceCertificateLayout.lean \
  PvsNP.MCSP.rowField_of_layout \
  PvsNP.MCSP.checks_of_encoded \
  PvsNP.MCSP.checks_iff_exact_fields
audit_counting_private PvsNP/TuringMachine/Registers/StridedZeroWindow.lean \
  PvsNP.RegisterMachine.Fragment.paddingViolation \
  PvsNP.RegisterMachine.Fragment.zeroWindowIteration \
  PvsNP.RegisterMachine.Fragment.zeroIterationValues \
  PvsNP.RegisterMachine.Fragment.runsValues_zeroWindowIteration \
  PvsNP.RegisterMachine.Fragment.runsValues_stridedZeroWindow_badBits
# Private checks behind counted initialization and model bridges.
audit_counting_private PvsNP/Circuits/ConstantFolding.lean \
  PvsNP.Circuits.referenceValue \
  PvsNP.Circuits.GateFold \
  PvsNP.Circuits.GateFold.eval \
  PvsNP.Circuits.foldBinaryConstant \
  PvsNP.Circuits.foldBinary \
  PvsNP.Circuits.foldGate \
  PvsNP.Circuits.foldBinary_eval \
  PvsNP.Circuits.foldGate_eval \
  PvsNP.Circuits.chargedRest_le \
  PvsNP.Circuits.chargedKeep \
  PvsNP.Circuits.referenceValue_castSucc \
  PvsNP.Circuits.FoldedNetwork \
  PvsNP.Circuits.foldNetwork \
  PvsNP.Circuits.BooleanCircuit.endpoints_ne_of_small_constantFree
audit_counting_private PvsNP/MCSP/CheckedDescriptionRegister.lean \
  PvsNP.MCSP.offsetRole \
  PvsNP.MCSP.offsetRole_injective \
  PvsNP.MCSP.positionRole \
  PvsNP.MCSP.positionRole_injective \
  PvsNP.MCSP.installPosition \
  PvsNP.MCSP.runsValues_installPosition \
  PvsNP.MCSP.installValue \
  PvsNP.MCSP.runsValues_installValue \
  PvsNP.MCSP.countRole \
  PvsNP.MCSP.countRole_injective \
  PvsNP.MCSP.compareRole \
  PvsNP.MCSP.compareRole_injective \
  PvsNP.MCSP.checkedBranch \
  PvsNP.MCSP.runsValues_checkedBranch \
  PvsNP.MCSP.countNonzero \
  PvsNP.MCSP.runsValues_countNonzero \
  PvsNP.MCSP.countDescriptionFailures \
  PvsNP.MCSP.checkedDescriptionBody \
  PvsNP.MCSP.runsValues_countDescriptionFailures
audit_counting_private PvsNP/MCSP/DescriptionCountRegister.lean \
  PvsNP.MCSP.countReaderLane \
  PvsNP.MCSP.countReaderLane_injective \
  PvsNP.MCSP.clearCountPosition \
  PvsNP.MCSP.runsValues_clearCountPosition
audit_counting_private PvsNP/MCSP/DescriptionOffsetRegister.lean \
  PvsNP.MCSP.copyTime \
  PvsNP.MCSP.productTime \
  PvsNP.MCSP.copyPredecessor \
  PvsNP.MCSP.offsetCodeLength \
  PvsNP.MCSP.offsetGateStart \
  PvsNP.MCSP.runsValues_copyPredecessor \
  PvsNP.MCSP.runsValues_offsetProduct \
  PvsNP.MCSP.runsValues_offsetCodeLength \
  PvsNP.MCSP.runsValues_offsetGateStart
audit_counting_private PvsNP/MCSP/PreparedPrefixRegister.lean \
  PvsNP.MCSP.prefixSourceLane \
  PvsNP.MCSP.prefixPositionLane \
  PvsNP.MCSP.prefixBaseBias \
  PvsNP.MCSP.prefixOffsetLane \
  PvsNP.MCSP.prefixOffsetLane_injective \
  PvsNP.MCSP.prefixCompareLane \
  PvsNP.MCSP.prefixCompareLane_injective \
  PvsNP.MCSP.clearPrefixLane \
  PvsNP.MCSP.preparePrefixPosition \
  PvsNP.MCSP.runsValues_clearPrefixLane \
  PvsNP.MCSP.runsValues_preparePrefixPosition
audit_counting_private PvsNP/MCSP/PreparedSeenRegister.lean \
  PvsNP.MCSP.preparedSeenScanLane \
  PvsNP.MCSP.preparedSeenScanLane_injective \
  PvsNP.MCSP.clearSeenPosition \
  PvsNP.MCSP.runsValues_clearSeenPosition
audit_counting_private PvsNP/MCSP/TraceExtentDispatch.lean \
  PvsNP.MCSP.invalidQuery_of_bad_extents
audit_counting_private PvsNP/MCSP/TraceExtentLink.lean \
  PvsNP.MCSP.fieldWidth_le \
  PvsNP.MCSP.witnessLength_le \
  PvsNP.MCSP.layoutCost_le \
  PvsNP.MCSP.parsedHeaderCounts_le
audit_counting_private PvsNP/MCSP/TraceExtentRegister.lean \
  PvsNP.MCSP.traceCircuitLayoutLanes_injective \
  PvsNP.MCSP.traceShapeLanes_injective \
  PvsNP.MCSP.extentCompareLanes \
  PvsNP.MCSP.extentCompareLanes_injective \
  PvsNP.MCSP.loadOldCap \
  PvsNP.MCSP.mergeWitnessLength_poly \
  PvsNP.MCSP.runsValues_loadOldCap
audit_counting_private PvsNP/MCSP/TraceHeaderDispatch.lean \
  PvsNP.MCSP.testHeaderLane \
  PvsNP.MCSP.runsOutput_testHeaderLane \
  PvsNP.MCSP.runsOutput_dispatchBit \
  PvsNP.MCSP.invalidQuery_of_missing_inner \
  PvsNP.MCSP.invalidQuery_of_bad_header \
  PvsNP.MCSP.positive_flag
audit_counting_private PvsNP/MCSP/TraceHeaderRegister.lean \
  PvsNP.MCSP.pairHeaderCompareLanes \
  PvsNP.MCSP.pairHeaderCompareLanes_injective \
  PvsNP.MCSP.prepareTraceHeaders \
  PvsNP.MCSP.requestHeaderRegisterCost_mono \
  PvsNP.MCSP.runsValues_prepareTraceHeaders
audit_counting_private PvsNP/TuringMachine/OneWayInput.lean \
  PvsNP.Machine.oneWayPhaseCode \
  PvsNP.Machine.withOneWayInput_run_copy \
  PvsNP.Machine.withOneWayInput_run_rewind
audit_counting_private PvsNP/TuringMachine/Registers/ReverseWindow.lean \
  PvsNP.RegisterMachine.Fragment.reverseCopyDecrement \
  PvsNP.RegisterMachine.Fragment.clearReverseLane \
  PvsNP.RegisterMachine.Fragment.runsValues_reverseCopyDecrement \
  PvsNP.RegisterMachine.Fragment.runsValues_clearReverseLane
```

The private declarations for SAT witness search use the same namespace.

```sh
audit_search_private() {
  pvsnp_source_file=$1
  shift
  {
    cat "$pvsnp_source_file"
    printf '\n#print axioms PvsNP.SATSearch.%s\n' "$@"
  } | lake env lean --stdin
}

audit_search_private PvsNP/SAT/SearchOracleQuery.lean unitPrefix_eq sat_unit_bit
audit_search_private PvsNP/Circuits/PrefixQueryWiring.lean \
  queryLayout constantsNetwork constantWire liftedWire eval_constantWire eval_liftedWire \
  eval_queryLayout queryTemplate eval_queryTemplate length_queryTemplate queryCircuitOf \
  eval_queryCircuitOf size_queryCircuitOf
audit_search_private PvsNP/SAT/OracleSearch.lean queryCharge_le
audit_search_private PvsNP/SAT/SearchCircuits.lean \
  nextBitCircuit prefixCircuit prefixCircuit_eval_input prefixCircuitWord length_prefixCircuitWord \
  prefixCircuitWord_succ prefixCircuit_size_le witnessCircuit_eval_assignment
```

Use the audit function that takes fully qualified names for the returning-call
proofs.

```sh
audit_counting_private PvsNP/TuringMachine/TrackCall/Tracks.lean \
  PvsNP.TrackCall.scratchMap PvsNP.TrackCall.pairCells \
  PvsNP.TrackCall.nth_mk_pairCells PvsNP.TrackCall.pairTracks PvsNP.TrackCall.nth_pairTracks \
  PvsNP.TrackCall.map_pairTracks_fst
audit_counting_private PvsNP/TuringMachine/TrackCall/Simulation.lean \
  PvsNP.TrackCall.write_move_nth_ne PvsNP.TrackCall.simulate_tick
audit_counting_private PvsNP/TuringMachine/TrackCall/Rewind.lean \
  PvsNP.TrackCall.rewind_tick_at_origin PvsNP.TrackCall.rewind_tick_off_origin \
  PvsNP.TrackCall.finishing_tick PvsNP.TrackCall.rewind_at_origin PvsNP.TrackCall.rewind_progress \
  PvsNP.TrackCall.rewind_move_nth PvsNP.TrackCall.rewind_run_preserved
audit_counting_private PvsNP/TuringMachine/TrackCall/Return.lean PvsNP.TrackCall.firstReturningHalt
audit_counting_private PvsNP/SAT/OracleCalls.lean PvsNP.SATSearch.exists_ticks_of_pointwise
```

The scratch loader's private proofs use the same audit function.

```sh
audit_counting_private PvsNP/TuringMachine/TrackCall/Loader/Travel.lean \
  PvsNP.TrackCall.Loader.tick_move PvsNP.TrackCall.Loader.run_left_steps \
  PvsNP.TrackCall.Loader.run_right_left
audit_counting_private PvsNP/TuringMachine/TrackCall/Loader/Write.lean \
  PvsNP.TrackCall.Loader.tick_writeForward PvsNP.TrackCall.Loader.run_writeForward_from
audit_counting_private PvsNP/TuringMachine/TrackCall/Loader/Load.lean \
  PvsNP.TrackCall.Loader.tape_eq_of_nth
```

The in-place query edit and iteration proofs use both audit functions.

```sh
audit_search_private PvsNP/SAT/AppendQuery.lean \
  encode_ne_nil dropLast_encode_append prefixQueryFrom_encode length_encode_append_comm
audit_search_private PvsNP/SAT/QueryBuffer.lean \
  encodeIndex_eq_replicate appendEdits_bits appendEdits_tail_map appendEdits_pending_map \
  'getElem?_singleMark' appendEdits_tail_at appendEdits_pending_at
audit_search_private PvsNP/SAT/QueryIndices.lean \
  queryTail_le unary_stop_lt_tail prefixQueryLengthFrom_next
audit_counting_private PvsNP/TuringMachine/TrackCall/QueryEdit/Travel.lean \
  PvsNP.TrackCall.QueryEdit.tick_move PvsNP.TrackCall.QueryEdit.scanPosition \
  PvsNP.TrackCall.QueryEdit.scanPosition_zero PvsNP.TrackCall.QueryEdit.scanPosition_succ \
  PvsNP.TrackCall.QueryEdit.run_scan
audit_counting_private PvsNP/TuringMachine/TrackCall/QueryEdit/AppendBody.lean \
  PvsNP.TrackCall.QueryEdit.tick_editRight PvsNP.TrackCall.QueryEdit.run_closing \
  PvsNP.TrackCall.QueryEdit.run_writeIndex
audit_counting_private PvsNP/TuringMachine/TrackCall/QueryEdit/Commit.lean \
  PvsNP.TrackCall.QueryEdit.tick_commit
audit_counting_private PvsNP/TuringMachine/TrackCall/QueryEdit/LoaderBridge.lean \
  PvsNP.TrackCall.QueryEdit.savedMap PvsNP.TrackCall.QueryEdit.tracksAt_nth_origin \
  PvsNP.TrackCall.QueryEdit.start_nth_eq_queryBit
audit_search_private PvsNP/SAT/QueryIterationSAT.lean length_appendPrefixQuery_le
audit_search_private PvsNP/SAT/QueryIterationProgram.lean \
  commitCode commitCode_injective phaseCode loaderLabel loaderStep
```

The crossing-sequence proof uses the audit function for fully qualified names.

```sh
audit_counting_private PvsNP/TuringMachine/Crossing/Splice.lean \
  PvsNP.Machine.absoluteConfig_eq PvsNP.Machine.AgreesOn PvsNP.Machine.agreesOn_tick \
  PvsNP.Machine.tick_splice_left PvsNP.Machine.tick_splice_right \
  PvsNP.Machine.splice_stay_left PvsNP.Machine.splice_stay_right \
  PvsNP.Machine.splice_cross PvsNP.Machine.replay_after_step
audit_counting_private PvsNP/TuringMachine/Crossing/Counting.lean \
  PvsNP.Crossing.card_short_le PvsNP.Crossing.column_length_lower
audit_counting_private PvsNP/TuringMachine/Crossing/Time.lean \
  PvsNP.Machine.crossing_cut_eq PvsNP.Machine.sum_crossing_charge_le_one
audit_counting_private PvsNP/SAT/CrossingFamily.lean \
  PvsNP.SATCrossing.signedLiteral PvsNP.SATCrossing.signedLiteral_sat \
  PvsNP.SATCrossing.literalIndex_signedLiteral PvsNP.SATCrossing.addressClause \
  PvsNP.SATCrossing.addressClause_sat PvsNP.SATCrossing.tableFormula_sat \
  PvsNP.SATCrossing.tautology \
  PvsNP.SATCrossing.clauseWidth PvsNP.SATCrossing.length_encodeClause_eq \
  PvsNP.SATCrossing.length_addressClause PvsNP.SATCrossing.length_addressBlocks \
  PvsNP.SATCrossing.length_encode_tableFormula PvsNP.SATCrossing.length_paddingFormula
audit_counting_private PvsNP/SAT/CrossingTimeLowerBound.lean \
  PvsNP.SATCrossing.absolute_rejects_diagonal PvsNP.SATCrossing.splice_diagonal_start \
  PvsNP.SATCrossing.diagonal_transcripts_injective
```

The parity and full binary-basis proofs use the same audit function.

```sh
audit_counting_private PvsNP/Circuits/PairRestriction.lean \
  PvsNP.Circuits.pairCube_agree PvsNP.Circuits.parity_rows_ne
audit_counting_private PvsNP/Circuits/BinaryBasisPair.lean \
  PvsNP.Circuits.cube_agree_at PvsNP.Circuits.parity_rows_different PvsNP.Circuits.cube_of_old \
  PvsNP.Circuits.cube_promote PvsNP.Circuits.exclusive_gate_factor
audit_counting_private PvsNP/Circuits/BinaryBasisBridge.lean \
  PvsNP.Circuits.lowerBinaryFunction PvsNP.Circuits.eval_lowerBinaryFunction \
  PvsNP.Circuits.size_lowerBinaryFunction_le PvsNP.Circuits.lowerGate PvsNP.Circuits.eval_lowerGate \
  PvsNP.Circuits.size_lowerGate_le PvsNP.Circuits.lowerFrom PvsNP.Circuits.eval_lowerFrom \
  PvsNP.Circuits.size_lowerFrom_le PvsNP.Circuits.initial
audit_counting_private PvsNP/SAT/CircuitCloseParity.lean \
  PvsNP.SATCircuitBounds.signed PvsNP.SATCircuitBounds.unitBits \
  PvsNP.SATCircuitBounds.length_unitBits PvsNP.SATCircuitBounds.encodeIndex_replicate \
  PvsNP.SATCircuitBounds.encode_signed_unit_cons PvsNP.SATCircuitBounds.closeClauses \
  PvsNP.SATCircuitBounds.true_cons_replicate_append PvsNP.SATCircuitBounds.encode_closeClauses \
  PvsNP.SATCircuitBounds.sat_closeClauses PvsNP.SATCircuitBounds.closeFormula_satisfiable \
  PvsNP.SATCircuitBounds.pairWord PvsNP.SATCircuitBounds.pairWord_set_left \
  PvsNP.SATCircuitBounds.pairWord_set_right PvsNP.SATCircuitBounds.wordInput \
  PvsNP.SATCircuitBounds.ofFn_wordInput PvsNP.SATCircuitBounds.cnfsat_close_pair_with_pin
audit_counting_private PvsNP/SAT/CircuitParityRestriction.lean \
  PvsNP.SATCircuitBounds.unit PvsNP.SATCircuitBounds.unitBits \
  PvsNP.SATCircuitBounds.encode_unit_cons PvsNP.SATCircuitBounds.length_encodeIndex \
  PvsNP.SATCircuitBounds.length_unitBits PvsNP.SATCircuitBounds.unit_sat \
  PvsNP.SATCircuitBounds.positiveBits PvsNP.SATCircuitBounds.encode_positive_append \
  PvsNP.SATCircuitBounds.beforeBits PvsNP.SATCircuitBounds.betweenBits \
  PvsNP.SATCircuitBounds.anchorUnits PvsNP.SATCircuitBounds.afterBits \
  PvsNP.SATCircuitBounds.pairWord PvsNP.SATCircuitBounds.pairFormula \
  PvsNP.SATCircuitBounds.pairWord_eq_encode PvsNP.SATCircuitBounds.length_beforeBits \
  PvsNP.SATCircuitBounds.length_betweenBits PvsNP.SATCircuitBounds.length_anchorBits \
  PvsNP.SATCircuitBounds.length_afterBits PvsNP.SATCircuitBounds.length_pairWord \
  PvsNP.SATCircuitBounds.anchor_sat PvsNP.SATCircuitBounds.pairWord_mem_CNFSAT_iff \
  PvsNP.SATCircuitBounds.parityInput PvsNP.SATCircuitBounds.ofFn_parityInput \
  PvsNP.SATCircuitBounds.HasUnitRestriction PvsNP.SATCircuitBounds.restriction_of_units \
  PvsNP.SATCircuitBounds.long_pair_restriction
audit_counting_private PvsNP/SAT/CircuitParitySize.lean \
  PvsNP.SATCircuitBounds.parityInteriorWires
audit_counting_private PvsNP/SAT/CircuitBinaryBasisSize.lean \
  PvsNP.SATCircuitBounds.cnfsat_binaryBasis_sensitive PvsNP.SATCircuitBounds.basisInteriorWires
```

The palette crossing and rational-clock proofs use the same audit function.

```sh
audit_counting_private PvsNP/SAT/CrossingPalette.lean \
  PvsNP.SATCrossing.Palette.signedLiteral_sat PvsNP.SATCrossing.Palette.three_mul_gt_payloadIndex \
  PvsNP.SATCrossing.Palette.le_payloadIndex PvsNP.SATCrossing.Palette.payloadIndex_injective \
  PvsNP.SATCrossing.Palette.header_sat PvsNP.SATCrossing.Palette.header_unique \
  PvsNP.SATCrossing.Palette.rowClause_sat PvsNP.SATCrossing.Palette.side_sat
audit_counting_private PvsNP/SAT/CrossingBlockPadding.lean \
  PvsNP.SATCrossing.rawBlockLength_positive_unit
audit_counting_private PvsNP/SAT/CrossingPaletteBlocks.lean \
  PvsNP.SATCrossing.Palette.rawBlockLength_le PvsNP.SATCrossing.Palette.raw_side_le \
  PvsNP.SATCrossing.Palette.raw_header_le PvsNP.SATCrossing.Palette.padding_room \
  PvsNP.SATCrossing.Palette.left_fits PvsNP.SATCrossing.Palette.right_fits \
  PvsNP.SATCrossing.Palette.combined_blocks_mem_CNFSAT_iff PvsNP.SATCrossing.Palette.middle_room \
  PvsNP.SATCrossing.Palette.length_middleBlock
audit_counting_private PvsNP/SAT/CrossingPaletteTime.lean \
  PvsNP.SATCrossing.Palette.middle_clock_lower_bound \
  PvsNP.SATCrossing.Palette.exists_rejecting_of_common_bound
audit_counting_private PvsNP/SAT/CrossingPaletteWorstCase.lean \
  PvsNP.SATCrossing.Palette.width_succ_le
audit_counting_private PvsNP/SAT/CrossingPowerBound.lean \
  PvsNP.SATCrossing.width_mul_rows_le_time PvsNP.SATCrossing.row_bound_of_power_clock
audit_counting_private PvsNP/SAT/CrossingTimeLowerBound.lean \
  PvsNP.SATCrossing.absolute_rejects_diagonal PvsNP.SATCrossing.splice_diagonal_start \
  PvsNP.SATCrossing.diagonal_transcripts_injective
```
