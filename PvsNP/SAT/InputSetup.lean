module

public import PvsNP.SAT.VerifierTape

public import Mathlib.Basic.Finite.Sum

/-! # Validating a SAT verifier input on the tape

The setup prefix writes a left sentinel, sweeps right to validate the pair,
and returns left to the sentinel. The final move enters the verifier's
initial control state with the head back at the start of the formula.
-/

@[expose] public section

namespace PvsNP.SATMachine

open Turing

/-- The setup control distinguishes the two sides of the unique separator. -/
inductive SetupState where
  | start
  | placeBoundary
  | beforeSeparator
  | afterSeparator
  | rewind
  deriving DecidableEq

private def setupCode : SetupState → Fin 5
  | .start => 0
  | .placeBoundary => 1
  | .beforeSeparator => 2
  | .afterSeparator => 3
  | .rewind => 4

instance : Finite SetupState :=
  Finite.of_injective setupCode (by intro x y h; cases x <;> cases y <;> simp_all [setupCode])

/-- Add a validator that leaves a left sentinel to an arbitrary verifier program. -/
abbrev withInputSetup {Q : Type} [Finite Q] (entry : Q)
    (program : Q → Symbol → ((SetupState ⊕ Q) ⊕ Bool) × Symbol × Dir) :
    Machine VerifierSymbol where
  State := SetupState ⊕ Q
  Symbol := SATMachine.Symbol
  stateFinite := inferInstance
  symbolFinite := SATMachine.symbolFinite
  initial := .inl .start
  blank := .blank
  input := SATMachine.input
  input_ne_blank := SATMachine.input_ne_blank
  transition
    | .inr q, a => program q a
    | .inl .start, a => ⟨.inl (.inl .placeBoundary), a, .left⟩
    | .inl .placeBoundary, .blank => ⟨.inl (.inl .beforeSeparator), .leftEnd, .right⟩
    | .inl .beforeSeparator, .bit b => ⟨.inl (.inl .beforeSeparator), .bit b, .right⟩
    | .inl .beforeSeparator, .delimiter => ⟨.inl (.inl .afterSeparator), .delimiter, .right⟩
    | .inl .afterSeparator, .bit b => ⟨.inl (.inl .afterSeparator), .bit b, .right⟩
    | .inl .afterSeparator, .blank => ⟨.inl (.inl .rewind), .blank, .left⟩
    | .inl .rewind, .bit b => ⟨.inl (.inl .rewind), .bit b, .left⟩
    | .inl .rewind, .delimiter => ⟨.inl (.inl .rewind), .delimiter, .left⟩
    | .inl .rewind, .leftEnd => ⟨.inl (.inr entry), .leftEnd, .right⟩
    | .inl _, a => ⟨.inr false, a, .right⟩

variable {Q : Type} [Finite Q] (entry : Q)
  (program : Q → Symbol → ((SetupState ⊕ Q) ⊕ Bool) × Symbol × Dir)

local notation "M" => withInputSetup entry program

private abbrev tape (left right : List Symbol) : (M).Tape :=
  (M).tapeFromLists left right

private abbrev shift (d : Dir) (t : (M).Tape) : (M).Tape :=
  @Tape.move _ (M).tapeInhabited d t

private abbrev cfg (q : SetupState) (l r : List Symbol) : (M).Config :=
  ⟨.inl (.inl q), tape entry program l r⟩

private theorem run_place_boundary (pair : VerifierWord) :
    (M).run 2 ((M).start pair) =
      cfg entry program .beforeSeparator [.leftEnd] (pair.map input) := by
  change (M).tick (⟨.inl (.inl .placeBoundary), shift entry program .left
    (tape entry program [] (pair.map input))⟩ : (M).Config) = _
  have leftEq := (M).move_tapeFromLists_left_nil (pair.map input)
  have goLeft := congrArg (fun t ↦ (M).tick ⟨.inl (.inl .placeBoundary), t⟩) leftEq
  have writeBoundary := (M).tick_tapeFromLists_cons (.inl .placeBoundary) []
    (pair.map input) .blank rfl
  have goRight := congrArg (fun t ↦ (⟨.inl (.inl .beforeSeparator), t⟩ : (M).Config))
    ((M).move_tapeFromLists_right_cons [] (pair.map input) .leftEnd)
  exact goLeft.trans (writeBoundary.trans goRight)

private theorem scan_bits (q : SetupState) (hq : q = .beforeSeparator ∨ q = .afterSeparator)
    (bits : BinaryWord) (l r : List Symbol) :
    (M).run bits.length (cfg entry program q l (bits.map Symbol.bit ++ r)) =
      cfg entry program q ((bits.map Symbol.bit).reverse ++ l) r := by
  have h (s : Symbol) (hs : s ∈ bits.map Symbol.bit) :
      (M).transition (.inl q) s = ⟨.inl (.inl q), s, .right⟩ := by
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hs
    rcases hq with rfl | rfl <;> rfl
  simpa only [List.length_map] using (M).run_sweep_right (.inl q) (bits.map Symbol.bit) l r h

private theorem tick_separator (l r : List Symbol) :
    (M).tick (cfg entry program .beforeSeparator l (.delimiter :: r)) =
      cfg entry program .afterSeparator (.delimiter :: l) r := by
  exact congrArg (fun t ↦ (⟨.inl (.inl .afterSeparator), t⟩ : (M).Config))
    ((M).move_tapeFromLists_right_cons l r .delimiter)

private theorem tick_rewind_blank (l : List Symbol) :
    (M).tick (cfg entry program .afterSeparator l []) =
      ⟨.inl (.inl .rewind), shift entry program .left (tape entry program l [])⟩ := rfl

private theorem rewind_word (x y : BinaryWord) :
    let raw := x.map Symbol.bit ++ .delimiter :: y.map Symbol.bit
    (M).run raw.length ⟨.inl (.inl .rewind), shift entry program .left
        (tape entry program (raw.reverse ++ [.leftEnd]) [])⟩ =
      ⟨.inl (.inl .rewind), shift entry program .left (tape entry program [.leftEnd] raw)⟩ := by
  dsimp only
  let raw := x.map Symbol.bit ++ .delimiter :: y.map Symbol.bit
  have h (s : Symbol) (hs : s ∈ raw.reverse) :
      (M).transition (.inl .rewind) s = ⟨.inl (.inl .rewind), s, .left⟩ := by
    simp only [raw, List.mem_reverse, List.mem_append, List.mem_cons] at hs
    rcases hs with hs | rfl | hs
    · obtain ⟨b, _, rfl⟩ := List.mem_map.mp hs
      rfl
    · rfl
    · obtain ⟨b, _, rfl⟩ := List.mem_map.mp hs
      rfl
  simpa only [raw, List.length_reverse, List.reverse_reverse, List.append_nil] using
    (M).run_sweep_left (.inl .rewind) raw.reverse [.leftEnd] [] h

private theorem tick_accept_setup (r : List Symbol) :
    (M).tick ⟨.inl (.inl .rewind), shift entry program .left (tape entry program [.leftEnd] r)⟩ =
      ⟨.inl (.inr entry), tape entry program [.leftEnd] r⟩ := by
  change (M).tick (cfg entry program .rewind [] (.leftEnd :: r)) = _
  exact congrArg (fun t ↦ (⟨.inl (.inr entry), t⟩ : (M).Config))
    ((M).move_tapeFromLists_right_cons [] r .leftEnd)

/-- A valid pair reaches the verifier's entry state in exactly two complete sweeps and
four further moves. The only tape change is insertion of the left sentinel. -/
theorem withInputSetup_valid (x y : BinaryWord) :
    (M).run (2 * (encodePair x y).length + 4) ((M).start (encodePair x y)) =
      ⟨.inl (.inr entry), (M).tapeFromLists [.leftEnd] ((encodePair x y).map input)⟩ := by
  let raw := x.map Symbol.bit ++ .delimiter :: y.map Symbol.bit
  have clocks : 2 * (encodePair x y).length + 4 =
      2 + x.length + 1 + y.length + 1 + raw.length + 1 := by
    simp only [length_encodePair, raw, List.length_append, List.length_cons, List.length_map]
    omega
  have mapped : (encodePair x y).map input = raw := input_encodePair x y
  rw [clocks, mapped, Machine.run_add, Machine.run_add, Machine.run_add, Machine.run_add,
    Machine.run_add, Machine.run_add, run_place_boundary, mapped]
  have hScan := scan_bits entry program .beforeSeparator (Or.inl rfl) x [.leftEnd]
    (.delimiter :: y.map Symbol.bit)
  change (M).run 1 ((M).run raw.length ((M).run 1 ((M).run y.length ((M).run 1
    ((M).run x.length (cfg entry program .beforeSeparator [.leftEnd] raw)))))) = _
  rw [hScan]
  have hScanY := scan_bits entry program .afterSeparator (Or.inr rfl) y
    (.delimiter :: ((x.map Symbol.bit).reverse ++ [.leftEnd])) []
  simp only [List.append_nil] at hScanY
  simp only [Machine.run_succ, Machine.run_zero, tick_separator entry program,
    hScanY, tick_rewind_blank entry program]
  have eqLeft : (y.map Symbol.bit).reverse ++
      .delimiter :: ((x.map Symbol.bit).reverse ++ [.leftEnd]) = raw.reverse ++ [.leftEnd] := by
    simp [raw, List.reverse_append, List.reverse_cons, List.append_assoc]
  rw [eqLeft, rewind_word entry program x y]
  exact tick_accept_setup entry program raw

private theorem bits_or_separator (pair : VerifierWord) :
    (∃ bits : BinaryWord, pair = bits.map some) ∨
      ∃ (bits : BinaryWord) (rest : VerifierWord), pair = bits.map some ++ none :: rest := by
  induction pair with
  | nil => exact Or.inl ⟨[], rfl⟩
  | cons a w ih =>
    cases a with
    | none => exact Or.inr ⟨[], w, rfl⟩
    | some b =>
      rcases ih with ⟨bits, rfl⟩ | ⟨bits, rest, rfl⟩
      · exact Or.inl ⟨b :: bits, rfl⟩
      · exact Or.inr ⟨b :: bits, rest, rfl⟩

/-- Every malformed pair rejects during the forward validation sweep. -/
theorem withInputSetup_malformed (pair : VerifierWord) (bad : decodePair pair = none) :
    ∃ t ≤ pair.length + 3, ((M).run t ((M).start pair)).state = .inr false := by
  have map_bits (w : BinaryWord) : (w.map some).map input = w.map Symbol.bit :=
    by simp only [List.map_map]; rfl
  rcases bits_or_separator pair with ⟨bits, rfl⟩ | ⟨bits, rest, rfl⟩
  · refine ⟨2 + bits.length + 1, by simp only [List.length_map]; omega, ?_⟩
    rw [Machine.run_add, Machine.run_add, run_place_boundary, map_bits,
      ← List.append_nil (bits.map Symbol.bit),
      scan_bits entry program .beforeSeparator (Or.inl rfl)]
    rfl
  · rcases bits_or_separator rest with ⟨cert, rfl⟩ | ⟨cert, rest, rfl⟩
    · rw [← encodePair_eq, decodePair_encodePair] at bad
      cases bad
    · refine ⟨2 + bits.length + 1 + cert.length + 1, ?_, ?_⟩
      · simp only [List.length_append, List.length_cons, List.length_map]
        omega
      · rw [Machine.run_add, Machine.run_add, Machine.run_add, Machine.run_add,
          run_place_boundary]
        simp only [List.map_append, List.map_cons, map_bits, input_none,
          scan_bits entry program .beforeSeparator (Or.inl rfl), Machine.run_succ, Machine.run_zero,
          tick_separator entry program, scan_bits entry program .afterSeparator (Or.inr rfl)]
        rfl

end PvsNP.SATMachine
