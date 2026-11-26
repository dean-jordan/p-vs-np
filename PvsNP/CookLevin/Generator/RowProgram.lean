module

public import PvsNP.CookLevin.Generator.Parameters
public import PvsNP.CookLevin.Generator.Rows
public import PvsNP.TuringMachine.Registers.SimulationBound

/-! # Compiled polynomial transducer for the tableau's row section -/

@[expose] public section

namespace PvsNP.CookLevin

open RegisterMachine RegisterMachine.Fragment

/-- The two stages share the initialized width and stride. Each other row
register is initially zero and sits outside the parameter registers. -/
structure RowProgramLanes (R : Type) where
  parameters : ParameterLane ↪ R
  rows : RowLane ↪ R
  width : rows .width = parameters .width
  stride : rows .stride = parameters .stride
  fresh : ∀ lane, lane ≠ .width → lane ≠ .stride → ∀ p, rows lane ≠ parameters p

variable {R : Type} (lanes : RowProgramLanes R)

/-- The binary row section, excluding the surrounding formula blocks and terminator. -/
def binaryTableauRows (k d states symbols : Nat) (x : BinaryWord) : BinaryWord :=
  let t := horizon x.length k d
  let width := 2 * t + 1
  tableauRowsOutput states symbols width (Tableau.atomStride states width symbols) t []

/-- Compute the initialized dimensions, then emit the complete row section. -/
def rowProgramFragment (k d states symbols : Nat) : Fragment R :=
  (parameterPrelude lanes.parameters k d states symbols).seq
    (rowsFragment lanes.rows (lanes.parameters .horizon) states symbols)

variable [DecidableEq R]

/-- The register instruction budget, including the closing halt. -/
def rowProgramTimeBound (n k d states symbols : Nat) : Nat :=
  parameterTime n k d states symbols + rowsTimeBound lanes.rows (lanes.parameters .horizon)
    (parameterValues lanes.parameters n k d states symbols) states symbols + 1

theorem rowProgramTimeBound_polynomiallyBounded (k d states symbols : Nat) :
    PolynomiallyBounded (fun n ↦ rowProgramTimeBound lanes n k d states symbols) := by
  let lit := PolynomiallyBounded.const
  have hTicks := horizon_polynomiallyBounded k d
  have hWidth := ((lit 2).mul hTicks).add (lit 1)
  have hStride := ((lit states).add hWidth).add (hWidth.mul (lit symbols))
  have hRows := rowsTimeBound_polynomiallyBounded lanes.rows (lanes.parameters .horizon)
    states symbols (v := fun n ↦ parameterValues lanes.parameters n k d states symbols)
    (by simpa only [parameterValues_at] using hTicks)
    (by simpa only [lanes.stride, parameterValues_at, Tableau.atomStride] using hStride)
    (by simpa only [lanes.width, parameterValues_at] using hWidth)
  exact ((parameterTime_polynomiallyBounded k d states symbols).add hRows).add (lit 1)

omit [DecidableEq R] in
private theorem horizon_disjoint (lane : RowLane) :
    lanes.parameters .horizon ≠ lanes.rows lane := by
  by_cases hWidth : lane = .width
  · subst lane
    rw [lanes.width]
    exact lanes.parameters.injective.ne (by decide)
  by_cases hStride : lane = .stride
  · subst lane
    rw [lanes.stride]
    exact lanes.parameters.injective.ne (by decide)
  exact (lanes.fresh lane hWidth hStride .horizon).symm

/-- A linked normal run of the parameter prelude and every row block. -/
theorem run_rowProgramFragment (k d states symbols : Nat) (x : BinaryWord) :
    ∃ cost, cost + 1 ≤ rowProgramTimeBound lanes x.length k d states symbols ∧
      (rowProgramFragment lanes k d states symbols).RunsOutput x cost
        (fun _ ↦ 0) (parameterValues lanes.parameters x.length k d states symbols) []
        (binaryTableauRows k d states symbols x) := by
  let v := parameterValues lanes.parameters x.length k d states symbols
  have zero (lane : RowLane) (hWidth : lane ≠ .width) (hStride : lane ≠ .stride) :
      v (lanes.rows lane) = 0 :=
    parameterValues_outside lanes.parameters x.length k d states symbols (lanes.rows lane)
      (lanes.fresh lane hWidth hStride)
  have fieldZero (lane : ExactlyOneLane) : v (rowFieldLanes lanes.rows lane) = 0 :=
    zero (.field lane) (fun eq ↦ by cases eq) (fun eq ↦ by cases eq)
  have hReady : RowReady lanes.rows v := by
    refine ⟨⟨fieldZero .base, fieldZero .count,
      zero .multiplier (by decide) (by decide),
      zero .preparationScratch (by decide) (by decide)⟩, ?_, fieldZero .left, fieldZero .right⟩
    simp [ExactlyOneScratchZero, fieldZero]
  obtain ⟨ticks, hTicks, hRows⟩ := run_rowsFragment lanes.rows (lanes.parameters .horizon)
    states symbols x [] v (horizon_disjoint lanes) (zero .time (by decide) (by decide))
    hReady (zero .position (by decide) (by decide))
  have hWidth : v (lanes.rows .width) = 2 * horizon x.length k d + 1 := by
    simp only [v, lanes.width, parameterValues_at]
  have hStride : v (lanes.rows .stride) =
      Tableau.atomStride states (2 * horizon x.length k d + 1) symbols := by
    simp only [v, lanes.stride, parameterValues_at]
  have hHorizon : v (lanes.parameters .horizon) = horizon x.length k d :=
    parameterValues_at lanes.parameters x.length k d states symbols .horizon
  rw [hWidth, hStride, hHorizon] at hRows
  have hPrep := (run_parameterPrelude lanes.parameters k d states symbols x).withOutput []
  exact ⟨_, Nat.add_le_add_right (Nat.add_le_add_left hTicks _) 1, hPrep.seq hRows⟩

omit [DecidableEq R] in
/-- Closing a linked row program gives a polynomial-time Cook transducer. -/
theorem binaryTableauRows_polynomialTimeMap_of_layout [Finite R]
    (layout : RowProgramLanes R) (k d states symbols : Nat) :
    PolynomialTimeMap (binaryTableauRows k d states symbols) := by
  classical
  let program := rowProgramFragment layout k d states symbols
  apply polynomialTimeMap_of_run program.entry program.close
    (rowProgramTimeBound_polynomiallyBounded layout k d states symbols)
  intro x
  obtain ⟨cost, hCost, hRun⟩ := run_rowProgramFragment layout k d states symbols x
  let final : program.Cfg :=
    ⟨some none, parameterValues layout.parameters x.length k d states symbols,
      none, binaryTableauRows k d states symbols x⟩
  have hNormal : program.run x cost (Config.initial program.entry) = some final := hRun
  have hHalt := Fragment.run_close hNormal rfl rfl
  exact ⟨cost + 1, hCost, { final with pc := none }, hHalt, rfl, rfl⟩

/-- Register numbers used by the parameter prelude in the concrete allocation. -/
def rowProgramParameterIndex : ParameterLane → Fin 21
  | .length => 0
  | .capacity => 1
  | .pairBound => 2
  | .horizon => 3
  | .width => 4
  | .stride => 5
  | .work => 6
  | .scratch => 7

/-- Register numbers used by the row loop in the concrete allocation. -/
def rowProgramRowIndex : RowLane → Fin 21
  | .width => 4
  | .stride => 5
  | .time => 8
  | .position => 9
  | .multiplier => 10
  | .preparationScratch => 11
  | .field .base => 12
  | .field .count => 13
  | .field .left => 14
  | .field .right => 15
  | .field .index => 16
  | .field .additionScratch => 17
  | .field .leftCopy => 18
  | .field .rightCopy => 19
  | .field .comparisonScratch => 20

/-- A concrete 21-register allocation with the width and stride shared. -/
def rowProgramLanes : RowProgramLanes (Fin 21) where
  parameters := ⟨rowProgramParameterIndex, by
    intro a b h
    cases a <;> cases b <;> simp_all [rowProgramParameterIndex]⟩
  rows := ⟨rowProgramRowIndex, by
    intro a b h
    cases a <;> cases b <;> (try cases ‹ExactlyOneLane›) <;>
      (try cases ‹ExactlyOneLane›) <;> simp_all [rowProgramRowIndex]⟩
  width := rfl
  stride := rfl
  fresh := by
    intro lane hWidth hStride p
    cases lane <;> (try cases ‹ExactlyOneLane›) <;> cases p <;>
      first | contradiction | decide

/-- The complete row section has an explicit polynomial-time Cook-tape implementation. -/
theorem binaryTableauRows_polynomialTimeMap (k d states symbols : Nat) :
    PolynomialTimeMap (binaryTableauRows k d states symbols) :=
  binaryTableauRows_polynomialTimeMap_of_layout rowProgramLanes k d states symbols

end PvsNP.CookLevin
