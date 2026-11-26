module

public import PvsNP.CookLevin.Generator.AcceptingBlock
public import PvsNP.CookLevin.Generator.FiniteTable
public import PvsNP.CookLevin.Generator.Parameters
public import PvsNP.TuringMachine.Registers.SimulationBound

/-! # The accepting assertion in the indexed verifier code -/

@[expose] public section

namespace PvsNP.CookLevin

open RegisterMachine

variable {states symbols certificates : Nat}

/-- Name of the accepting-state atom at the last tick. -/
def FiniteTable.acceptanceName (table : FiniteTable states symbols certificates)
    (n k d : Nat) : Nat :=
  let t := horizon n k d
  t * Tableau.atomStride states (2 * t + 1) symbols + table.accept.val

/-- The last clause and the formula terminator in the forward binary word. -/
def FiniteTable.acceptanceCode (table : FiniteTable states symbols certificates)
    (n k d : Nat) : BinaryWord :=
  CNFCode.encode [[.pos (table.acceptanceName n k d)]]

private theorem code_append_has_suffix (initial last : CNF.Formula Nat) :
    ∃ front, CNFCode.encode (initial ++ last) = front ++ CNFCode.encode last := by
  induction initial with
  | nil => exact ⟨[], rfl⟩
  | cons clause initial ih =>
    obtain ⟨front, h⟩ := ih
    refine ⟨true :: (CNFCode.encodeClause clause ++ front), ?_⟩
    rw [List.cons_append, CNFCode.encode_cons, h, List.cons_append, List.append_assoc]

/-- The accepting assertion is emitted first by the right-to-left generator. -/
theorem FiniteTable.binaryVerifierMap_acceptance_suffix
    (table : FiniteTable states symbols certificates) (x : BinaryWord) (k d : Nat) :
    ∃ front, table.binaryVerifierMap x k d = front ++ table.acceptanceCode x.length k d := by
  simp only [FiniteTable.binaryVerifierMap, FiniteTable.verifierFormula, Tableau.acceptingClauses,
    CNF.mapAtoms, List.map_append, List.map_cons, List.map_nil, CNF.Literal.map]
  exact code_append_has_suffix _ [[.pos (table.acceptanceName x.length k d)]]

variable {R : Type}

/-- Initialize the generator and emit its first block, the last clause of the forward word. -/
def FiniteTable.generatorPrefix (table : FiniteTable states symbols certificates)
    (lanes : ParameterLane ↪ R) (index : R) (k d : Nat) : Fragment R :=
  (parameterPrelude lanes k d states symbols).seq
    (Fragment.acceptingBlock (lanes .horizon) (lanes .stride) index (lanes .work)
      (lanes .scratch) table.accept.val)

/-- Count initialization and emission of the accepting assertion. -/
def FiniteTable.generatorPrefixTime (table : FiniteTable states symbols certificates)
    (n k d : Nat) : Nat :=
  let t := horizon n k d
  parameterTime n k d states symbols +
    Fragment.acceptingBlockTime table.accept.val t (Tableau.atomStride states (2 * t + 1) symbols)

theorem FiniteTable.generatorPrefixTime_polynomiallyBounded
    (table : FiniteTable states symbols certificates) (k d : Nat) :
    PolynomiallyBounded (fun n ↦ table.generatorPrefixTime n k d) := by
  let constant := PolynomiallyBounded.const
  have t := horizon_polynomiallyBounded k d
  have w := ((constant 2).mul t).add (constant 1)
  have stride := ((constant states).add w).add (w.mul (constant symbols))
  exact (parameterTime_polynomiallyBounded k d states symbols).add
    (Fragment.acceptingBlockTime_polynomiallyBounded table.accept.val t stride)

variable [DecidableEq R]

/-- The linked prefix preserves the size parameters and emits the exact accepting suffix. -/
theorem FiniteTable.run_generatorPrefix (table : FiniteTable states symbols certificates)
    (lanes : ParameterLane ↪ R) (index : R) (hIndex : ∀ lane, index ≠ lanes lane)
    (x : BinaryWord) (k d : Nat) (suffix : BinaryWord) :
    let f := table.generatorPrefix lanes index k d
    f.run x (table.generatorPrefixTime x.length k d)
        (f.enter (⟨none, fun _ ↦ 0, none, suffix⟩ : Config R Unit)) =
      some ⟨some none, parameterValues lanes x.length k d states symbols, none,
        table.acceptanceCode x.length k d ++ suffix⟩ := by
  let first := parameterPrelude lanes k d states symbols
  let mid : first.Cfg :=
    ⟨some none, parameterValues lanes x.length k d states symbols, none, suffix⟩
  have hFirst : first.run x (parameterTime x.length k d states symbols)
      (first.enter (⟨none, fun _ ↦ 0, none, suffix⟩ : Config R Unit)) = some mid :=
    run_parameterPrelude lanes k d states symbols x suffix
  have hIndex' (lane : ParameterLane) : lanes lane ≠ index := (hIndex lane).symm
  have hDistinct : [lanes .horizon, lanes .stride, index, lanes .work, lanes .scratch].Nodup := by
    simp [hIndex, hIndex']
  have hV := parameterValues_at lanes x.length k d states symbols
  have hSecond := Fragment.run_acceptingBlock x (lanes .horizon) (lanes .stride)
    index (lanes .work) (lanes .scratch) table.accept.val mid hDistinct
    (parameterValues_outside lanes x.length k d states symbols index hIndex) (hV .work)
    (hV .scratch) rfl
  have hTime : mid.values (lanes .horizon) = horizon x.length k d := hV .horizon
  have hStride : mid.values (lanes .stride) =
      Tableau.atomStride states (2 * horizon x.length k d + 1) symbols := hV .stride
  dsimp only at hSecond
  rw [hTime, hStride] at hSecond
  simpa only [FiniteTable.generatorPrefix, FiniteTable.generatorPrefixTime, first, mid,
    FiniteTable.acceptanceCode, FiniteTable.acceptanceName, CNFCode.encode_cons, CNFCode.encode_nil,
    Config.map, Option.map_some, Option.map_none, List.cons_append, List.append_assoc,
    List.singleton_append, List.nil_append] using
      Fragment.run_seq hFirst rfl hSecond rfl

private def prefixRegisterCode : ParameterLane → Fin 9
  | .length => 0
  | .capacity => 1
  | .pairBound => 2
  | .horizon => 3
  | .width => 4
  | .stride => 5
  | .work => 6
  | .scratch => 7

private def prefixLanes : ParameterLane ↪ Fin 9 :=
  ⟨prefixRegisterCode, by
    intro a b h
    cases a <;> cases b <;> simp_all [prefixRegisterCode]⟩

/-- The prefix alone can be closed as a Cook transducer for the accepting suffix. -/
theorem FiniteTable.acceptanceCode_polynomialTime
    (table : FiniteTable states symbols certificates) (k d : Nat) :
    PolynomialTimeMap (fun x ↦ table.acceptanceCode x.length k d) := by
  let f := table.generatorPrefix prefixLanes 8 k d
  have distinct (lane : ParameterLane) : (8 : Fin 9) ≠ prefixLanes lane := by
    cases lane <;> decide
  refine polynomialTimeMap_of_run f.entry f.close
    ((table.generatorPrefixTime_polynomiallyBounded k d).add (PolynomiallyBounded.const 1)) ?_
  intro x
  let done : f.Cfg :=
    ⟨some none, parameterValues prefixLanes x.length k d states symbols, none,
      table.acceptanceCode x.length k d⟩
  have hRun : f.run x (table.generatorPrefixTime x.length k d) (Config.initial f.entry) =
      some done := by
    simpa only [f, done, Fragment.enter, Config.initial, List.append_nil] using
      table.run_generatorPrefix prefixLanes 8 distinct x k d []
  exact ⟨_, Nat.le_refl _, { done with pc := none }, Fragment.run_close hRun rfl rfl, rfl, rfl⟩

end PvsNP.CookLevin
