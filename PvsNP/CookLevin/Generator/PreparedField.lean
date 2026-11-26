module

public import PvsNP.CookLevin.Generator.ExactlyOne
public import PvsNP.TuringMachine.Registers.Clear

/-! # Preparing and emitting one exactly-one field -/

@[expose] public section

namespace PvsNP.RegisterMachine.Fragment

variable {R : Type}

/-- Clear a register with a single decrement-loop label. -/
abbrev clear (lane : R) : Fragment R where
  Label := Unit
  entry := some ()
  code _ := .dec lane none (some ())

/-- Clear one register in its value plus one instruction, preserving the output. -/
theorem runsValues_clear [DecidableEq R] (lane : R) (x : BinaryWord) (values : R → Nat) :
    (clear lane).RunsValues x (values lane + 1) values (setValue lane 0 values) := by
  intro suffix
  let cfg : Config R Unit := ⟨none, values, none, suffix⟩
  exact RegisterMachine.run_clear x (program := (clear lane).close) (entry := some ())
    (next := none) (cfg := (clear lane).enter cfg) rfl rfl

end PvsNP.RegisterMachine.Fragment

namespace PvsNP.CookLevin

open RegisterMachine RegisterMachine.Fragment

variable {R : Type} (lanes : ExactlyOneLane ↪ R)

local notation "B" => lanes ExactlyOneLane.base
local notation "N" => lanes ExactlyOneLane.count
local notation "I" => lanes ExactlyOneLane.left
local notation "J" => lanes ExactlyOneLane.right

/-- Load the field parameters, emit its clauses, and clear the parameter lanes. -/
abbrev preparedField (prepare : Fragment R) : Fragment R :=
  (prepare.seq (exactlyOneField lanes)).seq ((clear B).seq (clear N))

/-- The cost of preparing, emitting, and clearing one field. -/
def preparedFieldTimeBound (prepCost base count : Nat) : Nat :=
  prepCost + exactlyOneFieldTimeBound base count + base + count + 2

theorem preparedFieldTimeBound_polynomiallyBounded {prepCost base count : Nat → Nat}
    (hPrep : PolynomiallyBounded prepCost) (hBase : PolynomiallyBounded base)
    (hCount : PolynomiallyBounded count) :
    PolynomiallyBounded (fun n ↦ preparedFieldTimeBound (prepCost n) (base n) (count n)) :=
  (((hPrep.add (exactlyOneFieldTimeBound_polynomiallyBounded hBase hCount)).add hBase).add
    hCount).add (PolynomiallyBounded.const 2)

/-- With zeroed field lanes, a prepared block prepends its field and restores the valuation. -/
theorem run_preparedField [DecidableEq R] (prepare : Fragment R) (x suffix : BinaryWord)
    (before : R → Nat) (prepCost base count : Nat)
    (hPrepare : prepare.RunsValues x prepCost before (setValue N count (setValue B base before)))
    (hBaseZero : before B = 0) (hCountZero : before N = 0)
    (hLeftZero : before I = 0) (hRightZero : before J = 0)
    (hScratch : ExactlyOneScratchZero lanes before) :
    ∃ cost ≤ preparedFieldTimeBound prepCost base count,
      (preparedField lanes prepare).RunsOutput x cost before before suffix
        (exactlyOneFieldOutput base count suffix) := by
  let loaded := setValue N count (setValue B base before)
  have hBase : loaded B = base := by simp [loaded, setValue]
  have hCount : loaded N = count := setValue_same ..
  have hLeft : loaded I = 0 := by simpa [loaded, setValue] using hLeftZero
  have hRight : loaded J = 0 := by simpa [loaded, setValue] using hRightZero
  have hWork : ExactlyOneScratchZero lanes loaded := by
    simpa [ExactlyOneScratchZero, loaded, setValue] using hScratch
  obtain ⟨fieldCost, hFieldCost, hField⟩ :=
    run_exactlyOneField lanes x suffix loaded hWork hLeft hRight
  rw [hBase, hCount] at hFieldCost hField
  let clearedBase := setValue B 0 loaded
  have hLeftover : clearedBase N = count := by simp [clearedBase, loaded, setValue]
  have hRestore : setValue N 0 clearedBase = before := by
    funext r
    by_cases hb : r = B
    · subst r
      simp [clearedBase, setValue, hBaseZero]
    by_cases hn : r = N
    · subst r
      simp [hCountZero]
    simp [clearedBase, loaded, setValue, hb, hn]
  have hClearBase := runsValues_clear B x loaded
  have hClearCount := runsValues_clear N x clearedBase
  rw [hBase] at hClearBase
  rw [hLeftover, hRestore] at hClearCount
  refine ⟨prepCost + fieldCost + ((base + 1) + (count + 1)), ?_, ?_⟩
  · unfold preparedFieldTimeBound
    omega
  · let output := exactlyOneFieldOutput base count suffix
    exact ((hPrepare.withOutput suffix).seq hField).seq
      ((hClearBase.withOutput output).seq (hClearCount.withOutput output))

end PvsNP.CookLevin
