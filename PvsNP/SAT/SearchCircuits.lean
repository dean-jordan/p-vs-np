module

public import PvsNP.Circuits.PrefixQueryWiring
public import PvsNP.Complexity.CircuitLowerBound
public import PvsNP.SAT.OracleSearch

/-! # Boolean circuits for search from SAT decision circuits -/

public section

namespace PvsNP.SATSearch

open Circuits

private def nextBitCircuit (decision : (m : Nat) → BooleanCircuit m) (n k : Nat) :
    BooleanCircuit (n + k) :=
  ((prefixQueryFalseCircuit n k).thenBoolean (decision (prefixQueryLength n (k + 1)))).not

private def prefixCircuit (decision : (m : Nat) → BooleanCircuit m) (n : Nat) :
    (k : Nat) → MultiCircuit n (n + k)
  | 0 => ⟨n, .empty n, id⟩
  | k + 1 => (prefixCircuit decision n k).pushOutput (nextBitCircuit decision n k)

private theorem prefixCircuit_eval_input (decision : (m : Nat) → BooleanCircuit m)
    (n k : Nat) (x : Fin n → Bool) (i : Fin n) :
    (prefixCircuit decision n k).eval x (i.castAdd k) = x i := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change ((prefixCircuit decision n k).pushOutput (nextBitCircuit decision n k)).eval x
      (i.castAdd k).castSucc = x i
    rw [MultiCircuit.eval_pushOutput_castSucc, ih]

private def prefixCircuitWord (decision : (m : Nat) → BooleanCircuit m)
    (n k : Nat) (x : Fin n → Bool) : BinaryWord :=
  List.ofFn fun j : Fin k ↦ (prefixCircuit decision n k).eval x (Fin.natAdd n j)

private theorem length_prefixCircuitWord (decision : (m : Nat) → BooleanCircuit m)
    (n k : Nat) (x : Fin n → Bool) : (prefixCircuitWord decision n k x).length = k :=
  List.length_ofFn

private theorem prefixCircuitWord_succ (decision : (m : Nat) → BooleanCircuit m)
    (hDecision : ∀ m (bits : Fin m → Bool), (decision m).eval bits = true ↔
      List.ofFn bits ∈ CNFSAT)
    (answer : BinaryWord → Bool) (hAnswer : ∀ q, answer q = true ↔ q ∈ CNFSAT)
    (n k : Nat) (x : Fin n → Bool) (hk : k + 1 ≤ n) :
    prefixCircuitWord decision n (k + 1) x = prefixCircuitWord decision n k x ++
      [!(extensionOracle answer (List.ofFn x) (prefixCircuitWord decision n k x ++ [false]))] := by
  let before := prefixCircuit decision n k
  let pref := prefixCircuitWord decision n k x
  have hInput : (fun i : Fin n ↦ before.eval x (i.castAdd k)) = x :=
    funext (prefixCircuit_eval_input decision n k x)
  have hQuery : List.ofFn ((prefixQueryFalseCircuit n k).eval (before.eval x)) =
      prefixQuery (List.ofFn x) (pref ++ [false]) := by
    change _ = prefixQuery (List.ofFn x)
      ((List.ofFn fun j : Fin k ↦ before.eval x (Fin.natAdd n j)) ++ [false])
    rw [eval_prefixQueryFalseCircuit, hInput]
  have hGuard : (pref ++ [false]).length ≤ (List.ofFn x).length := by
    simpa only [List.length_append, List.length_singleton, List.length_ofFn,
      pref, length_prefixCircuitWord] using hk
  have hAnswerEq : (decision (prefixQueryLength n (k + 1))).eval
      ((prefixQueryFalseCircuit n k).eval (before.eval x)) =
      extensionOracle answer (List.ofFn x) (pref ++ [false]) := by
    apply Bool.eq_iff_iff.mpr
    rw [hDecision, hQuery, extensionOracle, ite_eq_left hGuard, hAnswer]
  have hLast : (prefixCircuit decision n (k + 1)).eval x (Fin.natAdd n (Fin.last k)) =
      !(extensionOracle answer (List.ofFn x) (pref ++ [false])) := by
    change (before.pushOutput (nextBitCircuit decision n k)).eval x (Fin.last (n + k)) = _
    rw [MultiCircuit.eval_pushOutput_last]
    simp only [nextBitCircuit, BooleanCircuit.eval_not, MultiCircuit.eval_thenBoolean, hAnswerEq]
  have hPrevious :
      (fun j : Fin k ↦ (prefixCircuit decision n (k + 1)).eval x (Fin.natAdd n j.castSucc)) =
        fun j : Fin k ↦ before.eval x (Fin.natAdd n j) := by
    funext j
    change (before.pushOutput (nextBitCircuit decision n k)).eval x
      (Fin.natAdd n j).castSucc = _
    rw [MultiCircuit.eval_pushOutput_castSucc]
  simp only [prefixCircuitWord, List.ofFn_succ_last, hPrevious, hLast]
  rfl

private theorem prefixCircuit_size_le (decision : (m : Nat) → BooleanCircuit m)
    (n k K : Nat) (hDecision : ∀ j < k, (decision (prefixQueryLength n (j + 1))).size ≤ K) :
    (prefixCircuit decision n k).size ≤ k * (K + 3) := by
  induction k with
  | zero => simp [prefixCircuit, MultiCircuit.size, Network.size]
  | succ k ih =>
    have hPrevious := ih (fun j hj ↦ hDecision j (hj.trans (Nat.lt_succ_self k)))
    have hNew := hDecision k (Nat.lt_succ_self k)
    simp only [prefixCircuit, MultiCircuit.size_pushOutput, nextBitCircuit,
      BooleanCircuit.size_not, MultiCircuit.size_thenBoolean, size_prefixQueryFalseCircuit,
      Nat.succ_mul]
    omega

/-- Use the first `n` output wires for the assignment and the last for
the SAT decision. The assignment is relevant when the last bit is true. -/
def witnessCircuit (decision : (m : Nat) → BooleanCircuit m) (n : Nat) : MultiCircuit n (n + 1) :=
  let prefixWithInput := prefixCircuit decision n n
  let result := prefixWithInput.pushOutput ((decision n).mapInputs (Fin.castAdd n))
  ⟨result.wires, result.network, fun i ↦ result.output (Fin.natAdd n i)⟩

theorem witnessCircuit_eval_success (decision : (m : Nat) → BooleanCircuit m)
    (n : Nat) (x : Fin n → Bool) :
    (witnessCircuit decision n).eval x (Fin.last n) = (decision n).eval x := by
  change ((prefixCircuit decision n n).pushOutput ((decision n).mapInputs (Fin.castAdd n))).eval
    x (Fin.last (n + n)) = _
  rw [MultiCircuit.eval_pushOutput_last, BooleanCircuit.eval_mapInputs]
  congr 1
  exact funext (prefixCircuit_eval_input decision n n x)

private theorem witnessCircuit_eval_assignment (decision : (m : Nat) → BooleanCircuit m)
    (n : Nat) (x : Fin n → Bool) :
    List.ofFn (fun i : Fin n ↦ (witnessCircuit decision n).eval x i.castSucc) =
      prefixCircuitWord decision n n x := by
  unfold prefixCircuitWord
  congr 1
  funext i
  change ((prefixCircuit decision n n).pushOutput ((decision n).mapInputs (Fin.castAdd n))).eval
    x (Fin.natAdd n i).castSucc = _
  rw [MultiCircuit.eval_pushOutput_castSucc]

theorem witnessCircuit_size_le (decision : (m : Nat) → BooleanCircuit m) (n K : Nat)
    (hDecision : ∀ m ≤ n + n * (n + 5), (decision m).size ≤ K) :
    (witnessCircuit decision n).size ≤ n * (K + 3) + K := by
  have hPrefix := prefixCircuit_size_le decision n n K
    (fun j hj ↦ hDecision _ (prefixQueryLength_le n (j + 1) (Nat.succ_le_of_lt hj)))
  have hFinal := hDecision n (Nat.le_add_right ..)
  change ((prefixCircuit decision n n).pushOutput ((decision n).mapInputs (Fin.castAdd n))).size
    ≤ _
  rw [MultiCircuit.size_pushOutput, BooleanCircuit.size_mapInputs]
  exact Nat.add_le_add hPrefix hFinal

/-- On satisfiable inputs, the assignment output satisfies the original word. -/
theorem witnessCircuit_eval_checkWord (decision : (m : Nat) → BooleanCircuit m)
    (hDecision : ∀ m (bits : Fin m → Bool), (decision m).eval bits = true ↔
      List.ofFn bits ∈ CNFSAT)
    (n : Nat) (x : Fin n → Bool) (hSat : List.ofFn x ∈ CNFSAT) :
    SATAssignment.checkWord (List.ofFn x)
      (List.ofFn fun i : Fin n ↦ (witnessCircuit decision n).eval x i.castSucc) = true := by
  classical
  let answer (q : BinaryWord) := decide (q ∈ CNFSAT)
  have hAnswer (q : BinaryWord) : answer q = true ↔ q ∈ CNFSAT := Iff.of_eq decide_eq_true_eq
  let oracle := extensionOracle answer (List.ofFn x)
  have hSpec := extensionOracle_eq_true_iff answer hAnswer (List.ofFn x)
  have hFeasible (k : Nat) (hk : k ≤ n) :
      oracle (prefixCircuitWord decision n k x) = true := by
    induction k with
    | zero =>
      change extensionOracle answer (List.ofFn x) [] = true
      simpa only [extensionOracle, List.length_nil, Nat.zero_le, ite_true, prefixQuery_nil, hAnswer]
        using hSat
    | succ k ih =>
      rw [prefixCircuitWord_succ decision hDecision answer hAnswer n k x hk]
      exact prefixOracle_append_feasible hSpec
        (by simpa only [List.length_ofFn, length_prefixCircuitWord] using Nat.lt_of_succ_le hk)
        (ih (Nat.le_of_succ_le hk))
  obtain ⟨assignment, hLength, hPrefix, hCheck⟩ :=
    (hSpec (prefixCircuitWord decision n n x)).mp (hFeasible n (Nat.le_refl _))
  have hEqual : prefixCircuitWord decision n n x = assignment :=
    hPrefix.eq_of_length (by rw [length_prefixCircuitWord, hLength, List.length_ofFn])
  rwa [witnessCircuit_eval_assignment, hEqual]

/-- Polynomial-size SAT decision circuits are equivalent to polynomial-size
circuits that output a decision bit and a satisfying assignment on success. -/
theorem CNFSAT_mem_PPoly_iff_exists_witnessCircuits :
    CNFSAT ∈ PPoly ↔
      ∃ family : (n : Nat) → MultiCircuit n (n + 1),
        PolynomiallyBounded (fun n ↦ (family n).size) ∧
        ∀ n (x : Fin n → Bool),
          ((family n).eval x (Fin.last n) = true ↔ List.ofFn x ∈ CNFSAT) ∧
          ((family n).eval x (Fin.last n) = true →
            SATAssignment.checkWord (List.ofFn x)
              (List.ofFn fun i : Fin n ↦ (family n).eval x i.castSucc) = true) := by
  constructor
  · rintro ⟨decision, ⟨C, d, hSize⟩, hDecision⟩
    let cap (n : Nat) := n + n * (n + 5)
    let K (n : Nat) := C * (cap n + 1) ^ d
    let c := PolynomiallyBounded.const
    let idBound := PolynomiallyBounded.id
    have hCap : PolynomiallyBounded cap := idBound.add (idBound.mul (idBound.add (c 5)))
    have hK : PolynomiallyBounded K := (c C).mul ((hCap.add (c 1)).pow d)
    refine ⟨witnessCircuit decision, ((idBound.mul (hK.add (c 3))).add hK).mono ?_, ?_⟩
    · intro n
      apply witnessCircuit_size_le
      intro m hm
      exact (hSize m).trans (Nat.mul_le_mul_left C
        (Nat.pow_le_pow_left (Nat.add_le_add_right hm 1) d))
    · intro n x
      rw [witnessCircuit_eval_success]
      exact ⟨hDecision n x, fun h ↦ witnessCircuit_eval_checkWord decision hDecision n x
        ((hDecision n x).mp h)⟩
  · rintro ⟨family, hSize, hCorrect⟩
    let decision (n : Nat) : BooleanCircuit n :=
      ⟨(family n).wires, (family n).network, (family n).output (Fin.last n)⟩
    exact ⟨decision, hSize, fun n x ↦ (hCorrect n x).1⟩

end PvsNP.SATSearch
