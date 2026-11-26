module

public import PvsNP.Circuits.BooleanCircuit
public import PvsNP.SAT.SearchOracleQuery

/-! # Circuit wiring for a CNF-SAT prefix query -/

public section

namespace PvsNP.SATSearch

open Circuits

/-- The query template contains input wire names and two names for constant bits. -/
private def queryLayout {α : Type} (literal : Bool → α) : Nat → List α → List α → List α
  | _, word, [] => word
  | i, word, bit :: rest =>
    [literal true, literal true, bit] ++ (CNFCode.encodeIndex i).map literal ++
      [literal false] ++ queryLayout literal (i + 1) word rest

private def constantsNetwork (N : Nat) : Network N (N + 2) :=
  .cons (.const true) (.cons (.const false) (.empty (N + 2)))

private def constantWire (N : Nat) : Bool → Fin (N + 2)
  | true => (Fin.last N).castSucc
  | false => Fin.last (N + 1)

private def liftedWire {N : Nat} (i : Fin N) : Fin (N + 2) :=
  i.castLE (Nat.le_add_right N 2)

private theorem eval_constantWire (N : Nat) (x : Fin N → Bool) (b : Bool) :
    (constantsNetwork N).eval x (constantWire N b) = b := by
  cases b <;> simp only [constantsNetwork, Network.eval, constantWire,
    Gate.extend_castSucc, Gate.extend_last, Gate.eval]

private theorem eval_liftedWire {N : Nat} (x : Fin N → Bool) (i : Fin N) :
    (constantsNetwork N).eval x (liftedWire i) = x i :=
  (constantsNetwork N).eval_castLE x i

private theorem eval_queryLayout {α : Type} (literal : Bool → α) (read : α → Bool)
    (hLiteral : ∀ b, read (literal b) = b) (i : Nat) (word pref : List α) :
    (queryLayout literal i word pref).map read =
      prefixQueryFrom i (word.map read) (pref.map read) := by
  induction pref generalizing i with
  | nil => simp only [queryLayout, List.map_nil, prefixQueryFrom_nil]
  | cons b rest ih =>
    simp only [queryLayout, List.map_append, List.map_cons, List.map_nil, hLiteral, List.map_map,
      Function.comp_def, ih, prefixQueryFrom_cons]
    rw [show (CNFCode.encodeIndex i).map (fun b ↦ b) = _ from List.map_id _]

private def queryTemplate {N n k : Nat} (word : Fin n → Fin (N + 2))
    (pref : Fin k → Fin (N + 2)) : List (Fin (N + 2)) :=
  queryLayout (constantWire N) 0 (List.ofFn word) (List.ofFn pref)

private theorem eval_queryTemplate {N n k : Nat} (word : Fin n → Fin (N + 2))
    (pref : Fin k → Fin (N + 2)) (x : Fin N → Bool) :
    (queryTemplate word pref).map ((constantsNetwork N).eval x) =
      prefixQuery (List.ofFn ((constantsNetwork N).eval x ∘ word))
        (List.ofFn ((constantsNetwork N).eval x ∘ pref)) := by
  simpa only [queryTemplate, prefixQuery, List.map_ofFn] using
    eval_queryLayout (constantWire N) ((constantsNetwork N).eval x) (eval_constantWire N x)
      0 (List.ofFn word) (List.ofFn pref)

private theorem length_queryTemplate {N n k : Nat} (word : Fin n → Fin (N + 2))
    (pref : Fin k → Fin (N + 2)) : (queryTemplate word pref).length = prefixQueryLength n k := by
  simpa only [List.length_map, length_prefixQuery, List.length_ofFn] using
    congrArg List.length (eval_queryTemplate word pref (fun _ ↦ false))

private def queryCircuitOf {N n k : Nat} (word : Fin n → Fin (N + 2))
    (pref : Fin k → Fin (N + 2)) : MultiCircuit N (prefixQueryLength n k) where
  wires := N + 2
  network := constantsNetwork N
  output i := (queryTemplate word pref)[i.val]'(by
    rw [length_queryTemplate]
    exact i.isLt)

private theorem eval_queryCircuitOf {N n k : Nat} (word : Fin n → Fin (N + 2))
    (pref : Fin k → Fin (N + 2)) (x : Fin N → Bool) :
    List.ofFn ((queryCircuitOf word pref).eval x) =
      prefixQuery (List.ofFn ((constantsNetwork N).eval x ∘ word))
        (List.ofFn ((constantsNetwork N).eval x ∘ pref)) := by
  rw [← eval_queryTemplate word pref x]
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_map, length_queryTemplate]
  · intro i _ _
    rw [List.getElem_ofFn, List.getElem_map]
    rfl

private theorem size_queryCircuitOf {N n k : Nat} (word : Fin n → Fin (N + 2))
    (pref : Fin k → Fin (N + 2)) : (queryCircuitOf word pref).size = 2 := rfl

/-- Form the query word from the original word and prefix stored in adjacent input wires. -/
def prefixQueryCircuit (n k : Nat) : MultiCircuit (n + k) (prefixQueryLength n k) :=
  queryCircuitOf (fun i ↦ liftedWire (i.castAdd k)) (fun j ↦ liftedWire (Fin.natAdd n j))

theorem eval_prefixQueryCircuit (n k : Nat) (x : Fin (n + k) → Bool) :
    List.ofFn ((prefixQueryCircuit n k).eval x) =
      prefixQuery (List.ofFn fun i : Fin n ↦ x (i.castAdd k))
        (List.ofFn fun j : Fin k ↦ x (Fin.natAdd n j)) := by
  rw [prefixQueryCircuit, eval_queryCircuitOf]
  simp only [Function.comp_def, eval_liftedWire]

theorem size_prefixQueryCircuit (n k : Nat) : (prefixQueryCircuit n k).size = 2 :=
  size_queryCircuitOf _ _

/-- Form the next prefix query with its last prefix bit wired to the shared false gate. -/
def prefixQueryFalseCircuit (n k : Nat) : MultiCircuit (n + k) (prefixQueryLength n (k + 1)) :=
  queryCircuitOf (fun i ↦ liftedWire (i.castAdd k))
    (Fin.lastCases (constantWire (n + k) false) (fun j ↦ liftedWire (Fin.natAdd n j)))

theorem eval_prefixQueryFalseCircuit (n k : Nat) (x : Fin (n + k) → Bool) :
    List.ofFn ((prefixQueryFalseCircuit n k).eval x) =
      prefixQuery (List.ofFn fun i : Fin n ↦ x (i.castAdd k))
        ((List.ofFn fun j : Fin k ↦ x (Fin.natAdd n j)) ++ [false]) := by
  rw [prefixQueryFalseCircuit, eval_queryCircuitOf]
  congr 1
  · simp only [Function.comp_def, eval_liftedWire]
  · rw [List.ofFn_succ_last]
    simp only [Function.comp_apply, Fin.lastCases_castSucc, Fin.lastCases_last, eval_liftedWire,
      eval_constantWire]

theorem size_prefixQueryFalseCircuit (n k : Nat) : (prefixQueryFalseCircuit n k).size = 2 :=
  size_queryCircuitOf _ _

end PvsNP.SATSearch
