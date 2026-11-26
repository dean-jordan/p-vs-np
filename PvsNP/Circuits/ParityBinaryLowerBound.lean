module

public import PvsNP.Circuits.PairRestriction
public import PvsNP.Circuits.ParitySupport

/-! # Binary gate counts from two-input parity restrictions -/

public section

namespace PvsNP.Circuits

variable {n m : Nat}

namespace Network

/-- A backward support and wires with pairwise parity restrictions are
charged together. A shared source can account for one lost designated wire.
Two exclusive designated sources cannot disappear into a binary gate. -/
theorem inputSupport_card_add_parity_le (network : Network n m) (output : Fin m)
    (marked : Finset (Fin n))
    (hMarked : marked ⊆ network.inputSupport {output})
    (hParity : ∀ i ∈ marked, ∀ j ∈ marked, i ≠ j →
      ParityRestriction (fun x ↦ network.eval x output) i j) :
    (network.inputSupport {output}).card + marked.card ≤ network.binarySize + 2 := by
  induction network with
  | empty n =>
    have hCount := Finset.card_le_card hMarked
    simp only [inputSupport, Finset.card_singleton] at hCount ⊢
    simpa only [binarySize, Nat.zero_add] using Nat.add_le_add_left hCount 1
  | @cons n m gate rest ih =>
    let needed := rest.inputSupport {output}
    let g (x : Fin (n + 1) → Bool) := rest.eval x output
    have hAgree (x y : Fin (n + 1) → Bool) (h : ∀ i ∈ needed, x i = y i) : g x = g y :=
      rest.eval_eq_of_agree_inputSupport {output} x y h output (Finset.mem_singleton_self _)
    change marked ⊆ previousSupport gate needed at hMarked
    change (previousSupport gate needed).card + marked.card ≤
      (gate.arity - 1) + rest.binarySize + 2
    obtain ⟨next, hNext, hNextParity, hStep⟩ := exists_next_pair_support gate needed marked
      (ParityRestriction (fun x ↦ g (gate.extend x))) (ParityRestriction g)
      hMarked hParity (fun h ↦ h.swap)
      (not_parityRestriction_of_exclusive_sources gate needed g hAgree)
      (parityRestriction_of_old gate needed g hAgree)
      (parityRestriction_promote gate needed g hAgree)
    have hRest := ih output next hNext hNextParity
    change needed.card + next.card ≤ rest.binarySize + 2 at hRest
    omega

end Network

namespace BooleanCircuit

/-- A circuit with all inputs relevant pays an additional binary-gate
budget for a set with a parity restriction on every pair. -/
theorem card_le_binarySize_add_two_of_parity {k : Nat} (c : BooleanCircuit n)
    (coords : Fin k ↪ Fin n)
    (hSensitive : ∀ i : Fin n, ∃ x y : Fin n → Bool,
      c.eval x ≠ c.eval y ∧ ∀ j, j ≠ i → x j = y j)
    (hParity : ∀ i j, i ≠ j → ParityRestriction c.eval (coords i) (coords j)) :
    n + k ≤ c.binarySize + 2 := by
  let support := c.network.inputSupport {c.output}
  have hAll (i : Fin n) : i ∈ support := by
    by_contra hMiss
    obtain ⟨x, y, hDiff, hSame⟩ := hSensitive i
    have hAgree (j : Fin n) (hj : j ∈ support) : x j = y j :=
      hSame j (fun he ↦ hMiss (he ▸ hj))
    exact hDiff (c.network.eval_eq_of_agree_inputSupport {c.output} x y hAgree c.output
      (Finset.mem_singleton_self _))
  let marked := (Finset.univ : Finset (Fin k)).map coords
  have hMarked : marked ⊆ support := fun i _ ↦ hAll i
  have hPairs : ∀ i ∈ marked, ∀ j ∈ marked, i ≠ j → ParityRestriction c.eval i j := by
    intro i hi j hj hNe
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hi
    obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp hj
    exact hParity a b (fun he ↦ hNe (congrArg coords he))
  have hSupport : support = Finset.univ := Finset.eq_univ_of_forall hAll
  have hCount := c.network.inputSupport_card_add_parity_le c.output marked hMarked hPairs
  change support.card + marked.card ≤ c.binarySize + 2 at hCount
  simpa only [hSupport, marked, Finset.card_map, Finset.card_univ, Fintype.card_fin] using hCount

end BooleanCircuit

end PvsNP.Circuits
