module

public import PvsNP.Circuits.BinaryBasisPair

/-! # Pair restrictions force sharing in arbitrary binary circuits -/

public section

namespace PvsNP.Circuits

variable {n m : Nat}

namespace Network

/-- Count needed wires and marked wires together for arbitrary binary gates.
The same topology supports both operations and their pair restrictions. -/
theorem inputSupport_card_add_basisPair_le (network : Network n m)
    (ops : network.BinaryFunctions) (output : Fin m) (marked : Finset (Fin n))
    (hMarked : marked ⊆ network.inputSupport {output})
    (hPairs : ∀ i ∈ marked, ∀ j ∈ marked, i ≠ j →
      BasisPair (fun x ↦ network.evalWith ops x output) i j) :
    (network.inputSupport {output}).card + marked.card ≤ network.binarySize + 2 := by
  induction network with
  | empty n =>
    have hCount := Finset.card_le_card hMarked
    simp only [inputSupport, Finset.card_singleton] at hCount ⊢
    simpa only [binarySize, Nat.zero_add] using Nat.add_le_add_left hCount 1
  | @cons n m gate rest ih =>
    let needed := rest.inputSupport {output}
    let g (x : Fin (n + 1) → Bool) := rest.evalWith ops.2 x output
    have hAgree (x y : Fin (n + 1) → Bool) (h : ∀ i ∈ needed, x i = y i) : g x = g y :=
      rest.evalWith_eq_of_agree_inputSupport ops.2 {output} x y h output
        (Finset.mem_singleton_self _)
    change marked ⊆ previousSupport gate needed at hMarked
    change (previousSupport gate needed).card + marked.card ≤
      (gate.arity - 1) + rest.binarySize + 2
    obtain ⟨next, hNext, hNextPairs, hStep⟩ := exists_next_pair_support gate needed marked
      (BasisPair (fun x ↦ g (gate.extendWith ops.1 x))) (BasisPair g)
      hMarked hPairs (fun h ↦ h.swap)
      (not_basisPair_of_exclusive_sources gate ops.1 needed g hAgree)
      (basisPair_of_old gate ops.1 needed g hAgree)
      (basisPair_promote gate ops.1 needed g hAgree)
    have hRest := ih ops.2 output next hNext hNextPairs
    change needed.card + next.card ≤ rest.binarySize + 2 at hRest
    omega

end Network

namespace BinaryBasisCircuit

/-- A circuit with `n` relevant inputs and `k` pair witnesses requires
at least `n + k - 2` binary gates. -/
theorem card_le_binarySize_add_two_of_basisPair {k : Nat} (c : BinaryBasisCircuit n)
    (coords : Fin k ↪ Fin n)
    (hSensitive : ∀ i : Fin n, ∃ x y : Fin n → Bool,
      c.eval x ≠ c.eval y ∧ ∀ j, j ≠ i → x j = y j)
    (hPairs : ∀ i j, i ≠ j → BasisPair c.eval (coords i) (coords j)) :
    n + k ≤ c.binarySize + 2 := by
  let net := c.topology.network
  let output := c.topology.output
  let support := net.inputSupport {output}
  have hAll (i : Fin n) : i ∈ support := by
    by_contra hMiss
    obtain ⟨x, y, hDiff, hSame⟩ := hSensitive i
    have hAgree (j : Fin n) (hj : j ∈ support) : x j = y j :=
      hSame j (fun he ↦ hMiss (he ▸ hj))
    exact hDiff (net.evalWith_eq_of_agree_inputSupport c.operations {output} x y hAgree output
      (Finset.mem_singleton_self _))
  let marked := (Finset.univ : Finset (Fin k)).map coords
  have hMarked : marked ⊆ support := fun i _ ↦ hAll i
  have hMarkedPairs : ∀ i ∈ marked, ∀ j ∈ marked, i ≠ j → BasisPair c.eval i j := by
    intro i hi j hj hNe
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hi
    obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp hj
    exact hPairs a b (fun he ↦ hNe (congrArg coords he))
  have hSupport : support = Finset.univ := Finset.eq_univ_of_forall hAll
  have hCount := net.inputSupport_card_add_basisPair_le c.operations output marked
    hMarked hMarkedPairs
  change support.card + marked.card ≤ c.binarySize + 2 at hCount
  simpa only [hSupport, marked, Finset.card_map, Finset.card_univ, Fintype.card_fin] using hCount

end BinaryBasisCircuit

end PvsNP.Circuits
