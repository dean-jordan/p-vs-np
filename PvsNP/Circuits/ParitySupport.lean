module

public import PvsNP.Circuits.InputSupport

/-! # Live wires and shared inputs in gate elimination -/

public section

namespace PvsNP.Circuits

variable {n : Nat}

/-- Each already-needed operand is counted once when a needed gate is expanded. -/
theorem previousSupport_card_add_inter (gate : Gate n) (needed : Finset (Fin (n + 1)))
    (hLast : Fin.last n ∈ needed) :
    (previousSupport gate needed).card + (gateInputs gate ∩ oldWires needed).card + 1 =
      needed.card + (gateInputs gate).card := by
  rw [previousSupport, ite_eq_left hLast, Finset.inter_comm (gateInputs gate) (oldWires needed),
    Finset.card_union_add_card_inter, oldWires_card]
  have hErase := Finset.card_erase_add_one hLast
  omega

theorem previousSupport_card_add_inter_le (gate : Gate n) (needed : Finset (Fin (n + 1)))
    (hLast : Fin.last n ∈ needed) :
    (previousSupport gate needed).card + (gateInputs gate ∩ oldWires needed).card ≤
      needed.card + (gate.arity - 1) := by
  have hCount := previousSupport_card_add_inter gate needed hLast
  have hInputs := gateInputs_card_le gate
  omega

/-- Transport a pair property across one gate, charging any discarded
designations to already-needed operands. The semantic premises describe
which pairs survive or can be promoted to the new wire. -/
theorem exists_next_pair_support (gate : Gate n) (needed : Finset (Fin (n + 1)))
    (marked : Finset (Fin n)) (before : Fin n → Fin n → Prop)
    (after : Fin (n + 1) → Fin (n + 1) → Prop)
    (hMarked : marked ⊆ previousSupport gate needed)
    (hPairs : ∀ i ∈ marked, ∀ j ∈ marked, i ≠ j → before i j)
    (hSwap : ∀ {i j}, after i j → after j i)
    (hExclusive : ∀ {i j}, i ∉ oldWires needed → j ∉ oldWires needed → ¬ before i j)
    (hOld : ∀ {i j}, (Fin.last n ∉ needed ∨ (i ∉ gateInputs gate ∧ j ∉ gateInputs gate)) →
      before i j → after i.castSucc j.castSucc)
    (hPromote : ∀ {i j}, i ∉ oldWires needed → j ∉ gateInputs gate →
      before i j → after (Fin.last n) j.castSucc) :
    ∃ next, next ⊆ needed ∧ (∀ u ∈ next, ∀ v ∈ next, u ≠ v → after u v) ∧
      (previousSupport gate needed).card + marked.card ≤
        needed.card + next.card + (gate.arity - 1) := by
  by_cases hLast : Fin.last n ∈ needed
  · let shared := gateInputs gate ∩ oldWires needed
    let keep := marked \ shared
    let promote (i : Fin n) : Fin (n + 1) :=
      if i ∈ oldWires needed then i.castSucc else Fin.last n
    let next := keep.image promote
    have hOldNoSource {i : Fin n} (hi : i ∈ keep) (hOld : i ∈ oldWires needed) :
        i ∉ gateInputs gate := by
      intro hSource
      exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_inter.mpr ⟨hSource, hOld⟩)
    have hSingle {i j : Fin n} (hi : i ∈ keep) (hj : j ∈ keep)
        (hiOld : i ∉ oldWires needed) (hjOld : j ∉ oldWires needed) : i = j := by
      by_contra hNe
      exact hExclusive hiOld hjOld
        (hPairs i (Finset.mem_sdiff.mp hi).1 j (Finset.mem_sdiff.mp hj).1 hNe)
    have hInj : Set.InjOn promote (keep : Set (Fin n)) := by
      intro i hi j hj hEq
      by_cases hiOld : i ∈ oldWires needed <;> by_cases hjOld : j ∈ oldWires needed
      · simp only [promote, ite_eq_left hiOld, ite_eq_left hjOld, Fin.castSucc_inj] at hEq
        exact hEq
      · exact (Fin.castSucc_ne_last i (by
          simpa only [promote, ite_eq_left hiOld, ite_eq_right hjOld] using hEq)).elim
      · exact (Fin.castSucc_ne_last j (by
          simpa only [promote, ite_eq_right hiOld, ite_eq_left hjOld] using hEq.symm)).elim
      · exact hSingle hi hj hiOld hjOld
    have hNext : next ⊆ needed := by
      intro v hv
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
      by_cases hOld : i ∈ oldWires needed
      · simpa only [promote, ite_eq_left hOld] using (mem_oldWires_iff needed i).mp hOld
      · simpa only [promote, ite_eq_right hOld] using hLast
    have hNextPairs : ∀ u ∈ next, ∀ v ∈ next, u ≠ v → after u v := by
      intro u hu v hv hDiff
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
      have hNe : i ≠ j := fun h ↦ hDiff (congrArg promote h)
      have hPair := hPairs i (Finset.mem_sdiff.mp hi).1 j (Finset.mem_sdiff.mp hj).1 hNe
      by_cases hiOld : i ∈ oldWires needed <;> by_cases hjOld : j ∈ oldWires needed
      · simp only [promote, ite_eq_left hiOld, ite_eq_left hjOld]
        exact hOld
          (Or.inr ⟨hOldNoSource hi hiOld, hOldNoSource hj hjOld⟩) hPair
      · simp only [promote, ite_eq_left hiOld, ite_eq_right hjOld]
        exact hSwap (hPromote hjOld (hOldNoSource hi hiOld)
          (hPairs j (Finset.mem_sdiff.mp hj).1 i (Finset.mem_sdiff.mp hi).1 hNe.symm))
      · simp only [promote, ite_eq_right hiOld, ite_eq_left hjOld]
        exact hPromote hiOld
          (hOldNoSource hj hjOld) hPair
      · exact (hNe (hSingle hi hj hiOld hjOld)).elim
    have hCardNext : next.card = keep.card := Finset.card_image_of_injOn hInj
    have hCardMarked : marked.card ≤ keep.card + shared.card :=
      Finset.card_le_card_sdiff_add_card
    have hStep := previousSupport_card_add_inter_le gate needed hLast
    change (previousSupport gate needed).card + shared.card ≤
      needed.card + (gate.arity - 1) at hStep
    refine ⟨next, hNext, hNextPairs, ?_⟩
    omega
  · let next := marked.map Fin.castSuccEmb
    have hOldMarked : marked ⊆ oldWires needed := by
      simpa only [previousSupport, ite_eq_right hLast, Finset.union_empty] using hMarked
    have hNext : next ⊆ needed := by
      intro v hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hv
      exact (mem_oldWires_iff needed i).mp (hOldMarked hi)
    have hNextPairs : ∀ u ∈ next, ∀ v ∈ next, u ≠ v → after u v := by
      intro u hu v hv hDiff
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hu
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hv
      have hNe : i ≠ j := fun h ↦ hDiff (congrArg Fin.castSucc h)
      exact hOld (Or.inl hLast)
        (hPairs i hi j hj hNe)
    have hCard : next.card = marked.card := Finset.card_map _
    have hStep : (previousSupport gate needed).card ≤ needed.card := by
      rw [previousSupport, ite_eq_right hLast, Finset.union_empty, oldWires_card]
      exact Finset.card_erase_le
    refine ⟨next, hNext, hNextPairs, ?_⟩
    omega

end PvsNP.Circuits
