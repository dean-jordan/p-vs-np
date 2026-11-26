module

public import PvsNP.Circuits.BinaryBasis
public import PvsNP.Circuits.PairRestriction

/-! # Two incompatible restrictions through one arbitrary binary gate -/

namespace PvsNP.Circuits

variable {n : Nat}

/-- Restrict the output to a given table on two pins, holding all other pins fixed. -/
@[expose] public def PairCube (f : (Fin n → Bool) → Bool) (i j : Fin n)
    (table : BinaryFunction) : Prop :=
  ∃ x : Bool → Bool → Fin n → Bool,
    (∀ a b, x a b i = a) ∧ (∀ a b, x a b j = b) ∧
    (∀ a b p, p ≠ i → p ≠ j → x a b p = x false false p) ∧
    ∀ a b, f (x a b) = table a b

/-- An AND table with independently chosen input and output polarities. -/
@[expose] public def signedAnd (leftFlip rightFlip outputFlip : Bool) : BinaryFunction :=
  fun a b ↦ (((a ^^ leftFlip) && (b ^^ rightFlip)) ^^ outputFlip)

@[expose] public def AndRestriction (f : (Fin n → Bool) → Bool) (i j : Fin n) : Prop :=
  ∃ leftFlip rightFlip outputFlip : Bool, PairCube f i j (signedAnd leftFlip rightFlip outputFlip)

/-- Two contexts give a parity table and a signed-AND table on the same pins. -/
@[expose] public def BasisPair (f : (Fin n → Bool) → Bool) (i j : Fin n) : Prop :=
  ParityRestriction f i j ∧ AndRestriction f i j

public theorem BasisPair.ne {f : (Fin n → Bool) → Bool} {i j : Fin n}
    (h : BasisPair f i j) : i ≠ j := h.1.ne

public theorem BasisPair.swap {f : (Fin n → Bool) → Bool} {i j : Fin n}
    (h : BasisPair f i j) : BasisPair f j i := by
  obtain ⟨l, r, o, x, hLeft, hRight, hOff, hEval⟩ := h.2
  refine ⟨h.1.swap, r, l, o, fun a b ↦ x b a, fun a b ↦ hRight b a, fun a b ↦ hLeft b a,
    fun a b p hj hi ↦ hOff b a p hi hj, ?_⟩
  intro a b
  rw [hEval]
  simp only [signedAnd, Bool.and_comm (b ^^ l)]

private theorem cube_agree_at {i j : Fin n} {x : Bool → Bool → Fin n → Bool}
    (hLeft : ∀ a b, x a b i = a) (hRight : ∀ a b, x a b j = b)
    (hOff : ∀ a b p, p ≠ i → p ≠ j → x a b p = x false false p)
    (a b a' b' : Bool) (p : Fin n) (ha : p = i → a = a') (hb : p = j → b = b') :
    x a b p = x a' b' p := by
  by_cases hi : p = i
  · subst p
    rw [hLeft, hLeft, ha rfl]
  · by_cases hj : p = j
    · subst p
      rw [hRight, hRight, hb rfl]
    · exact (hOff a b p hi hj).trans (hOff a' b' p hi hj).symm

private theorem parity_rows_different (p : Bool) :
    (((false : Bool) == false) == p) ≠ (((true : Bool) == false) == p) := by
  cases p <;> decide

private theorem cube_of_old (gate : Gate n) (op : BinaryFunction)
    (needed : Finset (Fin (n + 1))) (g : (Fin (n + 1) → Bool) → Bool)
    (hSupport : ∀ x y, (∀ p ∈ needed, x p = y p) → g x = g y)
    {i j : Fin n} {table : BinaryFunction}
    (hFixed : Fin.last n ∉ needed ∨ (i ∉ gateInputs gate ∧ j ∉ gateInputs gate))
    (h : PairCube (fun z ↦ g (gate.extendWith op z)) i j table) :
    PairCube g i.castSucc j.castSucc table := by
  obtain ⟨x, hLeft, hRight, hOff, hEval⟩ := h
  let y (a b : Bool) : Fin (n + 1) → Bool :=
    Fin.lastCases (gate.evalWith op (x false false)) (x a b)
  have hResult (a b : Bool) : g (y a b) = g (gate.extendWith op (x a b)) := by
    apply hSupport
    intro p
    refine Fin.lastCases ?_ (fun q ↦ ?_) p
    · intro hNeeded
      simp only [y, Fin.lastCases_last, Gate.extendWith_last]
      rcases hFixed with hUnused | ⟨hi, hj⟩
      · exact (hUnused hNeeded).elim
      · symm
        apply gate_evalWith_eq_of_agree
        intro q hq
        exact hOff a b q (fun he ↦ hi (he ▸ hq)) (fun he ↦ hj (he ▸ hq))
    · intro _
      simp only [y, Fin.lastCases_castSucc, Gate.extendWith_castSucc]
  refine ⟨y, ?_, ?_, ?_, fun a b ↦ (hResult a b).trans (hEval a b)⟩
  · intro a b
    simpa only [y, Fin.lastCases_castSucc] using hLeft a b
  · intro a b
    simpa only [y, Fin.lastCases_castSucc] using hRight a b
  · intro a b p
    refine Fin.lastCases ?_ (fun q ↦ ?_) p
    · intro _ _
      simp only [y, Fin.lastCases_last]
    · intro hi hj
      simpa only [y, Fin.lastCases_castSucc] using hOff a b q
        (fun he ↦ hi (congrArg Fin.castSucc he)) (fun he ↦ hj (congrArg Fin.castSucc he))

private theorem cube_promote (gate : Gate n) (op : BinaryFunction)
    (needed : Finset (Fin (n + 1))) (g : (Fin (n + 1) → Bool) → Bool)
    (hSupport : ∀ x y, (∀ p ∈ needed, x p = y p) → g x = g y)
    {i j : Fin n} {table : BinaryFunction}
    (hi : i ∉ oldWires needed) (hj : j ∉ gateInputs gate) (hNe : i ≠ j)
    (hEssential : ∃ b, table false b ≠ table true b)
    (h : PairCube (fun z ↦ g (gate.extendWith op z)) i j table) :
    ∃ flip : Bool, PairCube g (Fin.last n) j.castSucc (fun a b ↦ table (a ^^ flip) b) := by
  have hiUnused : i.castSucc ∉ needed := fun hm ↦ hi ((mem_oldWires_iff needed i).mpr hm)
  obtain ⟨x, hLeft, hRight, hOff, hEval⟩ := h
  obtain ⟨essential, hEssential⟩ := hEssential
  dsimp only at hEval
  let u (a : Bool) := gate.evalWith op (x a false)
  have hIndependent (a b : Bool) : gate.evalWith op (x a b) = u a := by
    apply gate_evalWith_eq_of_agree
    intro p hp
    exact cube_agree_at hLeft hRight hOff a b a false p (fun _ ↦ rfl)
      (fun he ↦ (hj (he ▸ hp)).elim)
  have hDistinct : u false ≠ u true := by
    intro hEqual
    have hSame : g (gate.extendWith op (x false essential)) =
        g (gate.extendWith op (x true essential)) := by
      apply hSupport
      intro p
      refine Fin.lastCases ?_ (fun q ↦ ?_) p
      · intro _
        rw [Gate.extendWith_last, Gate.extendWith_last, hIndependent, hIndependent]
        exact hEqual
      · intro hNeeded
        simp only [Gate.extendWith_castSucc]
        exact cube_agree_at hLeft hRight hOff false essential true essential q
          (fun he ↦ (hiUnused (congrArg Fin.castSucc he ▸ hNeeded)).elim) (fun _ ↦ rfl)
    rw [hEval false essential, hEval true essential] at hSame
    exact hEssential hSame
  let flip := u false
  let decode (a : Bool) := a ^^ flip
  have hDecode (a : Bool) : u (decode a) = a := by
    have hFlip := Bool.eq_not_of_ne hDistinct.symm
    cases hZero : u false <;> cases a <;> simp [decode, flip, hZero, hFlip]
  let y (a b : Bool) : Fin (n + 1) → Bool :=
    Fin.lastCases a (fun p ↦ if p = i then x false false i else x (decode a) b p)
  have hResult (a b : Bool) : g (y a b) = g (gate.extendWith op (x (decode a) b)) := by
    apply hSupport
    intro p
    refine Fin.lastCases ?_ (fun q ↦ ?_) p
    · intro _
      simp only [y, Fin.lastCases_last, Gate.extendWith_last, hIndependent, hDecode]
    · intro hNeeded
      have hqi : q ≠ i := fun he ↦ hiUnused (congrArg Fin.castSucc he ▸ hNeeded)
      simp only [y, Fin.lastCases_castSucc, Gate.extendWith_castSucc, ite_eq_right hqi]
  refine ⟨flip, y, ?_, ?_, ?_, fun a b ↦ (hResult a b).trans (hEval (decode a) b)⟩
  · intro a b
    simp only [y, Fin.lastCases_last]
  · intro a b
    simp only [y, Fin.lastCases_castSucc, ite_eq_right hNe.symm, hRight]
  · intro a b p
    refine Fin.lastCases ?_ (fun q ↦ ?_) p
    · intro hLast _
      exact (hLast rfl).elim
    · intro _ hOther
      have hqj : q ≠ j := fun he ↦ hOther (congrArg Fin.castSucc he)
      by_cases hqi : q = i
      · simp only [y, Fin.lastCases_castSucc, ite_eq_left hqi]
      · simp only [y, Fin.lastCases_castSucc, ite_eq_right hqi]
        exact (hOff (decode a) b q hqi hqj).trans (hOff (decode false) false q hqi hqj).symm

public theorem basisPair_of_old (gate : Gate n) (op : BinaryFunction)
    (needed : Finset (Fin (n + 1))) (g : (Fin (n + 1) → Bool) → Bool)
    (hSupport : ∀ x y, (∀ p ∈ needed, x p = y p) → g x = g y)
    {i j : Fin n}
    (hFixed : Fin.last n ∉ needed ∨ (i ∉ gateInputs gate ∧ j ∉ gateInputs gate))
    (h : BasisPair (fun z ↦ g (gate.extendWith op z)) i j) :
    BasisPair g i.castSucc j.castSucc := by
  obtain ⟨p, hParity⟩ := h.1
  obtain ⟨l, r, o, hAnd⟩ := h.2
  exact ⟨⟨p, cube_of_old gate op needed g hSupport hFixed
    (table := fun a b ↦ (a == b) == p) hParity⟩,
    ⟨l, r, o, cube_of_old gate op needed g hSupport hFixed hAnd⟩⟩

public theorem basisPair_promote (gate : Gate n) (op : BinaryFunction)
    (needed : Finset (Fin (n + 1))) (g : (Fin (n + 1) → Bool) → Bool)
    (hSupport : ∀ x y, (∀ p ∈ needed, x p = y p) → g x = g y)
    {i j : Fin n} (hi : i ∉ oldWires needed) (hj : j ∉ gateInputs gate)
    (h : BasisPair (fun z ↦ g (gate.extendWith op z)) i j) :
    BasisPair g (Fin.last n) j.castSucc := by
  obtain ⟨p, hParity⟩ := h.1
  obtain ⟨l, r, o, hAnd⟩ := h.2
  constructor
  · obtain ⟨flip, x, hLeft, hRight, hOff, hEval⟩ :=
      cube_promote gate op needed g hSupport hi hj h.ne
        (table := fun a b ↦ (a == b) == p) ⟨false, parity_rows_different p⟩ hParity
    refine ⟨p ^^ flip, x, hLeft, hRight, hOff, ?_⟩
    intro a b
    rw [hEval]
    cases a <;> cases b <;> cases p <;> cases flip <;> rfl
  · have hEssential : ∃ b, signedAnd l r o false b ≠ signedAnd l r o true b := by
      refine ⟨!r, ?_⟩
      cases l <;> cases r <;> cases o <;> decide
    obtain ⟨flip, x, hLeft, hRight, hOff, hEval⟩ :=
      cube_promote gate op needed g hSupport hi hj h.ne hEssential hAnd
    refine ⟨flip ^^ l, r, o, x, hLeft, hRight, hOff, ?_⟩
    intro a b
    rw [hEval]
    simp only [signedAnd, Bool.xor_assoc]

private theorem exclusive_gate_factor (gate : Gate n) (op : BinaryFunction)
    (needed : Finset (Fin (n + 1))) (g : (Fin (n + 1) → Bool) → Bool)
    (hSupport : ∀ x y, (∀ p ∈ needed, x p = y p) → g x = g y)
    {i j : Fin n} (hi : i ∉ oldWires needed) (hj : j ∉ oldWires needed)
    {x : Bool → Bool → Fin n → Bool} {table : BinaryFunction}
    (hOff : ∀ a b p, p ≠ i → p ≠ j → x a b p = x false false p)
    (hEval : ∀ a b, g (gate.extendWith op (x a b)) = table a b) :
    ∃ w : Bool → Bool, ∀ a b, w (gate.evalWith op (x a b)) = table a b := by
  refine ⟨fun t ↦ g (Fin.lastCases t (x false false)), fun a b ↦ ?_⟩
  rw [← hEval a b]
  apply hSupport
  intro p
  refine Fin.lastCases ?_ (fun q ↦ ?_) p
  · intro _
    simp only [Fin.lastCases_last, Gate.extendWith_last]
  · intro hNeeded
    simp only [Fin.lastCases_castSucc, Gate.extendWith_castSucc]
    have hOld := (mem_oldWires_iff needed q).mpr hNeeded
    exact (hOff a b q (fun he ↦ hi (he ▸ hOld)) (fun he ↦ hj (he ▸ hOld))).symm

/-- Both exclusive pins would reach the output only through one Boolean signal.
With the pin values fixed, every cube uses the same gate table. -/
public theorem not_basisPair_of_exclusive_sources (gate : Gate n) (op : BinaryFunction)
    (needed : Finset (Fin (n + 1))) (g : (Fin (n + 1) → Bool) → Bool)
    (hSupport : ∀ x y, (∀ p ∈ needed, x p = y p) → g x = g y)
    {i j : Fin n} (hi : i ∉ oldWires needed) (hj : j ∉ oldWires needed) :
    ¬ BasisPair (fun z ↦ g (gate.extendWith op z)) i j := by
  intro h
  have hij := h.ne
  obtain ⟨p, x, hLeft, hRight, hOff, hEval⟩ := h.1
  obtain ⟨w, hFactor⟩ := exclusive_gate_factor gate op needed g hSupport hi hj hOff
    (table := fun a b ↦ (a == b) == p) hEval
  have hSourceLeft : i ∈ gateInputs gate := by
    by_contra hAbsent
    have hGate : gate.evalWith op (x false false) = gate.evalWith op (x true false) :=
      gate_evalWith_eq_of_agree gate op _ _ fun k hk ↦ cube_agree_at hLeft hRight hOff
        false false true false k (fun he ↦ (hAbsent (he ▸ hk)).elim) (fun _ ↦ rfl)
    have hSame := congrArg w hGate
    rw [hFactor false false, hFactor true false] at hSame
    exact parity_rows_different p hSame
  have hSourceRight : j ∈ gateInputs gate := by
    by_contra hAbsent
    have hGate : gate.evalWith op (x false false) = gate.evalWith op (x false true) :=
      gate_evalWith_eq_of_agree gate op _ _ fun k hk ↦ cube_agree_at hLeft hRight hOff
        false false false true k (fun _ ↦ rfl) (fun he ↦ (hAbsent (he ▸ hk)).elim)
    have hSame := congrArg w hGate
    rw [hFactor false false, hFactor false true] at hSame
    exact parity_rows_different p hSame
  have hSources : ({i, j} : Finset (Fin n)) = gateInputs gate := by
    apply Finset.eq_of_subset_of_card_le
    · intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hSourceLeft
      · rcases Finset.mem_singleton.mp hk with rfl
        exact hSourceRight
    · rw [Finset.card_pair hij]
      have hArity : gate.arity ≤ 2 := by cases gate <;> simp [Gate.arity]
      exact (gateInputs_card_le gate).trans hArity
  let table (a b : Bool) := gate.evalWith op (fun k ↦ if k = i then a else b)
  have hCanonical {cube : Bool → Bool → Fin n → Bool}
      (hL : ∀ a b, cube a b i = a) (hR : ∀ a b, cube a b j = b) (a b : Bool) :
      gate.evalWith op (cube a b) = table a b := by
    apply gate_evalWith_eq_of_agree
    intro k hk
    rw [← hSources] at hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · simpa only [ite_true] using hL a b
    · rcases Finset.mem_singleton.mp hk with rfl
      simpa only [ite_eq_right hij.symm] using hR a b
  have hParity (a b : Bool) : w (table a b) = ((a == b) == p) :=
    (congrArg w (hCanonical hLeft hRight a b)).symm.trans (hFactor a b)
  have hNonconstant : w false ≠ w true := by
    intro hEqual
    have hSame : w (table false false) = w (table true false) := by
      cases table false false <;> cases table true false <;> simp [hEqual]
    rw [hParity false false, hParity true false] at hSame
    exact parity_rows_different p hSame
  have hInjective : Function.Injective w := by
    intro a b hab
    cases a <;> cases b
    · rfl
    · exact (hNonconstant hab).elim
    · exact (hNonconstant hab.symm).elim
    · rfl
  obtain ⟨l, r, o, y, hYLeft, hYRight, hYOff, hYEval⟩ := h.2
  obtain ⟨v, hYFactor⟩ := exclusive_gate_factor gate op needed g hSupport hi hj hYOff hYEval
  have hAnd (a b : Bool) : v (table a b) = signedAnd l r o a b :=
    (congrArg v (hCanonical hYLeft hYRight a b)).symm.trans (hYFactor a b)
  have hSame : table (!l) (!r) = table l r := by
    apply hInjective
    rw [hParity, hParity]
    cases l <;> cases r <;> rfl
  have hImpossible := (hAnd (!l) (!r)).symm.trans ((congrArg v hSame).trans (hAnd l r))
  cases l <;> cases r <;> cases o <;> cases hImpossible

end PvsNP.Circuits
