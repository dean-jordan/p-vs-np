module

public import PvsNP.Circuits.InputSupport

/-! # Two-coordinate parity restrictions -/

namespace PvsNP.Circuits

variable {n : Nat}

/-- A two-coordinate restriction computes XOR or XNOR after fixing every
other input. The polarity records which parity is accepted. -/
@[expose] public def ParityRestriction (f : (Fin n → Bool) → Bool) (i j : Fin n) : Prop :=
  ∃ (polarity : Bool) (x : Bool → Bool → Fin n → Bool),
    (∀ a b, x a b i = a) ∧ (∀ a b, x a b j = b) ∧
    (∀ a b p, p ≠ i → p ≠ j → x a b p = x false false p) ∧
    ∀ a b, f (x a b) = ((a == b) == polarity)

public theorem ParityRestriction.ne {f : (Fin n → Bool) → Bool} {i j : Fin n}
    (h : ParityRestriction f i j) : i ≠ j := by
  intro hij
  subst j
  obtain ⟨_, _, hLeft, hRight, _, _⟩ := h
  exact Bool.false_ne_true ((hLeft false true).symm.trans (hRight false true))

public theorem ParityRestriction.swap {f : (Fin n → Bool) → Bool} {i j : Fin n}
    (h : ParityRestriction f i j) : ParityRestriction f j i := by
  obtain ⟨polarity, x, hLeft, hRight, hOff, hEval⟩ := h
  refine ⟨polarity, fun a b ↦ x b a, fun a b ↦ hRight b a, fun a b ↦ hLeft b a,
    fun a b p hj hi ↦ hOff b a p hi hj, ?_⟩
  intro a b
  rw [hEval]
  cases a <;> cases b <;> rfl

private theorem pairCube_agree {i j : Fin n} {x : Bool → Bool → Fin n → Bool}
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

private theorem parity_rows_ne (polarity : Bool) :
    (((false : Bool) == false) == polarity) ≠ (((true : Bool) == false) == polarity) := by
  cases polarity <;> decide

/-- One AND or OR, even with arbitrary unary maps on its inputs and
output, cannot compute parity on two inputs. -/
public theorem not_parity_of_binary_unaries (op : BinaryOp) (u v w : Bool → Bool)
    (polarity : Bool) : ¬ ∀ a b, w (op.eval (u a) (v b)) = ((a == b) == polarity) := by
  intro hEval
  have hDistinct : u false ≠ u true := by
    intro hEqual
    have hSame := congrArg (fun t ↦ w (op.eval t (v false))) hEqual
    rw [hEval false false, hEval true false] at hSame
    exact parity_rows_ne polarity hSame
  let control := match op with
    | .and => false
    | .or => true
  have hControl (b : Bool) : op.eval control b = control := by cases op <;> rfl
  have hPreimage : ∃ a, u a = control := by
    by_cases hFirst : u false = control
    · exact ⟨false, hFirst⟩
    · exact ⟨true, (Bool.eq_not_of_ne hDistinct.symm).trans
        (Bool.eq_not_of_ne (Ne.symm hFirst)).symm⟩
  obtain ⟨a, ha⟩ := hPreimage
  have hSame : w (op.eval (u a) (v (!a))) = w (op.eval (u a) (v a)) := by
    simp only [ha, hControl]
  rw [hEval a (!a), hEval a a] at hSame
  cases a <;> cases polarity <;> cases hSame

/-- Keep the old pins when the new wire is unused or its gate reads neither
of the two varying inputs. -/
public theorem parityRestriction_of_old (gate : Gate n) (needed : Finset (Fin (n + 1)))
    (g : (Fin (n + 1) → Bool) → Bool)
    (hSupport : ∀ x y, (∀ p ∈ needed, x p = y p) → g x = g y)
    {i j : Fin n}
    (hFixed : Fin.last n ∉ needed ∨ (i ∉ gateInputs gate ∧ j ∉ gateInputs gate))
    (h : ParityRestriction (fun z ↦ g (gate.extend z)) i j) :
    ParityRestriction g i.castSucc j.castSucc := by
  obtain ⟨polarity, x, hLeft, hRight, hOff, hEval⟩ := h
  let y (a b : Bool) : Fin (n + 1) → Bool := Fin.lastCases (gate.eval (x false false)) (x a b)
  have hResult (a b : Bool) : g (y a b) = g (gate.extend (x a b)) := by
    apply hSupport
    intro p
    refine Fin.lastCases ?_ (fun q ↦ ?_) p
    · intro hNeeded
      simp only [y, Fin.lastCases_last, Gate.extend_last]
      rcases hFixed with hUnused | ⟨hi, hj⟩
      · exact (hUnused hNeeded).elim
      · symm
        apply gate_eval_eq_of_agree
        intro q hq
        exact hOff a b q (fun he ↦ hi (he ▸ hq)) (fun he ↦ hj (he ▸ hq))
    · intro _
      simp only [y, Fin.lastCases_castSucc, Gate.extend_castSucc]
  refine ⟨polarity, y, ?_, ?_, ?_, fun a b ↦ (hResult a b).trans (hEval a b)⟩
  · intro a b
    simpa only [y, Fin.lastCases_castSucc] using hLeft a b
  · intro a b
    simpa only [y, Fin.lastCases_castSucc] using hRight a b
  · intro a b p
    refine Fin.lastCases ?_ (fun q ↦ ?_) p
    · intro _ _
      simp only [y, Fin.lastCases_last]
    · intro hi hj
      simpa only [y, Fin.lastCases_castSucc] using
        hOff a b q (fun he ↦ hi (congrArg Fin.castSucc he))
          (fun he ↦ hj (congrArg Fin.castSucc he))

/-- Replace an exclusive input pin by the new gate output. The other pin
is not read by that gate, so the output's possible negation is fixed. -/
public theorem parityRestriction_promote (gate : Gate n) (needed : Finset (Fin (n + 1)))
    (g : (Fin (n + 1) → Bool) → Bool)
    (hSupport : ∀ x y, (∀ p ∈ needed, x p = y p) → g x = g y)
    {i j : Fin n} (hi : i ∉ oldWires needed) (hj : j ∉ gateInputs gate)
    (h : ParityRestriction (fun z ↦ g (gate.extend z)) i j) :
    ParityRestriction g (Fin.last n) j.castSucc := by
  have hij := h.ne
  have hiUnused : i.castSucc ∉ needed := fun hm ↦ hi ((mem_oldWires_iff needed i).mpr hm)
  obtain ⟨polarity, x, hLeft, hRight, hOff, hEval⟩ := h
  dsimp only at hEval
  let u (a : Bool) := gate.eval (x a false)
  have hIndependent (a b : Bool) : gate.eval (x a b) = u a := by
    apply gate_eval_eq_of_agree
    intro p hp
    exact pairCube_agree hLeft hRight hOff a b a false p (fun _ ↦ rfl)
      (fun he ↦ (hj (he ▸ hp)).elim)
  have hDistinct : u false ≠ u true := by
    intro hEqual
    have hSame : g (gate.extend (x false false)) = g (gate.extend (x true false)) := by
      apply hSupport
      intro p
      refine Fin.lastCases ?_ (fun q ↦ ?_) p
      · intro _
        simpa only [Gate.extend_last] using hEqual
      · intro hNeeded
        simp only [Gate.extend_castSucc]
        exact pairCube_agree hLeft hRight hOff false false true false q
          (fun he ↦ (hiUnused (congrArg Fin.castSucc he ▸ hNeeded)).elim) (fun _ ↦ rfl)
    rw [hEval false false, hEval true false] at hSame
    exact parity_rows_ne polarity hSame
  let decode (a : Bool) := a ^^ u false
  let newPolarity := polarity ^^ u false
  have hDecode (a : Bool) : u (decode a) = a := by
    have hFlip := Bool.eq_not_of_ne hDistinct.symm
    cases hZero : u false <;> cases a <;> simp [decode, hZero, hFlip]
  have hPolarity (a b : Bool) : ((decode a == b) == polarity) = ((a == b) == newPolarity) := by
    cases hZero : u false <;> cases a <;> cases b <;> cases polarity <;>
      simp [decode, newPolarity, hZero]
  let y (a b : Bool) : Fin (n + 1) → Bool :=
    Fin.lastCases a (fun p ↦ if p = i then x false false i else x (decode a) b p)
  have hResult (a b : Bool) : g (y a b) = g (gate.extend (x (decode a) b)) := by
    apply hSupport
    intro p
    refine Fin.lastCases ?_ (fun q ↦ ?_) p
    · intro _
      simp only [y, Fin.lastCases_last, Gate.extend_last, hIndependent, hDecode]
    · intro hNeeded
      have hqi : q ≠ i := fun he ↦ hiUnused (congrArg Fin.castSucc he ▸ hNeeded)
      simp only [y, Fin.lastCases_castSucc, Gate.extend_castSucc, ite_eq_right hqi]
  refine ⟨newPolarity, y, ?_, ?_, ?_, ?_⟩
  · intro a b
    simp only [y, Fin.lastCases_last]
  · intro a b
    simp only [y, Fin.lastCases_castSucc, ite_eq_right hij.symm, hRight]
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
  · intro a b
    exact (hResult a b).trans ((hEval (decode a) b).trans (hPolarity a b))

/-- Two inputs that both disappear from the old support cannot interact by
parity through the single new gate. -/
public theorem not_parityRestriction_of_exclusive_sources (gate : Gate n)
    (needed : Finset (Fin (n + 1))) (g : (Fin (n + 1) → Bool) → Bool)
    (hSupport : ∀ x y, (∀ p ∈ needed, x p = y p) → g x = g y)
    {i j : Fin n} (hi : i ∉ oldWires needed) (hj : j ∉ oldWires needed) :
    ¬ ParityRestriction (fun z ↦ g (gate.extend z)) i j := by
  intro h
  have hij := h.ne
  have hiUnused : i.castSucc ∉ needed := fun hm ↦ hi ((mem_oldWires_iff needed i).mpr hm)
  have hjUnused : j.castSucc ∉ needed := fun hm ↦ hj ((mem_oldWires_iff needed j).mpr hm)
  obtain ⟨polarity, x, hLeft, hRight, hOff, hEval⟩ := h
  let w (t : Bool) := g (Fin.lastCases t (x false false))
  have hResult (a b : Bool) : w (gate.eval (x a b)) = ((a == b) == polarity) := by
    rw [← hEval a b]
    apply hSupport
    intro p
    refine Fin.lastCases ?_ (fun q ↦ ?_) p
    · intro _
      simp only [Fin.lastCases_last, Gate.extend_last]
    · intro hNeeded
      simp only [Fin.lastCases_castSucc, Gate.extend_castSucc]
      exact (hOff a b q (fun he ↦ hiUnused (congrArg Fin.castSucc he ▸ hNeeded))
        (fun he ↦ hjUnused (congrArg Fin.castSucc he ▸ hNeeded))).symm
  have hSourceLeft : i ∈ gateInputs gate := by
    by_contra hAbsent
    have hEqual : gate.eval (x false false) = gate.eval (x true false) :=
      gate_eval_eq_of_agree gate _ _ fun p hp ↦
        pairCube_agree hLeft hRight hOff false false true false p
          (fun he ↦ (hAbsent (he ▸ hp)).elim) (fun _ ↦ rfl)
    have hSame := congrArg w hEqual
    rw [hResult false false, hResult true false] at hSame
    exact parity_rows_ne polarity hSame
  have hSourceRight : j ∈ gateInputs gate := by
    by_contra hAbsent
    have hEqual : gate.eval (x false false) = gate.eval (x false true) :=
      gate_eval_eq_of_agree gate _ _ fun p hp ↦
        pairCube_agree hLeft hRight hOff false false false true p (fun _ ↦ rfl)
          (fun he ↦ (hAbsent (he ▸ hp)).elim)
    have hSame := congrArg w hEqual
    rw [hResult false false, hResult false true] at hSame
    exact parity_rows_ne polarity hSame
  cases gate with
  | const value => simp only [gateInputs, Finset.notMem_empty] at hSourceLeft
  | not source =>
    have hL : i = source := by simpa only [gateInputs, Finset.mem_singleton] using hSourceLeft
    have hR : j = source := by simpa only [gateInputs, Finset.mem_singleton] using hSourceRight
    exact hij (hL.trans hR.symm)
  | binary op left right =>
    have hL : i = left ∨ i = right := by
      simpa only [gateInputs, Finset.mem_insert, Finset.mem_singleton] using hSourceLeft
    have hR : j = left ∨ j = right := by
      simpa only [gateInputs, Finset.mem_insert, Finset.mem_singleton] using hSourceRight
    rcases hL with hL | hL <;> rcases hR with hR | hR
    · exact hij (hL.trans hR.symm)
    · apply not_parity_of_binary_unaries op id id w polarity
      intro a b
      simpa only [Gate.eval, ← hL, ← hR, hLeft, hRight, id_eq] using hResult a b
    · apply not_parity_of_binary_unaries op id id w polarity
      intro a b
      have hValue := hResult b a
      simp only [Gate.eval, ← hL, ← hR, hLeft, hRight] at hValue
      exact hValue.trans (by cases a <;> cases b <;> rfl)
    · exact hij (hL.trans hR.symm)

end PvsNP.Circuits
