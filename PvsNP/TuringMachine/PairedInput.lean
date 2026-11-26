module

public import PvsNP.Complexity.Classes

import Mathlib.Basic.Finite.Prod
import Mathlib.Basic.Finite.Sum

/-! # Simulating a binary machine on paired input symbols

Each physical cell contains two consecutive symbols of the simulated tape.
One transition suffices across a cell boundary. Moving between the two
symbols of one cell takes two transitions, because Cook's head must move.
-/

public section

namespace PvsNP.Machine

open Turing

variable {α : Type}

/-- Encode every input letter with two bits. -/
@[expose] def packInput (code : α ↪ Bool × Bool) (word : List α) : BinaryWord :=
  word.flatMap fun a ↦ [(code a).1, (code a).2]

@[simp] theorem length_packInput (code : α ↪ Bool × Bool) (word : List α) :
    (packInput code word).length = 2 * word.length := by
  induction word with
  | nil => rfl
  | cons a tail ih =>
    simp only [packInput, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    omega

theorem packInput_injective (code : α ↪ Bool × Bool) : Function.Injective (packInput code) := by
  intro x y h
  induction x generalizing y with
  | nil =>
    have hLen := congrArg List.length h
    simp only [length_packInput, List.length_nil, Nat.mul_zero] at hLen
    exact (List.length_eq_zero_iff.mp (by omega : y.length = 0)).symm
  | cons a tail ih =>
    cases y with
    | nil => cases h
    | cons b rest =>
      change (code a).1 :: (code a).2 :: packInput code tail =
        (code b).1 :: (code b).2 :: packInput code rest at h
      obtain ⟨hFirst, hSecond, hTail⟩ := List.cons.inj h |>.imp_right List.cons.inj
      rw [code.injective (Prod.ext hFirst hSecond), ih hTail]

variable (M : Machine Bool)

private abbrev Block := M.Symbol × M.Symbol

private abbrev blockInhabited : Inhabited M.Block := ⟨(M.blank, M.blank)⟩

private def selectBlock (offset : Bool) (block : M.Block) : M.Symbol :=
  if offset then block.2 else block.1

private def writeBlock (offset : Bool) (s : M.Symbol) (block : M.Block) : M.Block :=
  if offset then (block.1, s) else (s, block.2)

private def leavesBlock (offset : Bool) : Dir → Bool
  | .left => !offset
  | .right => offset

private abbrev PairState := (Bool × M.State) ⊕ (Bool × (M.State ⊕ Bool))

private def readyState (offset : Bool) (state : M.State ⊕ Bool) : M.PairState ⊕ Bool :=
  state.map (fun q ↦ .inl (offset, q)) id

private def packedSymbol (code : α ↪ Bool × Bool) : α ↪ M.Block where
  toFun a := (M.input (code a).1, M.input (code a).2)
  inj' := by
    intro a b h
    change (M.input (code a).1, M.input (code a).2) =
      (M.input (code b).1, M.input (code b).2) at h
    exact code.injective (Prod.ext (M.input.injective (congrArg Prod.fst h))
      (M.input.injective (congrArg Prod.snd h)))

/-- Read the original alphabet through pairs of virtual binary-machine tape cells. -/
@[reducible] def pairedInput (code : α ↪ Bool × Bool) : Machine α := by
  let _ : Finite M.State := M.stateFinite
  let _ : Finite M.Symbol := M.symbolFinite
  exact {
    State := M.PairState
    Symbol := M.Block
    stateFinite := inferInstance
    symbolFinite := inferInstance
    initial := .inl (false, M.initial)
    blank := (M.blank, M.blank)
    input := M.packedSymbol code
    input_ne_blank := by
      intro a h
      change (M.input (code a).1, M.input (code a).2) = (M.blank, M.blank) at h
      exact M.input_ne_blank (code a).1 (congrArg Prod.fst h)
    transition := fun state block ↦ match state with
      | .inl (offset, q) =>
        let (next, s, dir) := M.transition q (M.selectBlock offset block)
        let written := M.writeBlock offset s block
        if leavesBlock offset dir then (M.readyState (!offset) next, written, dir)
        else (.inl (.inr (!offset, next)), written, .right)
      | .inr (offset, next) => (M.readyState offset next, block, .left) }

private def blockSymbols (backward : Bool) (block : M.Block) : List M.Symbol :=
  if backward then [block.2, block.1] else [block.1, block.2]

private def expandBlocks (backward : Bool) (half : @ListBlank M.Block M.blockInhabited) :
    @ListBlank M.Symbol M.tapeInhabited :=
  @ListBlank.flatMap _ _ M.blockInhabited M.tapeInhabited half (M.blockSymbols backward)
    ⟨2, by cases backward <;> rfl⟩

private theorem expandBlocks_cons (backward : Bool) (a : M.Block)
    (half : @ListBlank M.Block M.blockInhabited) :
    let _ := M.blockInhabited
    let _ := M.tapeInhabited
    M.expandBlocks backward (half.cons a) = (M.expandBlocks backward half).append
      (M.blockSymbols backward a) := by
  exact @ListBlank.cons_flatMap _ _ M.blockInhabited M.tapeInhabited a half
    (M.blockSymbols backward) _

private def projectBlocks (offset : Bool) (tape : @Turing.Tape M.Block M.blockInhabited) : M.Tape :=
  let _ := M.blockInhabited
  let _ := M.tapeInhabited
  if offset then
    ⟨tape.head.2, (M.expandBlocks true tape.left).cons tape.head.1, M.expandBlocks false tape.right⟩
  else
    ⟨tape.head.1, M.expandBlocks true tape.left, (M.expandBlocks false tape.right).cons tape.head.2⟩

private theorem projectBlocks_head (offset : Bool) (tape : @Turing.Tape M.Block M.blockInhabited) :
    @Tape.head _ M.tapeInhabited (M.projectBlocks offset tape) =
      M.selectBlock offset (@Tape.head _ M.blockInhabited tape) := by
  cases offset <;> rfl

private theorem projectBlocks_write (offset : Bool) (s : M.Symbol)
    (tape : @Turing.Tape M.Block M.blockInhabited) :
    let _ := M.blockInhabited
    let _ := M.tapeInhabited
    M.projectBlocks offset (tape.write (M.writeBlock offset s tape.head)) =
      (M.projectBlocks offset tape).write s := by
  cases offset <;> rfl

private theorem projectBlocks_move_inside (offset : Bool) (dir : Dir)
    (tape : @Turing.Tape M.Block M.blockInhabited) (h : leavesBlock offset dir = false) :
    let _ := M.tapeInhabited
    (M.projectBlocks offset tape).move dir = M.projectBlocks (!offset) tape := by
  cases tape
  cases offset <;> cases dir <;>
    simp_all [leavesBlock, projectBlocks, Tape.move]

private theorem projectBlocks_move_across (offset : Bool) (dir : Dir)
    (tape : @Turing.Tape M.Block M.blockInhabited) (h : leavesBlock offset dir = true) :
    let _ := M.blockInhabited
    let _ := M.tapeInhabited
    (M.projectBlocks offset tape).move dir = M.projectBlocks (!offset) (tape.move dir) := by
  obtain ⟨a, left, right⟩ := tape
  cases offset <;> cases dir <;> simp only [leavesBlock, Bool.not_false, Bool.not_true] at h ⊢
  · obtain ⟨b, tail, rfl⟩ := @ListBlank.exists_cons _ M.blockInhabited left
    simp [projectBlocks, Tape.move, expandBlocks_cons, blockSymbols]
  · contradiction
  · contradiction
  · obtain ⟨b, tail, rfl⟩ := @ListBlank.exists_cons _ M.blockInhabited right
    simp [projectBlocks, Tape.move, expandBlocks_cons, blockSymbols]

private noncomputable def readyConfig (code : α ↪ Bool × Bool)
    (offset : Bool) (state : M.State ⊕ Bool)
    (tape : (M.pairedInput code).Tape) : (M.pairedInput code).Config :=
  ⟨M.readyState offset state, tape⟩

private def virtualConfig (offset : Bool) (state : M.State ⊕ Bool)
    (tape : @Turing.Tape M.Block M.blockInhabited) : M.Config :=
  ⟨state, M.projectBlocks offset tape⟩

private theorem pairedInput_simulates_tick (code : α ↪ Bool × Bool) (offset : Bool)
    (state : M.State ⊕ Bool) (tape : (M.pairedInput code).Tape) :
    ∃ cost ≤ 2, ∃ nextOffset nextTape nextState,
      (M.pairedInput code).run cost (M.readyConfig code offset state tape) =
        M.readyConfig code nextOffset nextState nextTape ∧
      M.tick (M.virtualConfig offset state tape) =
        M.virtualConfig nextOffset nextState nextTape := by
  cases state with
  | inr b => exact ⟨0, by omega, offset, tape, .inr b, rfl, rfl⟩
  | inl q =>
    let _ := M.blockInhabited
    rcases hStep : M.transition q (M.selectBlock offset tape.head) with ⟨next, sym, dir⟩
    let written := tape.write (M.writeBlock offset sym tape.head)
    have hVirtual : M.tick (M.virtualConfig offset (.inl q) tape) =
        ⟨next, @Turing.Tape.move _ M.tapeInhabited dir (M.projectBlocks offset written)⟩ := by
      simp only [tick, virtualConfig, projectBlocks_head, hStep, written, projectBlocks_write]
    by_cases hAcross : leavesBlock offset dir = true
    · refine ⟨1, by omega, !offset, written.move dir, next, ?_, ?_⟩
      · simp only [run_succ, run_zero, tick, readyConfig, readyState, Sum.map_inl,
          pairedInput, hStep, hAcross, ite_true, written]
      · rw [hVirtual, M.projectBlocks_move_across offset dir written hAcross]
        rfl
    · have hInside : leavesBlock offset dir = false := Bool.eq_false_iff.mpr hAcross
      let bounce : (M.pairedInput code).Config := ⟨.inl (.inr (!offset, next)), written.move .right⟩
      have hBounce :
          (M.pairedInput code).tick (M.readyConfig code offset (.inl q) tape) = bounce := by
        simp only [tick, readyConfig, readyState, Sum.map_inl, pairedInput, hStep, hInside,
          Bool.false_eq_true, ite_false, bounce, written]
      refine ⟨2, Nat.le_refl _, !offset, written, next, ?_, ?_⟩
      · rw [show 2 = 1 + 1 from rfl, run_succ, hBounce, run_succ, run_zero]
        simp only [bounce, tick, pairedInput, Tape.write_self, Tape.move_right_left, readyConfig]
      · rw [hVirtual, M.projectBlocks_move_inside offset dir written hInside]
        rfl

private theorem pairedInput_simulates_run (code : α ↪ Bool × Bool) (steps : Nat) (offset : Bool)
    (state : M.State ⊕ Bool) (tape : (M.pairedInput code).Tape) :
    ∃ cost ≤ 2 * steps, ∃ nextOffset nextTape nextState,
      (M.pairedInput code).run cost (M.readyConfig code offset state tape) =
        M.readyConfig code nextOffset nextState nextTape ∧
      M.run steps (M.virtualConfig offset state tape) =
        M.virtualConfig nextOffset nextState nextTape := by
  induction steps generalizing offset state tape with
  | zero => exact ⟨0, Nat.zero_le _, offset, tape, state, rfl, rfl⟩
  | succ steps ih =>
    obtain ⟨cost, hCost, midOffset, midTape, midState, hSim, hStep⟩ :=
      M.pairedInput_simulates_tick code offset state tape
    obtain ⟨rest, hRest, nextOffset, nextTape, nextState, hSimRest, hRun⟩ :=
      ih midOffset midState midTape
    refine ⟨cost + rest, by omega, nextOffset, nextTape, nextState, ?_, ?_⟩
    · rw [run_add, hSim, hSimRest]
    · rw [run_succ, hStep, hRun]

private theorem projectBlocks_first (tape : @Turing.Tape M.Block M.blockInhabited) :
    let _ := M.blockInhabited
    let _ := M.tapeInhabited
    M.projectBlocks false tape = Tape.mk' (M.expandBlocks true tape.left)
      (M.expandBlocks false tape.right₀) := by
  cases tape
  simp only [Tape.right₀, expandBlocks_cons, blockSymbols, Bool.false_eq_true, ite_false,
    ListBlank.append, Tape.mk', ListBlank.head_cons, ListBlank.tail_cons, projectBlocks]

private theorem virtualConfig_start (code : α ↪ Bool × Bool) (word : List α) :
    M.virtualConfig false (.inl M.initial) ((M.pairedInput code).start word).tape =
      M.start (packInput code word) := by
  let _ := M.blockInhabited
  let _ := M.tapeInhabited
  unfold virtualConfig
  rw [projectBlocks_first]
  change (⟨.inl M.initial, Tape.mk' (M.expandBlocks true (ListBlank.mk []))
    (M.expandBlocks false (Tape.mk' (ListBlank.mk [])
      (ListBlank.mk (word.map (M.packedSymbol code)))).right₀)⟩ : M.Config) = _
  simp only [Tape.mk'_right₀, expandBlocks, ListBlank.flatMap_mk, List.flatMap_nil,
    start, Tape.mk₁, Tape.mk₂, packInput, List.flatMap_map, List.map_flatMap]
  rfl

/-- Every halt of the virtual binary machine is reproduced in at most twice the steps. -/
theorem pairedInput_haltsAt (code : α ↪ Bool × Bool) (word : List α) (steps : Nat) {answer : Bool}
    (h : (M.run steps (M.start (packInput code word))).state = .inr answer) :
    ∃ cost ≤ 2 * steps,
      ((M.pairedInput code).run cost ((M.pairedInput code).start word)).state = .inr answer := by
  obtain ⟨cost, hCost, nextOffset, nextTape, nextState, hSim, hRun⟩ :=
    M.pairedInput_simulates_run code steps false (.inl M.initial)
      ((M.pairedInput code).start word).tape
  rw [M.virtualConfig_start code word] at hRun
  have hAnswer : nextState = .inr answer := (congrArg Config.state hRun).symm.trans h
  refine ⟨cost, hCost, ?_⟩
  have hActual := congrArg Config.state hSim
  rw [hAnswer] at hActual
  exact hActual

theorem pairedInput_haltsWithin (code : α ↪ Bool × Bool) (word : List α) {steps : Nat}
    (h : M.HaltsWithin (packInput code word) steps) :
    (M.pairedInput code).HaltsWithin word (2 * steps) := by
  obtain ⟨t, ht, b, hb⟩ := h
  obtain ⟨cost, hCost, hAnswer⟩ := M.pairedInput_haltsAt code word t hb
  exact ⟨cost, hCost.trans (Nat.mul_le_mul_left 2 ht), b, hAnswer⟩

theorem pairedInput_accepts_iff (code : α ↪ Bool × Bool) (word : List α) {steps : Nat}
    (h : M.HaltsWithin (packInput code word) steps) :
    (M.pairedInput code).Accepts word ↔ M.Accepts (packInput code word) := by
  obtain ⟨t, _, b, hb⟩ := h
  obtain ⟨cost, _, hCost⟩ := M.pairedInput_haltsAt code word t hb
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨t, ((M.pairedInput code).halt_result_unique _ hCost hu) ▸ hb⟩
  · rintro ⟨u, hu⟩
    exact ⟨cost, (M.halt_result_unique _ hb hu) ▸ hCost⟩

theorem pairedInput_polyTime (code : α ↪ Bool × Bool) (h : M.PolyTime) :
    (M.pairedInput code).PolyTime := by
  obtain ⟨k, hTime⟩ := h
  have hTwice := (PolynomiallyBounded.const 2).mul PolynomiallyBounded.id
  have hBound := (PolynomiallyBounded.const 2).mul
    ((hTwice.pow k).add (PolynomiallyBounded.const k))
  refine ((M.pairedInput code).polyTime_iff_polynomiallyBounded).mpr ⟨_, hBound, fun word ↦ ?_⟩
  have hWord := M.pairedInput_haltsWithin code word (hTime (packInput code word))
  rwa [length_packInput] at hWord

end PvsNP.Machine
