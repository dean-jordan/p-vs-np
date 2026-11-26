module

public import PvsNP.TuringMachine.Registers.OutputRuns

/-! # Linking a fixed list of register fragments -/

@[expose] public section

namespace PvsNP.RegisterMachine.Fragment

variable {R : Type}

/-- Link fragments in their chronological order. -/
def sequence : List (Fragment R) → Fragment R
  | [] => skip
  | f :: fs => f.seq (sequence fs)

variable [DecidableEq R]

/-- A sequence of fragments preserving the valuation emits their output fold.
The number of instructions is bounded by the number of fragments times the
uniform cost of one fragment. -/
theorem runsOutput_sequence {α : Type} (keys : List α) (body : α → Fragment R)
    (update : BinaryWord → α → BinaryWord) (x : BinaryWord) (v : R → Nat) (bound : Nat)
    (hBody : ∀ key ∈ keys, ∀ suffix, ∃ cost ≤ bound,
      (body key).RunsOutput x cost v v suffix (update suffix key)) (suffix : BinaryWord) :
    ∃ cost ≤ keys.length * bound,
      (sequence (keys.map body)).RunsOutput x cost v v suffix (keys.foldl update suffix) := by
  induction keys generalizing suffix with
  | nil => exact ⟨0, Nat.zero_le _, runsOutput_skip x v suffix⟩
  | cons key rest ih =>
    obtain ⟨first, hFirst, firstRun⟩ := hBody key (List.mem_cons_self ..) suffix
    obtain ⟨later, hLater, laterRun⟩ := ih
      (fun k hk ↦ hBody k (List.mem_cons_of_mem key hk)) (update suffix key)
    refine ⟨first + later, ?_, firstRun.seq laterRun⟩
    simpa only [List.length_cons, Nat.succ_mul, Nat.add_comm] using Nat.add_le_add hFirst hLater

end PvsNP.RegisterMachine.Fragment
