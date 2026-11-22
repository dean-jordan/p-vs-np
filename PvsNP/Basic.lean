module

public import Mathlib.Data.Finset.Card

/-! # Finite input sets -/

namespace PvsNP

/-- The finite set of natural numbers less than `n` has `n` elements. -/
public theorem card_inputs_below (n : ℕ) : (Finset.range n).card = n := by
  simp

end PvsNP
