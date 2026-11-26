module

public import PvsNP.Complexity.PairEncoding

/-! # Fixed-width binary buffers with exact length information -/

@[expose] public section

namespace PvsNP.Circuits

/-- The first `B` wires carry data and the next `B` wires mark present positions. -/
def bufferByHalves {α : Type} {B : Nat} (data present : Fin B → α) (i : Fin (B + B)) : α :=
  if h : i.val < B then data ⟨i.val, h⟩ else present ⟨i.val - B, by omega⟩

@[simp] theorem bufferByHalves_data {α : Type} {B : Nat} (data present : Fin B → α)
    (i : Fin B) : bufferByHalves data present (Fin.castAdd B i) = data i := by
  simp [bufferByHalves, i.isLt]

@[simp] theorem bufferByHalves_present {α : Type} {B : Nat} (data present : Fin B → α)
    (i : Fin B) : bufferByHalves data present (Fin.natAdd B i) = present i := by
  have h : ¬ i.val + B < B := by omega
  simp [bufferByHalves, h]

/-- A word's data bits are padded with false. Presence is true exactly before its end. -/
def wordBuffer (B : Nat) (word : BinaryWord) : Fin (B + B) → Bool :=
  bufferByHalves (fun i ↦ word[i.val]?.getD false) (fun i ↦ decide (i.val < word.length))

@[simp] theorem wordBuffer_data (B : Nat) (word : BinaryWord) (i : Fin B) :
    wordBuffer B word (Fin.castAdd B i) = word[i.val]?.getD false := by
  simp only [wordBuffer, bufferByHalves_data]

@[simp] theorem wordBuffer_present (B : Nat) (word : BinaryWord) (i : Fin B) :
    wordBuffer B word (Fin.natAdd B i) = decide (i.val < word.length) := by
  simp only [wordBuffer, bufferByHalves_present]

/-- Equality on both halves determines the entire buffer. -/
theorem buffer_ext {α : Type} {B : Nat} {f g : Fin (B + B) → α}
    (hData : ∀ i : Fin B, f (Fin.castAdd B i) = g (Fin.castAdd B i))
    (hPresent : ∀ i : Fin B, f (Fin.natAdd B i) = g (Fin.natAdd B i)) : f = g := by
  funext i
  by_cases h : i.val < B
  · exact hData ⟨i.val, h⟩
  · have hi : i.val - B < B := by omega
    have eq : Fin.natAdd B (⟨i.val - B, hi⟩ : Fin B) = i := by
      apply Fin.ext
      change B + (i.val - B) = i.val
      omega
    simpa only [eq] using hPresent ⟨i.val - B, hi⟩

end PvsNP.Circuits
