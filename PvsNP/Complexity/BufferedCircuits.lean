module

public import PvsNP.Circuits.LengthSelection
public import PvsNP.Complexity.CircuitLowerBound

/-! # Polynomial-size circuits on bounded-length words -/

public section

namespace PvsNP

open Circuits

private def fullBufferLayer (n : Nat) : Layer n (n + n) :=
  bufferByHalves (fun i ↦ .input i) (fun _ ↦ .const true)

private theorem fullBufferLayer_eval (n : Nat) (x : Fin n → Bool) :
    (fullBufferLayer n).eval x = wordBuffer n (List.ofFn x) := by
  apply buffer_ext
  · intro i
    simp [Layer.eval, fullBufferLayer, Expr.eval, i.isLt]
  · intro i
    simp only [Layer.eval, fullBufferLayer, bufferByHalves_present, Expr.eval,
      wordBuffer_present, List.length_ofFn]
    simp [i.isLt]

private theorem fullBufferLayer_size_le (n : Nat) : (fullBufferLayer n).size ≤ n + n := by
  calc
    _ ≤ (n + n) * 1 := Layer.size_le_of_forall _ _ fun j ↦ by
      simp only [fullBufferLayer, bufferByHalves]
      split <;> exact Nat.le_refl 1
    _ = n + n := Nat.mul_one _

/-- Fixed-length circuit families and bounded-length buffered families define the same class. -/
theorem mem_PPoly_iff_bufferCircuits {L : BinaryLanguage} :
    L ∈ PPoly ↔
      ∃ circuit : (B : Nat) → BooleanCircuit (B + B),
        PolynomiallyBounded (fun B ↦ (circuit B).size) ∧
        ∀ B (word : BinaryWord), word.length ≤ B →
          ((circuit B).eval (wordBuffer B word) = true ↔ word ∈ L) := by
  constructor
  · rintro ⟨family, ⟨C, d, hSize⟩, hCorrect⟩
    refine ⟨selectLength family, ?_, ?_⟩
    · let hLinear := PolynomiallyBounded.id.add (PolynomiallyBounded.const 1)
      have hUniform : PolynomiallyBounded (fun B ↦ C * (B + 1) ^ d) :=
        (PolynomiallyBounded.const C).mul (hLinear.pow d)
      refine ((hLinear.mul (hUniform.add (PolynomiallyBounded.const 5))).add
        (PolynomiallyBounded.const 1)).mono ?_
      intro B
      apply selectLength_size_le
      intro n hLen
      exact (hSize n).trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (Nat.succ_le_succ hLen) d))
    · intro B word hLen
      rw [selectLength_eval family B word hLen]
      simpa only [List.ofFn_getElem] using hCorrect word.length (fun i ↦ word[i.val])
  · rintro ⟨family, hSize, hCorrect⟩
    let pad (n : Nat) : Layered n (n + n) := .cons (fullBufferLayer n) (.id (n + n))
    let circuit (n : Nat) := (pad n).toMultiCircuit.thenBoolean (family n)
    refine ⟨circuit, ?_, ?_⟩
    · refine ((PolynomiallyBounded.id.add PolynomiallyBounded.id).add hSize).mono ?_
      intro n
      change ((pad n).toMultiCircuit.thenBoolean (family n)).size ≤ _
      rw [MultiCircuit.size_thenBoolean]
      have hPad := Layered.size_toMultiCircuit_le (pad n)
      simp only [pad, Layered.size, Nat.add_zero] at hPad
      exact Nat.add_le_add_right (hPad.trans (fullBufferLayer_size_le n)) _
    · intro n x
      have hLen : (List.ofFn x).length ≤ n := by simp
      change ((pad n).toMultiCircuit.thenBoolean (family n)).eval x = true ↔ _
      rw [MultiCircuit.eval_thenBoolean, Layered.eval_toMultiCircuit]
      change (family n).eval ((fullBufferLayer n).eval x) = true ↔ List.ofFn x ∈ L
      rw [fullBufferLayer_eval]
      exact hCorrect n (List.ofFn x) hLen

end PvsNP
