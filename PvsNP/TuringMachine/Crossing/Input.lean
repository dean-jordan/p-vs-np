module

public import PvsNP.TuringMachine.Crossing.Absolute

/-! # Splicing initial Cook input tapes at a common cut -/

public section

namespace PvsNP.Machine

variable {α : Type} (M : Machine α)

/-- Prefixes of the same length place both suffixes at the same coordinate. -/
theorem spliceConfig_absoluteStart_append (a a' b b' : List α)
    (hLength : a.length = a'.length) (hPos : 0 < a.length) :
    M.spliceConfig (a.length : Int) (M.absoluteStart (a ++ b)) (M.absoluteStart (a' ++ b')) =
      M.absoluteStart (a ++ b') := by
  have hOrigin : (0 : Int) < (a.length : Int) := by omega
  have hStart : (M.absoluteStart (a ++ b)).position = 0 := rfl
  simp only [spliceConfig, hStart, ite_eq_left hOrigin]
  change (⟨Sum.inl M.initial, 0,
      fun i ↦ if i < (a.length : Int) then (M.absoluteStart (a ++ b)).tape i
        else (M.absoluteStart (a' ++ b')).tape i⟩ : M.AbsoluteConfig) =
      M.absoluteStart (a ++ b')
  congr 1
  funext i
  change (if i < (a.length : Int) then (M.absoluteStart (a ++ b)).tape i
      else (M.absoluteStart (a' ++ b')).tape i) = (M.absoluteStart (a ++ b')).tape i
  simp only [M.absoluteStart_tape, List.map_append]
  by_cases hLeft : i < (a.length : Int)
  · rw [ite_eq_left hLeft]
    by_cases hNeg : i < 0
    · simp [hNeg]
    · have hIndex : i.toNat < (a.map M.input).length := by rw [List.length_map]; omega
      simp only [ite_eq_right hNeg, List.getElem?_append_left hIndex]
  · have hNeg : ¬ i < 0 := by omega
    have hIndex : (a.map M.input).length ≤ i.toNat := by rw [List.length_map]; omega
    have hMapLength : (a.map M.input).length = (a'.map M.input).length := by
      simpa only [List.length_map] using hLength
    have hIndex' : (a'.map M.input).length ≤ i.toNat := hMapLength ▸ hIndex
    simp only [ite_eq_right hLeft, ite_eq_right hNeg, List.getElem?_append_right hIndex,
      List.getElem?_append_right hIndex', hMapLength]

end PvsNP.Machine
