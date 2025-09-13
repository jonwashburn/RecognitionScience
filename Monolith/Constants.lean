import Mathlib

/-! Monolith constants slice. -/
namespace Monolith
noncomputable section

@[simp] def phi : ℝ := (1 + Real.sqrt 5) / 2

@[simp] theorem phi_pos : 0 < phi := by
  unfold phi
  have h5 : (0:ℝ) < 5 := by norm_num
  have hs : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr h5
  have hnum : 0 < 1 + Real.sqrt 5 := by have : (0:ℝ) < 1 := by norm_num; linarith
  have hden : 0 < (2:ℝ) := by norm_num
  exact (div_pos_iff.mpr ⟨hnum, hden⟩)

@[simp] def constsReport : String := "Constants: phi defined and positive."

end
end Monolith
