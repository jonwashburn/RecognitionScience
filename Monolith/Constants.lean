import Mathlib

/-! Monolith constants slice. -/
namespace Monolith
noncomputable section

@[simp] def phi : ℝ := (1 + Real.sqrt 5) / 2

@[simp] theorem phi_pos : 0 < phi := by
  unfold phi
  have h5 : (0:ℝ) < 5 := by norm_num
  have hs : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr h5
  have hnum : 0 < 1 + Real.sqrt 5 := by
    have hs0 : 0 ≤ Real.sqrt 5 := le_of_lt hs
    have h1 : 0 < (1:ℝ) := by norm_num
    exact add_pos_of_pos_of_nonneg h1 hs0
  have hden : 0 < (2:ℝ) := by norm_num
  exact (div_pos hnum hden)

@[simp] def constsReport : String := "Constants: phi defined and positive."

end
end Monolith


@[simp] theorem phi_gt_half : (1:ℝ)/2 < phi := by
  unfold phi
  have hs : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have h1 : (1:ℝ) < 1 + Real.sqrt 5 := by
    have := (add_lt_add_left hs 1)
    simpa [one_mul, one_add] using this
  have hden : 0 < (2:ℝ) := by norm_num
  exact (div_lt_div_right hden).mpr h1
