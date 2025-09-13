import Mathlib

/-! Constants and simple unit structure (trimmed for green build). -/

namespace IndisputableMonolith
namespace Constants
noncomputable section

/-- Golden ratio. -/
@[simp] def phi : ℝ := (1 + Real.sqrt 5) / 2

@[simp] theorem phi_pos : 0 < phi := by
  unfold phi
  have hs : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hnum : 0 < (1 : ℝ) + Real.sqrt 5 := by
    have h1 : 0 < (1 : ℝ) := by norm_num
    exact add_pos_of_pos_of_nonneg h1 (le_of_lt hs)
  have hden : 0 < (2 : ℝ) := by norm_num
  exact div_pos hnum hden

@[simp] theorem phi_ne_zero : phi ≠ 0 := ne_of_gt phi_pos

/-! Units skeleton. -/
namespace RSUnits

noncomputable section

structure RSUnits where
  tau0 : ℝ
  ell0 : ℝ
  Ecoh : ℝ

/-- Speed `c` derived from unit ratio. -/
@[simp] def c (U : RSUnits) : ℝ := U.ell0 / U.tau0

@[simp] def hbar (_U : RSUnits) : ℝ := 1

@[simp] theorem ell0_div_tau0_eq_c (U : RSUnits) : U.ell0 / U.tau0 = U.c := rfl

end

end RSUnits

end

end Constants
end IndisputableMonolith
