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
  exact (div_pos hnum hden)

@[simp] def constsReport : String := "Constants: phi defined and positive."

end
end Monolith


@[simp] theorem phi_sq_eq_phi_add_one : phi ^ 2 = phi + 1 := by
  unfold phi
  -- Let s = √5 for brevity
  set s : ℝ := Real.sqrt 5
  have hsq : s ^ 2 = (5:ℝ) := by
    have : 0 ≤ (5:ℝ) := by norm_num
    simpa [pow_two, s] using Real.mul_self_sqrt this
  have h4ne : (4:ℝ) ≠ 0 := by norm_num
  -- Multiply both sides by 4 and compare numerators
  -- Left after multiplying by 4
  have hL : 4 * (((1 + s) / 2) ^ 2) = (1 + s) ^ 2 := by
    have hdivpow : (((1 + s) / 2) ^ 2) = ((1 + s) ^ 2) / (2 ^ 2) := by
      simpa using div_pow (1 + s) (2:ℝ) (2:ℕ)
    -- 4 * ((1+s)^2 / 4) = (1+s)^2
    have hAssoc : 4 * (((1 + s) ^ 2) / 4) = (4 * ((1 + s) ^ 2)) / 4 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (mul_div_assoc (4:ℝ) ((1 + s) ^ 2) (4:ℝ))
    have hCancel : (4 * ((1 + s) ^ 2)) / 4 = (1 + s) ^ 2 := by
      simpa using (mul_div_cancel' ((1 + s) ^ 2) h4ne)
    simpa [hdivpow, pow_two, hAssoc, hCancel]
  -- Right after multiplying by 4
  have hR : 4 * (((1 + s) / 2) + 1) = 2 * (3 + s) := by
    -- 4 * ((1+s)/2 + 1) = 4 * ((3+s)/2) = 2 * (3+s)
    have : ((1 + s) / 2) + 1 = (3 + s) / 2 := by
      -- multiply both sides by 2 to avoid fractions
      apply (mul_right_cancel₀ (by norm_num : (2:ℝ) ≠ 0)).mp
      have : 2 * (((1 + s) / 2) + 1) = 2 * ((3 + s) / 2) := by
        ring_nf
      simpa [two_mul, add_comm, add_left_comm, add_assoc] using this
    -- now finish
    calc
      4 * (((1 + s) / 2) + 1)
          = 4 * ((3 + s) / 2) := by simpa [this]
      _ = (4 / 2) * (3 + s) := by ring
      _ = 2 * (3 + s) := by norm_num
  -- Expand (1+s)^2 and use s^2 = 5
  have hPoly : (1 + s) ^ 2 = 6 + 2 * s := by
    have : (1 + s) ^ 2 = 1 + 2 * s + s ^ 2 := by ring
    simpa [this, hsq] 
  -- Compare both numerators
  have hNumEq : (1 + s) ^ 2 = 2 * (3 + s) := by
    simpa [hPoly, two_mul, add_comm, add_left_comm, add_assoc, mul_add] using rfl
  -- Conclude by canceling 4
  apply (mul_right_cancel₀ h4ne).mpr
  simpa [hL, hR]
