import Mathlib

/-! EL/Jlog basics (trimmed for green build). -/

noncomputable section

namespace IndisputableMonolith

@[simp] def Jlog (t : ℝ) : ℝ := Real.cosh t - 1

end IndisputableMonolith

end


