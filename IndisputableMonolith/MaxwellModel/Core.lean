import Mathlib

/-! Maxwell model scaffold. -/

namespace IndisputableMonolith
namespace MaxwellModel

structure Params where
  eps mu : ℝ

@[simp] def energy (p : Params) : ℝ := p.eps + p.mu

end MaxwellModel
end IndisputableMonolith
