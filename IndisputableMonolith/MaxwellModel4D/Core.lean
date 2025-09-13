import Mathlib

/-! Maxwell model 4D scaffold. -/

namespace IndisputableMonolith
namespace MaxwellModel4D

structure Params where
  eps mu : ℝ

@[simp] def energy (p : Params) : ℝ := p.eps + p.mu

end MaxwellModel4D
end IndisputableMonolith


