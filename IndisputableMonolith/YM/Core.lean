import Mathlib

/-! Yang–Mills core scaffold. -/

namespace IndisputableMonolith
namespace YM

structure GaugeField where
  a : Nat → Nat → ℝ

@[simp] def action (F : GaugeField) : ℝ := 0

end YM
end IndisputableMonolith


