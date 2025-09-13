import Mathlib

/-! Quantum scaffold: path weight and basic predicates. -/

namespace IndisputableMonolith
namespace Quantum

structure Path (α : Type) where
  steps : List α

@[simp] def weight {α} (W : Path α → ℝ) (γ : Path α) : ℝ := W γ

@[simp] def born_rule (p : ℝ) : Prop := 0 ≤ p ∧ p ≤ 1

end Quantum
end IndisputableMonolith
