import Mathlib

/-! Information-Limited Gravity (ILG) scaffold. -/

namespace IndisputableMonolith
namespace Gravity
namespace ILG

structure Kernel where
  weight : Nat → Nat → ℝ

@[simp] def defaultKernel : Kernel := { weight := fun _ _ => 1 }

end ILG
end Gravity
end IndisputableMonolith


