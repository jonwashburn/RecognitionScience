import Mathlib
import IndisputableMonolith.Constants

/-! Recognition: φ powers (skeleton). -/

namespace IndisputableMonolith
namespace Recognition

@[simp] def PhiPow (n : ℤ) : ℝ := (Constants.phi) ^ Int.toNat (Int.natAbs n)

@[simp] theorem PhiPow_one : PhiPow 1 = Constants.phi := by
  simp [PhiPow]

end Recognition
end IndisputableMonolith


