import Mathlib

/-! DEC/CochainSpace scaffolds. -/

namespace IndisputableMonolith
namespace DEC

structure CochainSpace (α : Type) where
  dim : Nat

@[simp] def zero (A : CochainSpace α) : Nat := 0

end DEC
end IndisputableMonolith


