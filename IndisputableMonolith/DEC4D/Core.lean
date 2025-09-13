import Mathlib

/-! 4D Discrete Exterior Calculus scaffold. -/

namespace IndisputableMonolith
namespace DEC4D

structure Lattice where
  nx ny nz nt : Nat

@[simp] def cells (G : Lattice) : Nat := G.nx * G.ny * G.nz * G.nt

end DEC4D
end IndisputableMonolith


