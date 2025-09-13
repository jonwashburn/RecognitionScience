import Mathlib
import IndisputableMonolith.Complexity.VertexCover

/-! RS-to-VertexCover reduction scaffold. -/

namespace IndisputableMonolith
namespace Complexity
namespace RSVC

structure ConstraintInstance where
  vertices    : List Nat
  constraints : List (Nat × Nat)
  k           : Nat
deriving Repr

@[simp] def toVC (A : ConstraintInstance) : VertexCover.Instance :=
{ vertices := A.vertices, edges := A.constraints, k := A.k }

def Recognizes (A : ConstraintInstance) : Prop :=
  VertexCover.HasCover (toVC A)

@[simp] def reduceRS2VC : ConstraintInstance → VertexCover.Instance := toVC

@[simp] theorem reduce_correct (A : ConstraintInstance) :
  Recognizes A ↔ VertexCover.HasCover (reduceRS2VC A) := Iff.rfl

structure RSPreserving (A B : Type) where
  sizeA  : A → Nat
  sizeB  : B → Nat
  reduce : A → B

@[simp] def rs_preserving_RS2VC : RSPreserving ConstraintInstance VertexCover.Instance :=
{ sizeA := fun a => a.vertices.length + a.constraints.length
, sizeB := fun b => b.vertices.length + b.edges.length
, reduce := reduceRS2VC }

end RSVC
end Complexity
end IndisputableMonolith
