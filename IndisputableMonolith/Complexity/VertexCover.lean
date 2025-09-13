import Mathlib

/-! Vertex Cover toy problem scaffold. -/

namespace IndisputableMonolith
namespace Complexity
namespace VertexCover

/-- Vertex Cover instance over `Nat` vertices. -/
structure Instance where
  vertices : List Nat
  edges    : List (Nat × Nat)
  k        : Nat
deriving Repr

/-- A set `S` covers a vertex `v` if `v ∈ S`. -/
def InCover (S : List Nat) (v : Nat) : Prop := v ∈ S

def EdgeCovered (S : List Nat) (e : Nat × Nat) : Prop :=
  InCover S e.fst ∨ InCover S e.snd

/-- `S` covers all edges of instance `I`. -/
def Covers (S : List Nat) (I : Instance) : Prop :=
  ∀ e, e ∈ I.edges → EdgeCovered S e

/-- There exists a vertex cover of size ≤ k. -/
def HasCover (I : Instance) : Prop :=
  ∃ S : List Nat, S.length ≤ I.k ∧ Covers S I

/-- A trivial example with no edges is always covered by the empty set. -/
def example : Instance := { vertices := [1], edges := [], k := 0 }

lemma example_hasCover : HasCover example := by
  refine ⟨[], by decide, ?_⟩
  intro e he
  cases he

end VertexCover
end Complexity
end IndisputableMonolith


