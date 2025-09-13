import Mathlib

/-! Core: minimal MP and chain definitions extracted from the monolith. -/

namespace IndisputableMonolith

abbrev Nothing := Empty

structure Recognition (A : Type) (B : Type) : Type where
  recognizer : A
  recognized : B

def MP : Prop := ¬ ∃ _ : Recognition Nothing Nothing, True

/-- T1 (MP): Nothing cannot recognize itself. -/
theorem mp_holds : MP := by
  intro ⟨⟨r, _⟩, _⟩; cases r

structure RecognitionStructure where
  U : Type
  R : U → U → Prop

structure Chain (M : RecognitionStructure) where
  n : Nat
  f : Fin (n+1) → M.U
  ok : ∀ i : Fin n, M.R (f i.castSucc) (f i.succ)

namespace Chain
variable {M : RecognitionStructure} (ch : Chain M)

def head : M.U := by
  have hpos : 0 < ch.n + 1 := Nat.succ_pos _
  exact ch.f ⟨0, hpos⟩

def last : M.U := by
  have hlt : ch.n < ch.n + 1 := Nat.lt_succ_self _
  exact ch.f ⟨ch.n, hlt⟩

end Chain

end IndisputableMonolith


