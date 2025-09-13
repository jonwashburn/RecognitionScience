import Mathlib
import IndisputableMonolith.Ledger

/-! Parity patterns and eight-tick existence/minimality (T6/T7). -/

namespace IndisputableMonolith

@[simp] def Pattern (d : Nat) := (Fin d → Bool)

instance instFintypePattern (d : Nat) : Fintype (Pattern d) := by
  classical
  dsimp [Pattern]
  infer_instance

lemma card_pattern (d : Nat) : Fintype.card (Pattern d) = 2 ^ d := by
  classical
  simpa [Pattern, Fintype.card_fin] using
    (Fintype.card_fun : Fintype.card (Fin d → Bool) = (Fintype.card Bool) ^ (Fintype.card (Fin d)))

lemma no_surj_small (T d : Nat) (hT : T < 2 ^ d) :
  ¬ ∃ f : Fin T → Pattern d, Surjective f := by
  classical
  intro h; rcases h with ⟨f, hf⟩
  obtain ⟨g, hg⟩ := hf.hasRightInverse
  have hginj : Injective g := by
    intro y₁ y₂ hgy
    have : f (g y₁) = f (g y₂) := by simp [hgy]
    simpa [RightInverse, hg y₁, hg y₂] using this
  have hcard : Fintype.card (Pattern d) ≤ Fintype.card (Fin T) :=
    Fintype.card_le_of_injective _ hginj
  have : 2 ^ d ≤ T := by simp [Fintype.card_fin, card_pattern d] at hcard; simpa [Fintype.card_fin, card_pattern d] using hcard
  exact (lt_of_le_of_lt this hT).false

lemma min_ticks_cover {d T : Nat}
  (pass : Fin T → Pattern d) (covers : Surjective pass) : 2 ^ d ≤ T := by
  classical
  by_contra h
  exact (no_surj_small T d (lt_of_not_ge h)) ⟨pass, covers⟩

lemma eight_tick_min {T : Nat}
  (pass : Fin T → Pattern 3) (covers : Surjective pass) : 8 ≤ T := by
  simpa using (min_ticks_cover (d := 3) (T := T) pass covers)

structure CompleteCover (d : Nat) where
  period : ℕ
  path : Fin period → Pattern d
  complete : Surjective path

theorem cover_exact_pow (d : Nat) : ∃ w : CompleteCover d, w.period = 2 ^ d := by
  classical
  let e := (Fintype.equivFin (Pattern d)).symm
  refine ⟨{ period := Fintype.card (Pattern d)
          , path := fun i => e i
          , complete := (Fintype.equivFin (Pattern d)).symm.surjective }, ?_⟩
  simpa [card_pattern d]

theorem period_exactly_8 : ∃ w : CompleteCover 3, w.period = 8 := by
  simpa using cover_exact_pow 3

end IndisputableMonolith
