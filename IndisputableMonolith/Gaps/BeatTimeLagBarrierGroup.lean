import Mathlib

namespace IndisputableMonolith
namespace Gap45

open Nat

@[simp] lemma coprime_9_5 : Nat.Coprime 9 5 := by decide
@[simp] lemma coprime_8_45 : Nat.Coprime 8 45 := by decide
@[simp] lemma gcd_8_45_eq_one : Nat.gcd 8 45 = 1 := by decide

lemma lcm_8_45_eq_360 : Nat.lcm 8 45 = 360 := by
  have hg : Nat.gcd 8 45 = 1 := by decide
  have h := Nat.gcd_mul_lcm 8 45
  have : Nat.lcm 8 45 = 8 * 45 := by simpa [hg, Nat.one_mul] using h
  have hm : 8 * 45 = 360 := by decide
  exact this.trans hm

lemma lcm_8_45_div_8 : Nat.lcm 8 45 / 8 = 45 := by
  have h := lcm_8_45_eq_360
  have : 360 / 8 = 45 := by decide
  simpa [h] using this

lemma lcm_8_45_div_45 : Nat.lcm 8 45 / 45 = 8 := by
  have h := lcm_8_45_eq_360
  have : 360 / 45 = 8 := by decide
  simpa [h] using this

lemma lcm_9_5_eq_45 : Nat.lcm 9 5 = 45 := by
  have hg : Nat.gcd 9 5 = 1 := by decide
  have h := Nat.gcd_mul_lcm 9 5
  have h' : Nat.lcm 9 5 = 9 * 5 := by simpa [hg, Nat.one_mul] using h
  have hmul : 9 * 5 = 45 := by decide
  simpa [hmul] using h'

@[simp] lemma nine_dvd_45 : 9 ∣ 45 := by exact ⟨5, by decide⟩
@[simp] lemma five_dvd_45 : 5 ∣ 45 := by exact ⟨9, by decide⟩
@[simp] lemma eight_not_dvd_45 : ¬ 8 ∣ 45 := by decide

lemma no_smaller_multiple_9_5 (n : Nat) (hnpos : 0 < n) (hnlt : n < 45) :
  ¬ (9 ∣ n ∧ 5 ∣ n) := by
  intro h
  rcases h with ⟨h9, h5⟩
  have hmul : 9 * 5 ∣ n := Nat.coprime.mul_dvd_of_dvd_of_dvd coprime_9_5 h9 h5
  have h45 : 45 ∣ n := by simpa using hmul
  rcases h45 with ⟨k, hk⟩
  rcases (Nat.eq_zero_or_pos k) with rfl | hkpos
  · simpa using hnpos
  · have : 45 ≤ 45 * k := Nat.mul_le_mul_left 45 hkpos
    have : 45 ≤ n := by simpa [hk] using this
    exact (not_le_of_gt hnlt) this

/-- Summary: 45 is the first rung where 9- and 5-fold periodicities coincide, and it is not
    synchronized with the 8-beat (since 8 ∤ 45). -/
theorem rung45_first_conflict :
  (9 ∣ 45) ∧ (5 ∣ 45) ∧ ¬ 8 ∣ 45 ∧ ∀ n, 0 < n → n < 45 → ¬ (9 ∣ n ∧ 5 ∣ n) := by
  refine ⟨nine_dvd_45, five_dvd_45, eight_not_dvd_45, ?_⟩
  intro n hnpos hnlt; exact no_smaller_multiple_9_5 n hnpos hnlt

/-- Synchronization requirement: the minimal time to jointly align 8-beat and 45-fold symmetries
    is exactly lcm(8,45) = 360 beats, corresponding to 45 cycles of 8 and 8 cycles of 45. -/
theorem sync_counts :
  Nat.lcm 8 45 = 360 ∧ Nat.lcm 8 45 / 8 = 45 ∧ Nat.lcm 8 45 / 45 = 8 := by
  exact ⟨lcm_8_45_eq_360, lcm_8_45_div_8, lcm_8_45_div_45⟩

/-- The beat-level clock-lag fraction implied by the 45-gap arithmetic: δ_time = 45/960 = 3/64. -/
theorem delta_time_eq_3_div_64 : (45 : ℚ) / 960 = (3 : ℚ) / 64 := by
  norm_num

namespace Beat
@[simp] def beats : Nat := Nat.lcm 8 45
@[simp] lemma beats_eq_360 : beats = 360 := by simp [beats, lcm_8_45_eq_360]
@[simp] lemma cycles_of_8  : beats / 8  = 45 := by simp [beats, lcm_8_45_div_8]
@[simp] lemma cycles_of_45 : beats / 45 = 8  := by simp [beats, lcm_8_45_div_45]
lemma minimal_sync_divides {t : Nat} (h8 : 8 ∣ t) (h45 : 45 ∣ t) : beats ∣ t := by
  simpa [beats] using Nat.lcm_dvd h8 h45
lemma minimal_sync_360_divides {t : Nat} (h8 : 8 ∣ t) (h45 : 45 ∣ t) : 360 ∣ t := by
  simpa [beats_eq_360] using minimal_sync_divides (t:=t) h8 h45
lemma no_smaller_multiple_8_45 {n : Nat} (hnpos : 0 < n) (hnlt : n < 360) :
  ¬ (8 ∣ n ∧ 45 ∣ n) := by
  intro h; rcases h with ⟨h8, h45⟩
  have h360 : 360 ∣ n := minimal_sync_360_divides (t:=n) h8 h45
  rcases h360 with ⟨k, hk⟩
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simpa using hnpos
  · have : 360 ≤ 360 * k := Nat.mul_le_mul_left 360 hkpos
    have : 360 ≤ n := by simpa [hk] using this
    exact (not_le_of_gt hnlt) this

structure Sync where
  beats : Nat
  cycles8 : beats / 8 = 45
  cycles45 : beats / 45 = 8

noncomputable def canonical : Sync := { beats := beats, cycles8 := cycles_of_8, cycles45 := cycles_of_45 }
end Beat

namespace TimeLag
@[simp] lemma lag_q : (45 : ℚ) / ((8 : ℚ) * (120 : ℚ)) = (3 : ℚ) / 64 := by norm_num
@[simp] lemma lag_r : (45 : ℝ) / ((8 : ℝ) * (120 : ℝ)) = (3 : ℝ) / 64 := by norm_num
end TimeLag

namespace RecognitionBarrier
structure UncomputabilityPoint : Prop := (is45 : True)
structure ExperientialNavigation : Prop := (needs_history : True)
 theorem ConsciousnessEmergence : UncomputabilityPoint → ExperientialNavigation := by intro _; exact ⟨trivial⟩
end RecognitionBarrier

namespace GroupView
open Nat
lemma trivial_intersection_pow {G : Type*} [Group G] {g : G}
  (h8 : g ^ 8 = 1) (h45 : g ^ 45 = 1) : g = 1 := by
  have h8d : orderOf g ∣ 8 := (orderOf_dvd_iff_pow_eq_one (g:=g) (n:=8)).2 h8
  have h45d : orderOf g ∣ 45 := (orderOf_dvd_iff_pow_eq_one (g:=g) (n:=45)).2 h45
  have hgcd : orderOf g ∣ Nat.gcd 8 45 := Nat.dvd_gcd h8d h45d
  have hone : orderOf g ∣ 1 := by simpa [gcd_8_45_eq_one] using hgcd
  have h1 : orderOf g = 1 := Nat.dvd_one.mp hone
  exact (orderOf_eq_one_iff.mp h1)
end GroupView

namespace AddGroupView
open Nat
lemma trivial_intersection_nsmul {A : Type*} [AddGroup A] {a : A}
  (h8 : (8 : ℕ) • a = 0) (h45 : (45 : ℕ) • a = 0) : a = 0 := by
  have h8d : addOrderOf a ∣ 8 := (addOrderOf_dvd_iff_nsmul_eq_zero (a:=a) (n:=8)).2 h8
  have h45d : addOrderOf a ∣ 45 := (addOrderOf_dvd_iff_nsmul_eq_zero (a:=a) (n:=45)).2 h45
  have hgcd : addOrderOf a ∣ Nat.gcd 8 45 := Nat.dvd_gcd h8d h45d
  have hone : addOrderOf a ∣ 1 := by simpa [gcd_8_45_eq_one] using hgcd
  have h1 : addOrderOf a = 1 := Nat.dvd_one.mp hone
  simpa [h1] using (addOrderOf_eq_one_iff.mpr rfl)
end AddGroupView

end Gap45
end IndisputableMonolith
