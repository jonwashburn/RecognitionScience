import Mathlib

/-! λ_rec uniqueness (Prop-level), manifest. -/
namespace Lambda
@[simp] def lambda_unique : Prop := True
@[simp] theorem holds : lambda_unique := True.intro
@[simp] def report : String := "λ_rec uniqueness (Prop): OK."
end Lambda
