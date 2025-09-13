import Mathlib
import IndisputableMonolith.LedgerUnits
import IndisputableMonolith.Constants

/-! Affine mappings from δ-ledger to physical contexts (charge, time, action). -/

namespace IndisputableMonolith
namespace UnitMapping

open LedgerUnits

structure AffineMapZ where
  slope : ℝ
  offset : ℝ

@[simp] def apply (f : AffineMapZ) (n : ℤ) : ℝ := f.slope * (n : ℝ) + f.offset

noncomputable def mapDelta (δ : ℤ) (hδ : δ ≠ 0) (f : AffineMapZ) : DeltaSub δ → ℝ :=
  fun p => f.slope * ((toZ δ p) : ℝ) + f.offset

lemma mapDelta_diff (δ : ℤ) (hδ : δ ≠ 0) (f : AffineMapZ)
  (p q : DeltaSub δ) :
  mapDelta δ hδ f p - mapDelta δ hδ f q = f.slope * (((toZ δ p) : ℤ) - (toZ δ q)) := by
  classical
  simp [mapDelta, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg]

def chargeMap (qe : ℝ) : AffineMapZ := { slope := qe, offset := 0 }
def timeMap (U : IndisputableMonolith.Constants.RSUnits.RSUnits) : AffineMapZ := { slope := U.tau0, offset := 0 }
def actionMap (U : IndisputableMonolith.Constants.RSUnits.RSUnits) : AffineMapZ := { slope := IndisputableMonolith.Constants.RSUnits.hbar U, offset := 0 }

noncomputable def mapDeltaCharge (δ : ℤ) (hδ : δ ≠ 0) (qe : ℝ) : DeltaSub δ → ℝ :=
  mapDelta δ hδ (chargeMap qe)

noncomputable def mapDeltaTime (δ : ℤ) (hδ : δ ≠ 0) (U : IndisputableMonolith.Constants.RSUnits.RSUnits) : DeltaSub δ → ℝ :=
  mapDelta δ hδ (timeMap U)

noncomputable def mapDeltaAction (δ : ℤ) (hδ : δ ≠ 0) (U : IndisputableMonolith.Constants.RSUnits.RSUnits) : DeltaSub δ → ℝ :=
  mapDelta δ hδ (actionMap U)

@[simp] lemma mapDelta_fromZ (δ : ℤ) (hδ : δ ≠ 0) (f : AffineMapZ) (n : ℤ) :
  mapDelta δ hδ f (fromZ δ n) = f.slope * (n : ℝ) + f.offset := by
  classical
  simp [mapDelta, toZ_fromZ δ hδ]

lemma mapDelta_step (δ : ℤ) (hδ : δ ≠ 0) (f : AffineMapZ) (n : ℤ) :
  mapDelta δ hδ f (fromZ δ (n+1)) - mapDelta δ hδ f (fromZ δ n) = f.slope := by
  classical
  simp [mapDelta_fromZ (δ:=δ) (hδ:=hδ) (f:=f), add_comm, add_left_comm, add_assoc, sub_eq_add_neg, mul_add, add_comm]

@[simp] lemma mapDeltaTime_fromZ (δ : ℤ) (hδ : δ ≠ 0)
  (U : IndisputableMonolith.Constants.RSUnits.RSUnits) (n : ℤ) :
  mapDeltaTime δ hδ U (fromZ δ n) = U.tau0 * (n : ℝ) := by
  simp [mapDeltaTime, timeMap]

lemma mapDeltaTime_step (δ : ℤ) (hδ : δ ≠ 0)
  (U : IndisputableMonolith.Constants.RSUnits.RSUnits) (n : ℤ) :
  mapDeltaTime δ hδ U (fromZ δ (n+1)) - mapDeltaTime δ hδ U (fromZ δ n) = U.tau0 := by
  simpa [mapDeltaTime, timeMap]

@[simp] lemma mapDeltaAction_fromZ (δ : ℤ) (hδ : δ ≠ 0)
  (U : IndisputableMonolith.Constants.RSUnits.RSUnits) (n : ℤ) :
  mapDeltaAction δ hδ U (fromZ δ n) = (IndisputableMonolith.Constants.RSUnits.hbar U) * (n : ℝ) := by
  simp [mapDeltaAction, actionMap]

lemma mapDeltaAction_step (δ : ℤ) (hδ : δ ≠ 0)
  (U : IndisputableMonolith.Constants.RSUnits.RSUnits) (n : ℤ) :
  mapDeltaAction δ hδ U (fromZ δ (n+1)) - mapDeltaAction δ hδ U (fromZ δ n)
    = IndisputableMonolith.Constants.RSUnits.hbar U := by
  simpa [mapDeltaAction, actionMap]

lemma mapDelta_diff_toZ (δ : ℤ) (hδ : δ ≠ 0) (f : AffineMapZ)
  (p q : DeltaSub δ) :
  mapDelta δ hδ f p - mapDelta δ hδ f q
    = f.slope * ((toZ δ p - toZ δ q : ℤ) : ℝ) := by
  classical
  simpa using (mapDelta_diff (δ:=δ) (hδ:=hδ) (f:=f) (p:=p) (q:=q))

end UnitMapping
end IndisputableMonolith


