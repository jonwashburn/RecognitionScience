import Mathlib
import IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace Recognition
namespace Certification

noncomputable section
open Classical

structure Interval where
  lo : ℝ
  hi : ℝ
  lo_le_hi : lo ≤ hi
@[simp] def memI (I : Interval) (x : ℝ) : Prop := I.lo ≤ x ∧ x ≤ I.hi
@[simp] def width (I : Interval) : ℝ := I.hi - I.lo

lemma abs_sub_le_width_of_memI {I : Interval} {x y : ℝ}
  (hx : memI I x) (hy : memI I y) : |x - y| ≤ width I := by
  have hxhi : x ≤ I.hi := hx.2
  have hylo : I.lo ≤ y := hy.1
  have h1 : x - y ≤ I.hi - I.lo := by
    have hneg : -y ≤ -I.lo := neg_le_neg hylo
    have hleft : x - y ≤ x - I.lo := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using add_le_add_left hneg x
    have hright : x - I.lo ≤ I.hi - I.lo := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using sub_le_sub_right hxhi I.lo
    exact le_trans hleft hright
  have h2 : y - x ≤ I.hi - I.lo := by
    have hxlo : I.lo ≤ x := hx.1
    have hyhi : y ≤ I.hi := hy.2
    have hneg : -x ≤ -I.lo := neg_le_neg hxlo
    have hleft : y - x ≤ y - I.lo := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using add_le_add_left hneg y
    have hright : y - I.lo ≤ I.hi - I.lo := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using sub_le_sub_right hyhi I.lo
    exact le_trans hleft hright
  have hboth : -(I.hi - I.lo) ≤ x - y ∧ x - y ≤ I.hi - I.lo := by
    constructor
    · simpa [neg_sub] using h2
    · exact h1
  simpa [width, sub_eq_add_neg] using (abs_le.mpr hboth)

structure AnchorCert where
  M0 : Interval
  Ires : Species → Interval
  center : Int → ℝ
  eps : Int → ℝ
  eps_nonneg : ∀ z, 0 ≤ eps z

@[simp] def Igap (C : AnchorCert) (z : Int) : Interval :=
{ lo := C.center z - C.eps z
, hi := C.center z + C.eps z
, lo_le_hi := by have := C.eps_nonneg z; linarith }

structure Valid (C : AnchorCert) : Prop where
  M0_pos : 0 < C.M0.lo
  Fgap_in : ∀ i : Species, memI (C.Igap (Z i)) (Fgap (Z i))
  Ires_in_Igap : ∀ i : Species,
    (C.Igap (Z i)).lo ≤ (C.Ires i).lo ∧ (C.Ires i).hi ≤ (C.Igap (Z i)).hi

lemma M0_pos_of_cert {C : AnchorCert} (hC : Valid C) : 0 < C.M0.lo := hC.M0_pos

lemma anchorIdentity_cert {C : AnchorCert} (hC : Valid C)
  (res : Species → ℝ) (hres : ∀ i, memI (C.Ires i) (res i)) :
  ∀ i : Species, |res i - Fgap (Z i)| ≤ 2 * C.eps (Z i) := by
  intro i
  have hinc := (hC.Ires_in_Igap i)
  have hresI : memI (C.Igap (Z i)) (res i) := by
    have hri := hres i
    exact And.intro (le_trans hinc.left hri.left) (le_trans hri.right hinc.right)
  have : |res i - Fgap (Z i)| ≤ width (C.Igap (Z i)) :=
    abs_sub_le_width_of_memI hresI (hC.Fgap_in i)
  have : |res i - Fgap (Z i)| ≤ (C.center (Z i) + C.eps (Z i)) - (C.center (Z i) - C.eps (Z i)) := by
    simpa [Igap, width, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  simpa [two_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this

lemma equalZ_residue_of_cert {C : AnchorCert} (hC : Valid C)
  (res : Species → ℝ) (hres : ∀ i, memI (C.Ires i) (res i))
  {i j : Species} (hZ : Z i = Z j) :
  |res i - res j| ≤ 2 * C.eps (Z i) := by
  have hi : memI (C.Igap (Z i)) (res i) := by
    have hinc := (hC.Ires_in_Igap i); have hri := hres i
    exact And.intro (le_trans hinc.left hri.left) (le_trans hri.right hinc.right)
  have hj : memI (C.Igap (Z j)) (res j) := by
    have hinc := (hC.Ires_in_Igap j); have hrj := hres j
    exact And.intro (le_trans hinc.left hrj.left) (le_trans hrj.right hinc.right)
  have : |res i - res j| ≤ width (C.Igap (Z i)) := by
    have hj' : memI (C.Igap (Z i)) (res j) := by simpa [hZ] using hj
    exact abs_sub_le_width_of_memI hi hj'
  simpa [Igap, width, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, two_mul] using this

noncomputable def zeroWidthCert : AnchorCert :=
{ M0 := { lo := 1, hi := 1, lo_le_hi := by norm_num }
, Ires := fun i => { lo := Fgap (Z i), hi := Fgap (Z i), lo_le_hi := by linarith }
, center := fun z => Fgap z
, eps := fun _ => 0
, eps_nonneg := by intro _; exact by norm_num }

lemma zeroWidthCert_valid : Valid zeroWidthCert := by
  refine {
    M0_pos := by simp [zeroWidthCert]
  , Fgap_in := by
      intro i; dsimp [zeroWidthCert, Igap, memI]; simp
  , Ires_in_Igap := by
      intro i; dsimp [zeroWidthCert, Igap]; constructor <;> simp }

lemma anchorIdentity_of_zeroWidthCert
  (res : Species → ℝ) (hres : ∀ i, memI (zeroWidthCert.Ires i) (res i)) :
  ∀ i : Species, res i = Fgap (Z i) := by
  intro i
  have h := hres i
  dsimp [zeroWidthCert, memI] at h
  have hlo : Fgap (Z i) ≤ res i := by simpa using h.left
  have hhi : res i ≤ Fgap (Z i) := by simpa using h.right
  exact le_antisymm hhi hlo

end
end Certification
end Recognition

namespace RSBridge

def Sector | up | down | lepton | neutrino deriving DecidableEq, Repr
inductive Fermion
| d | s | b
| u | c | t
| e | mu | tau
| nu1 | nu2 | nu3
  deriving DecidableEq, Repr, Inhabited

def sectorOf : Fermion → Sector
| .d | .s | .b => .down
| .u | .c | .t => .up
| .e | .mu | .tau => .lepton
| .nu1 | .nu2 | .nu3 => .neutrino

def tildeQ : Fermion → ℤ
| .u | .c | .t => 4
| .d | .s | .b => -2
| .e | .mu | .tau => -6
| .nu1 | .nu2 | .nu3 => 0

def ZOf (f : Fermion) : ℤ :=
  let q := tildeQ f
  match sectorOf f with
  | .up | .down => 4 + q*q + q*q*q*q
  | .lepton     =>     q*q + q*q*q*q
  | .neutrino   => 0

def gap (Z : ℤ) : ℝ := (Real.log (1 + (Z : ℝ) / (Constants.phi))) / (Real.log (Constants.phi))
notation "𝓕(" Z ")" => gap Z

def residueAtAnchor (f : Fermion) : ℝ := gap (ZOf f)
@[simp] theorem anchorEquality (f : Fermion) : residueAtAnchor f = gap (ZOf f) := rfl

theorem equalZ_residue (f g : Fermion) (hZ : ZOf f = ZOf g) :
    residueAtAnchor f = residueAtAnchor g := by simp [residueAtAnchor, hZ]

noncomputable def rung : Fermion → ℤ
| .e   => 2   | .mu  => 13  | .tau => 19
| .u   => 4   | .c   => 15  | .t   => 21
| .d   => 4   | .s   => 15  | .b   => 21
| .nu1 => 0   | .nu2 => 11  | .nu3 => 19

def M0 : ℝ := 1
@[simp] theorem M0_pos : 0 < M0 := by norm_num

def massAtAnchor (f : Fermion) : ℝ :=
  M0 * Real.exp (((rung f : ℝ) - 8 + gap (ZOf f)) * Real.log (Constants.phi))

theorem anchor_ratio (f g : Fermion) (hZ : ZOf f = ZOf g) :
    massAtAnchor f / massAtAnchor g = Real.exp (((rung f : ℝ) - rung g) * Real.log (Constants.phi)) := by
  unfold massAtAnchor
  set Af := ((rung f : ℝ) - 8 + gap (ZOf f)) * Real.log (Constants.phi)
  set Ag := ((rung g : ℝ) - 8 + gap (ZOf g)) * Real.log (Constants.phi)
  have hM : M0 ≠ 0 := ne_of_gt M0_pos
  calc
    (M0 * Real.exp Af) / (M0 * Real.exp Ag) = (Real.exp Af) / (Real.exp Ag) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using (mul_div_mul_left (Real.exp Af) (Real.exp Ag) M0 hM)
    _ = Real.exp (Af - Ag) := by simpa [Real.exp_sub] using (Real.exp_sub Af Ag).symm
    _ = Real.exp ((((rung f : ℝ) - 8 + gap (ZOf f)) - ((rung g : ℝ) - 8 + gap (ZOf g))) * Real.log (Constants.phi)) := by
      have : Af - Ag = (((rung f : ℝ) - 8 + gap (ZOf f)) - ((rung g : ℝ) - 8 + gap (ZOf g))) * Real.log (Constants.phi) := by
        simp [Af, Ag, sub_eq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_add, add_mul, sub_eq_add_neg]
      have h' : ((rung f : ℝ) - 8 + gap (ZOf f)) - ((rung g : ℝ) - 8 + gap (ZOf g)) = (rung f : ℝ) - rung g + (gap (ZOf f) - gap (ZOf g)) := by ring
      simpa [this, h']
    _ = Real.exp (((rung f : ℝ) - rung g) * Real.log (Constants.phi)) := by
      simpa [hZ, sub_self, add_zero, add_comm, add_left_comm, add_assoc, mul_add, add_right_comm, mul_comm, mul_left_comm, mul_assoc]

structure ResidueCert where
  f  : Fermion
  lo hi : ℚ
  lo_le_hi : lo ≤ hi

def ResidueCert.valid (c : ResidueCert) : Prop :=
  (c.lo : ℝ) ≤ gap (ZOf c.f) ∧ gap (ZOf c.f) ≤ (c.hi : ℝ)

end RSBridge
end IndisputableMonolith
