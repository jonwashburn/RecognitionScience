import Mathlib

/-! Causality: Kinematics, n-ball predicate, and BFS equivalence (ConeBound). -/

namespace IndisputableMonolith
namespace Causality

variable {α : Type}

structure Kinematics (α : Type) where
  step : α → α → Prop

inductive ReachN (K : Kinematics α) : Nat → α → α → Prop
| zero {x} : ReachN K 0 x x
| succ {n x y z} : ReachN K n x y → K.step y z → ReachN K (n+1) x z

def inBall (K : Kinematics α) (x : α) (n : Nat) (y : α) : Prop :=
  ∃ k ≤ n, ReachN K k x y

lemma reach_in_ball {K : Kinematics α} {x y : α} {n : Nat}
  (h : ReachN K n x y) : inBall K x n y := ⟨n, le_rfl, h⟩

lemma reach_le_in_ball {K : Kinematics α} {x y : α} {k n : Nat}
  (hk : k ≤ n) (h : ReachN K k x y) : inBall K x n y := ⟨k, hk, h⟩

def Reaches (K : Kinematics α) (x y : α) : Prop := ∃ n, ReachN K n x y

lemma reaches_of_reachN {K : Kinematics α} {x y : α} {n : Nat}
  (h : ReachN K n x y) : Reaches K x y := ⟨n, h⟩

lemma inBall_mono {K : Kinematics α} {x y : α} {n m : Nat}
  (hnm : n ≤ m) : inBall K x n y → inBall K x m y := by
  intro ⟨k, hk, hkreach⟩
  exact ⟨k, le_trans hk hnm, hkreach⟩

end Causality

namespace Causality

variable {α : Type}

def ballP (K : Kinematics α) (x : α) : Nat → α → Prop
| 0, y => y = x
| Nat.succ n, y => ballP K x n y ∨ ∃ z, ballP K x n z ∧ K.step z y

lemma ballP_mono {K : Kinematics α} {x : α} {n m : Nat}
  (hnm : n ≤ m) : {y | ballP K x n y} ⊆ {y | ballP K x m y} := by
  induction hnm with
  | refl => intro y hy; exact (by simpa using hy)
  | @step m hm ih =>
      intro y hy
      exact Or.inl (ih hy)

lemma reach_mem_ballP {K : Kinematics α} {x y : α} :
  ∀ {n}, ReachN K n x y → ballP K x n y := by
  intro n h; induction h with
  | zero => simp [ballP]
  | @succ n x y z hxy hyz ih =>
      exact Or.inr ⟨y, ih, hyz⟩

lemma inBall_subset_ballP {K : Kinematics α} {x y : α} {n : Nat} :
  inBall K x n y → ballP K x n y := by
  intro ⟨k, hk, hreach⟩
  have : ballP K x k y := reach_mem_ballP (K:=K) (x:=x) (y:=y) hreach
  have mono := ballP_mono (K:=K) (x:=x) hk
  exact mono this

lemma ballP_subset_inBall {K : Kinematics α} {x y : α} :
  ∀ {n}, ballP K x n y → inBall K x n y := by
  intro n
  induction n generalizing y with
  | zero => intro hy; rcases hy with rfl; exact ⟨0, le_rfl, ReachN.zero⟩
  | succ n ih =>
      intro hy
      cases hy with
      | inl hy' =>
          rcases ih hy' with ⟨k, hk, hkreach⟩
          exact ⟨k, Nat.le_trans hk (Nat.le_succ _), hkreach⟩
      | inr h' =>
          rcases h' with ⟨z, hz, hstep⟩
          rcases ih hz with ⟨k, hk, hkreach⟩
          exact ⟨k + 1, Nat.succ_le_succ hk, ReachN.succ hkreach hstep⟩

end Causality

namespace ConeBound

open Causality

variable {α : Type} {d : Nat}

class BoundedStep (α : Type) (degree_bound : Nat) where
  step : α → α → Prop
  neighbors : α → Finset α
  step_iff_mem : ∀ x y, step x y ↔ y ∈ neighbors x
  degree_bound_holds : ∀ x, (neighbors x).card ≤ degree_bound

variable [DecidableEq α]
variable [B : BoundedStep α d]

def KB : Kinematics α := { step := BoundedStep.step }

noncomputable def ballFS (x : α) : Nat → Finset α
| 0 => {x}
| Nat.succ n =>
    let prev := ballFS x n
    prev ∪ prev.bind (fun z => BoundedStep.neighbors z)

@[simp] lemma mem_ballFS_zero {x y : α} : y ∈ ballFS (α:=α) x 0 ↔ y = x := by
  simp [ballFS]

@[simp] lemma mem_bind_neighbors {s : Finset α} {y : α} :
  y ∈ s.bind (fun z => BoundedStep.neighbors z) ↔ ∃ z ∈ s, y ∈ BoundedStep.neighbors z := by
  classical
  simp

theorem mem_ballFS_iff_ballP (x y : α) : ∀ n, y ∈ ballFS (α:=α) x n ↔ ballP (KB (α:=α)) x n y := by
  classical
  intro n
  induction' n with n ih generalizing y
  · simpa [ballFS, ballP]
  · have : ballFS (α:=α) x (Nat.succ n) =
      let prev := ballFS (α:=α) x n
      prev ∪ prev.bind (fun z => BoundedStep.neighbors z) := by rfl
    dsimp [ballFS] at this
    simp [ballFS, ballP, ih, BoundedStep.step_iff_mem]

@[simp] lemma card_singleton {x : α} : ({x} : Finset α).card = 1 := by
  classical
  simp

lemma card_union_le (s t : Finset α) : (s ∪ t).card ≤ s.card + t.card := by
  classical
  have : (s ∪ t).card ≤ (s ∪ t).card + (s ∩ t).card := Nat.le_add_right _ _
  simpa [Finset.card_union_add_card_inter] using this

lemma card_bind_le_sum (s : Finset α) (f : α → Finset α) :
  (s.bind f).card ≤ ∑ z in s, (f z).card := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha ih
    have hbind : (insert a s).bind f = f a ∪ s.bind f := by
      simp [Finset.bind, ha]
    have hle : ((insert a s).bind f).card ≤ (f a).card + (s.bind f).card := by
      simpa [hbind] using card_union_le (f a) (s.bind f)
    have hsum : (f a).card + (s.bind f).card ≤ ∑ z in insert a s, (f z).card := by
      simpa [Finset.sum_insert, ha] using Nat.add_le_add_left ih _
    exact le_trans hle hsum

lemma sum_card_neighbors_le (s : Finset α) :
  ∑ z in s, (BoundedStep.neighbors z).card ≤ d * s.card := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha ih
    have hdeg : (BoundedStep.neighbors a).card ≤ d := BoundedStep.degree_bound_holds a
    have : ∑ z in insert a s, (BoundedStep.neighbors z).card = (BoundedStep.neighbors a).card + ∑ z in s, (BoundedStep.neighbors z).card := by
      simp [Finset.sum_insert, ha]
    have hle : (BoundedStep.neighbors a).card + ∑ z in s, (BoundedStep.neighbors z).card ≤ d + ∑ z in s, (BoundedStep.neighbors z).card := Nat.add_le_add_right hdeg _
    have hmul : d + ∑ z in s, (BoundedStep.neighbors z).card ≤ d * (s.card + 1) := by
      have := ih
      simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_one] using (Nat.add_le_add_left this d)
    have : ∑ z in insert a s, (BoundedStep.neighbors z).card ≤ d * (insert a s).card := by
      simpa [this, Finset.card_insert_of_not_mem ha, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using (le_trans hle hmul)
    exact this

lemma card_bind_neighbors_le (s : Finset α) :
  (s.bind (fun z => BoundedStep.neighbors z)).card ≤ d * s.card := by
  classical
  exact le_trans (card_bind_le_sum (s := s) (f := fun z => BoundedStep.neighbors z)) (sum_card_neighbors_le (s := s))

lemma card_ballFS_succ_le (x : α) (n : Nat) :
  (ballFS (α:=α) x (n+1)).card ≤ (1 + d) * (ballFS (α:=α) x n).card := by
  classical
  have : ballFS (α:=α) x (Nat.succ n) =
    let prev := ballFS (α:=α) x n
    prev ∪ prev.bind (fun z => BoundedStep.neighbors z) := by rfl
  dsimp [ballFS] at this
  have h_union_le : (let prev := ballFS (α:=α) x n;
                     (prev ∪ prev.bind (fun z => BoundedStep.neighbors z)).card)
                    ≤ (ballFS (α:=α) x n).card + (ballFS (α:=α) x n).bind (fun z => BoundedStep.neighbors z) |>.card := by
    classical
    simpa [ballFS] using card_union_le (ballFS (α:=α) x n) ((ballFS (α:=α) x n).bind (fun z => BoundedStep.neighbors z))
  have h_bind_le : ((ballFS (α:=α) x n).bind (fun z => BoundedStep.neighbors z)).card ≤ d * (ballFS (α:=α) x n).card := card_bind_neighbors_le (s := ballFS (α:=α) x n)
  have : (ballFS (α:=α) x (Nat.succ n)).card ≤ (ballFS (α:=α) x n).card + d * (ballFS (α:=α) x n).card := by
    simpa [this] using Nat.le_trans h_union_le (Nat.add_le_add_left h_bind_le _)
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.one_mul] using this

theorem ballFS_card_le_geom (x : α) : ∀ n : Nat, (ballFS (α:=α) x n).card ≤ (1 + d) ^ n := by
  classical
  intro n
  induction' n with n ih
  · simpa [ballFS, card_singleton] using (Nat.le_of_eq (by simp : (1 + d) ^ 0 = 1))
  · have hrec := card_ballFS_succ_le (α:=α) (d:=d) (x := x) (n := n)
    have hmul : (1 + d) * (ballFS (α:=α) x n).card ≤ (1 + d) * (1 + d) ^ n := by exact Nat.mul_le_mul_left _ ih
    exact le_trans hrec hmul

end ConeBound

end IndisputableMonolith
