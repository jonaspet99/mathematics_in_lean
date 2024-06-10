import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  repeat'
    apply le_inf
    . apply inf_le_right
    apply inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  repeat
    apply le_inf
    apply le_trans
    apply inf_le_left
    apply inf_le_left
  apply le_inf
  . apply le_trans
    apply inf_le_left
    apply inf_le_right
  apply le_trans
  apply inf_le_right
  apply le_refl
  apply le_inf
  apply le_inf
  apply inf_le_left
  apply le_trans
  apply inf_le_right
  apply inf_le_left
  apply le_trans
  apply inf_le_right
  apply inf_le_right

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  repeat'
  apply sup_le
  apply le_sup_right
  apply le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  apply sup_le
  apply sup_le
  apply le_sup_left
  have h : y ≤ (y ⊔ z) := by
    apply le_sup_left
  apply le_trans h
  apply le_sup_right
  have h₁: z ≤ (y ⊔ z) := by
    apply le_sup_right
  apply le_trans h₁
  apply le_sup_right
  apply sup_le
  calc
    x ≤ x ⊔ y := by apply le_sup_left
    _ ≤ x ⊔ y ⊔ z := by apply le_sup_left
  apply sup_le
  calc
    y ≤ x ⊔ y := by apply le_sup_right
    _ ≤ x ⊔ y ⊔ z := by apply le_sup_left
  apply le_sup_right


theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  . apply inf_le_left
  apply le_inf
  . apply le_refl
  apply le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  . apply sup_le
    apply le_refl
    apply inf_le_left
  apply le_sup_left
end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  apply le_antisymm
  . apply le_inf
    apply sup_le
    apply le_sup_left
    apply le_trans
    apply inf_le_left
    apply le_sup_right
    apply sup_le
    apply le_sup_left
    apply le_trans
    apply inf_le_right
    apply le_sup_right
  rw [h (a ⊔ b) a c]
  apply sup_le
  . apply le_trans
    apply inf_le_right
    apply le_sup_left
  rw [inf_comm (a ⊔ b) c]
  rw [h c a b]
  apply sup_le
  . apply le_trans
    apply inf_le_right
    apply le_sup_left
  rw [inf_comm b c]
  apply le_sup_right

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  apply le_antisymm
  . rw [h]
    apply le_inf
    . apply le_trans
      apply inf_le_left
      apply le_sup_right
    rw [sup_comm (a ⊓ b)]
    rw [h]
    apply le_inf
    . apply le_trans
      apply inf_le_left
      apply le_sup_right
    rw [sup_comm]
    apply inf_le_right
  apply le_inf
  . apply sup_le
    apply inf_le_left
    apply inf_le_left
  apply sup_le
  . apply le_trans
    apply inf_le_right
    apply le_sup_left
  apply le_trans
  apply inf_le_right
  apply le_sup_right

end

section
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

lemma aux (h : a ≤ b) : 0 ≤ b - a := by
  rw [sub_eq_add_neg]
  rw [<- sub_add_cancel 0 (-a)]
  apply add_le_add_right
  rw [sub_neg_eq_add, zero_add]
  exact h

lemma aux_1 (h: 0 ≤ b - a) : a ≤ b := by
  rw[<- sub_add_cancel b a]
  nth_rw 1 [<- zero_add a]
  apply add_le_add_right
  exact h

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have h₂: 0 ≤ b* c - a*c := by
    rw [<- mul_sub_right_distrib]
    apply mul_nonneg
    . apply aux
      exact h
    exact h'
  apply aux_1
  exact h₂
end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  have h: dist x x ≤ dist x y + dist y x := by
    apply dist_triangle
  rw [dist_comm y x, dist_self, <- two_mul] at h
  have h₁ : (0:ℝ) ≤ 1/2 := by linarith
  have h₂ := mul_nonneg h₁ h
  have h₃ : 1 / 2 * (2 * dist x y) = dist x y := by ring
  rw [<- h₃]
  exact h₂
end
