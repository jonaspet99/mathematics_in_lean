import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

#check le_max_left
#check le_max_right
#check max_le

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  apply le_antisymm
  repeat
    apply max_le
    apply le_max_right
    apply le_max_left

lemma min_le_of_le_left {a b c : ℝ} (h : a ≤ b): min a c ≤ b := by
    have h₁ : min a c ≤ a := by exact min_le_left a c
    exact le_trans h₁ h

lemma min_le_of_le_right {a b c : ℝ} (h: a ≤ b): min c a ≤ b := by
    have h₁ : min c a ≤ a := by exact min_le_right c a
    exact le_trans h₁ h

example : min (min a b) c = min a (min b c) := by
  have h {a b c : ℝ} (h : a ≤ b): min a c ≤ b := by
    have h₁ : min a c ≤ a := by exact min_le_left a c
    exact le_trans h₁ h
  have h_opp {a b c : ℝ} (h: a ≤ b): min c a ≤ b := by
    have h₁ : min c a ≤ a := by exact min_le_right c a
    exact le_trans h₁ h
  apply le_antisymm
  . apply le_min
    . apply h
      apply min_le_left
    apply le_min
    . apply h
      apply h_opp
      exact le_refl b
    apply h_opp
    exact le_refl c
  apply le_min
  . apply le_min
    apply h
    apply le_refl
    apply h_opp
    apply h
    apply le_refl
  apply h_opp
  apply h_opp
  apply le_refl

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  . show min a b + c ≤ a + c
    have h: min a b ≤ a := by
      exact min_le_left a b
    apply add_le_add_right
    exact h
  apply add_le_add_right
  apply min_le_right

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  . show  min a b + c ≤ min (a + c) (b + c)
    apply aux
  #check add_neg_cancel_right
  rw [<- add_neg_cancel_right (min (a + c) (b + c)) (-c)]
  rw [neg_neg]
  apply add_le_add_right
  apply le_min
  have h (h₁:min (a + c) (b + c) + -c + c ≤ a + c):  min (a + c) (b + c) + -c ≤ a := by
    exact (add_le_add_iff_right c).mp h₁
  apply h
  ring_nf
  . apply min_le_of_le_left
    apply le_refl
  apply (add_le_add_iff_right c).mp
  ring_nf
  apply min_le_of_le_right
  apply le_refl





#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
  have h: |a-b+b| ≤ |a-b| + |b| := by exact abs_add (a-b) b
  rw [sub_add_cancel] at h
  linarith [h]
end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  . apply dvd_add
    rw [mul_comm x z, <- mul_assoc]
    apply dvd_mul_left
    rw [sq]
    apply dvd_mul_left
  apply dvd_mul_of_dvd_right
  exact h
end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

#check Nat.dvd_antisymm

example : Nat.gcd m n = Nat.gcd n m := by
  apply Nat.dvd_antisymm
  repeat
  . apply Nat.dvd_gcd_iff.mpr
    constructor
    apply Nat.gcd_dvd_right
    apply Nat.gcd_dvd_left
end
