import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  . rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h


example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  . rw [abs_of_nonneg h]
  rw [abs_of_neg h]; linarith

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  have := le_abs_self (-x)
  rw [abs_neg] at this; exact this

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rw [abs_le]
  constructor
  . have h: (-x + -y ≤ |x| + |y|) := by
      apply add_le_add (neg_le_abs_self x) (neg_le_abs_self y)
    linarith
  apply add_le_add (le_abs_self x) (le_abs_self y)


theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  . intro h
    rcases le_or_gt 0 y with h'|h'
    . left
      rw [abs_of_nonneg h'] at h
      exact h
    right
    rw [abs_of_neg h'] at h; exact h
  intro h
  rcases h with h'|h'
  . apply lt_of_lt_of_le h'
    exact le_abs_self y
  apply lt_of_lt_of_le h'
  exact neg_le_abs_self y

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  rcases le_or_gt 0 x with h|h
  . rw [abs_of_nonneg]
    constructor
    . intro h'
      constructor
      linarith
      exact h'
    . rintro ⟨_, h₂⟩
      exact h₂
    exact h
  rw [abs_of_neg]
  constructor
  . intro h'
    constructor
    repeat
    linarith
  . rintro ⟨h₁,_⟩
    linarith [h₁]
  exact h


end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  . right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  . rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x,y,h|h⟩; linarith [pow_two_nonneg x, pow_two_nonneg y]; linarith[pow_two_nonneg x, pow_two_nonneg y];

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h' : (x - 1)*(x+1) = 0 := by ring_nf; linarith
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h' with h|h
  . left
    linarith
  right
  linarith

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h': (x - y)*(x+y) = 0 := by ring_nf; linarith;
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h' with h|h
  . left; linarith
  right; linarith

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h': (x - 1)*(x+1) = 0 := by
    ring_nf
    rw [h]
    ring_nf
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h' with h|h
  . left
    rw [<- sub_add_cancel x 1, h, zero_add]
  right
  rw [<- add_sub_cancel_right x 1, h, zero_sub]

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h': (x - y)* (x + y) = 0 := by
    ring_nf; rw [h]; ring_nf;
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h' with h|h
  . left
    apply eq_of_sub_eq_zero
    exact h
  right
  apply eq_of_sub_eq_zero
  ring_nf
  assumption
end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  . contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  intro h
  by_cases h' : P
  . right
    exact h h'
  left
  assumption
  intro h
  rcases h with h'|h'
  intro hp
  contradiction
  intro _
  assumption
