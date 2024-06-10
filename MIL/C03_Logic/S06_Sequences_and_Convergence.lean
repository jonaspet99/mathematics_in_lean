import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext a b
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n hnmx
  apply max_le_iff.1 at hnmx
  have h₁ := hs n hnmx.1
  have h₂ := ht n hnmx.2
  have h₃ : |s n - a| + |t n - b| < ε := by
    linarith [h₁, h₂]
  apply lt_of_le_of_lt _ h₃
  ring_nf
  have : s n + t n + (-a - b) = (s n - a) + (t n - b) := by ring_nf
  rw [this]
  apply abs_add




theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  rw [ConvergesTo]
  intro ε hε
  have :  ∀n:ℕ, |c * s n - c * a| = |c| * |(s n - a)| := by
    intro n
    rw [<- abs_mul c (s n - a)]
    congr
    ring_nf
  rw [ConvergesTo] at cs
  have hεc : ε/|c| > 0 := by
    #check lt_div_iff acpos
    apply (lt_div_iff acpos).mpr
    norm_num
    exact hε
  obtain ⟨N: ℕ, hN⟩ := cs (ε/|c|) hεc
  use N
  intro n hn
  rw [this n]
  have : ε = ε / |c| * |c| := by
    field_simp
  rw [this]
  #check hN n hn
  rw [mul_comm]
  apply (mul_lt_mul_right acpos).mpr
  exact hN n hn




theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  rintro n hn
  have h' := h n hn
  #check abs_add
  rw [<- sub_add_cancel (s n) a]
  apply lt_of_le_of_lt
  apply abs_add (s n - a) a
  rw [add_comm]
  apply add_lt_add_left
  assumption


theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n hn
  have ⟨hnn0, hnn1⟩ := max_le_iff.mp hn
  ring_nf
  rw [abs_mul]
  have ht1 :=  h₀ n hnn0
  have ht2 := h₁ n hnn1
  ring_nf at ht2
  convert mul_lt_mul'' ht1 ht2 (abs_nonneg _) (abs_nonneg _)
  field_simp


theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by
    by_contra h
    push_neg at h
    have : 0 ≤ |a - b| := abs_nonneg _
    have : a = b := by
      apply eq_of_sub_eq_zero
      apply abs_eq_zero.mp (le_antisymm h this)
    exact abne this
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by
    apply hNa
    change max Na Nb ≥ Na
    apply le_max_left
  have absb : |s N - b| < ε := by
    apply hNb
    change max Na Nb ≥ Nb
    apply le_max_right
  have : |a - b| < |a - b| := by
    have hsum : |a - b| = ε + ε := by
      dsimp [ε]
      ring_nf
    nth_rw 2 [hsum]
    have hab: |a - b| = |(s N- b) - (s N - a)| := by
      congr 1
      ring_nf
    rw [hab]
    rw [sub_eq_add_neg]
    apply lt_of_le_of_lt
    apply abs_add
    apply add_lt_add
    assumption
    simp
    rw [<- abs_neg, neg_sub]
    assumption
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
