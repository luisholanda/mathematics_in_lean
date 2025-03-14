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
  · rw [abs_of_neg h]
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
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, le_neg_self_iff]
    apply h.le

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
    apply neg_le_self h
  · rw [abs_of_neg h]

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with h | h
  · rw [abs_of_nonneg h]
    linarith [le_abs_self x, le_abs_self y]
  · rw [abs_of_neg h]
    linarith [neg_le_abs_self x, neg_le_abs_self y]

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  rcases lt_or_ge 0 y with h | h
  · rw [abs_of_pos h]
    constructor <;> intro h₁
    · left
      exact h₁
    · rcases h₁ with h₁ | h₁
      · exact h₁
      · linarith
  · rw [abs_of_nonpos h]
    constructor <;> intro h₁
    · right; exact h₁
    rcases h₁ with h₁ | h₁
    · linarith
    · exact h₁

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  rcases lt_or_ge 0 x with h | h
  · rw [abs_of_pos h]
    constructor <;> intro h₁
    · constructor <;> linarith
    · linarith
  · rw [abs_of_nonpos h]
    constructor <;> intro h₁
    · constructor <;> linarith
    · linarith


end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, h | h⟩ <;> rw [h] <;> linarith [sq_nonneg x, sq_nonneg y]

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h₁ := eq_zero_or_eq_zero_of_mul_eq_zero (a := x - 1) (b := x + 1) (by linarith)
  rcases h₁ with h₁ | h₁
  · left; exact sub_eq_zero.mp h₁
  · rw [← neg_neg 1] at h₁
    right; exact add_neg_eq_zero.mp h₁

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h₁ := eq_zero_or_eq_zero_of_mul_eq_zero (a := x - y) (b := x + y) (by linarith)
  rcases h₁ with h₁ | h₁
  · left; linarith
  · right; linarith

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h₁ := eq_zero_or_eq_zero_of_mul_eq_zero (a := x - 1) (b := x + 1) <| by
    ring_nf
    rw [h, neg_add_cancel]
  rcases h₁ with h₁ | h₁
  · left; exact sub_eq_zero.mp h₁
  · rw [← neg_neg 1] at h₁
    right; exact add_neg_eq_zero.mp h₁

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h₁ := eq_zero_or_eq_zero_of_mul_eq_zero (a := x - y) (b := x + y) <| by
    ring_nf
    rw [h, sub_self]
  rcases h₁ with h₁ | h₁
  · left
    rw [sub_eq_zero] at h₁
    exact h₁
  · right
    rw [← add_zero x, ← zero_add (-y)]
    nth_rw 1 [← add_neg_cancel y, ← add_assoc]
    apply add_right_cancel_iff.mpr h₁


end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor <;> intro h
  · by_cases h₁ : P
    · right; exact h h₁
    · left; exact h₁
  · rcases h with h | h
    · intro h₁; contradiction
    · intro; exact h
