import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
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
  intro n nge
  have hst : |s n - a| + |t n - b| < ε := by
    have hns : |s n - a| < ε / 2 := hs n (le_of_max_le_left nge)
    have hnt : |t n - b| < ε / 2 := ht n (le_of_max_le_right nge)
    convert add_lt_add hns hnt
    norm_num
  have h : |s n + t n - (a + b)| = |s n - a + (t n - b)| := by ring_nf
  rw [h]
  apply lt_of_le_of_lt (abs_add _ _) hst


theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε εpos
  have εcpos : 0 < ε / |c| := div_pos εpos acpos
  rcases cs (ε / |c|) εcpos with ⟨N, hn⟩
  use N
  intro n h₁
  calc
    |c * s n - c * a| = |c| * |s n - a| := by rw [← mul_sub, abs_mul]
    _ < |c| * (ε / |c|) := mul_lt_mul_of_pos_left (hn n h₁) acpos
    _ = ε := mul_div_cancel₀ _ (ne_of_lt acpos).symm


theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n h₁
  calc
    |s n| = |s n - a + a| := by congr; abel
    _ ≤ |s n - a| + |a| := (abs_add _ _)
    _ < |a| + 1 := by linarith [h n h₁]

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use N₁ ⊔ N₀
  intro n h₂
  calc
    |s n * t n - 0| = |s n| * |t n - 0| := by
      ring_nf
      apply abs_mul
    _ < B * (ε / B) := by
      have hsB := h₀ n (le_of_max_le_right h₂)
      have htε := h₁ n (le_of_max_le_left h₂)
      exact mul_lt_mul'' hsB htε (abs_nonneg _) (abs_nonneg _)
    _ = ε := mul_div_cancel₀ _ Bpos.ne.symm


theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by
    norm_num
    exact sub_ne_zero_of_ne abne
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := hNa N (le_of_max_le_left (by rfl))
  have absb : |s N - b| < ε := hNb N (le_of_max_le_right (by rfl))
  have : |a - b| < |a - b| :=
    calc
      |a - b| = |-(s N - a) + (s N - b)| := by
        congr
        ring
      _ ≤ |-(s N - a)| + |s N - b| := abs_add _ _
      _ = |s N - a| + |s N - b| := by rw [abs_neg]
      _ < ε + ε := add_lt_add absa absb
      _ = |a - b| := by norm_num [ε]
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
