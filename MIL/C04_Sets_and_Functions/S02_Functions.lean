import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · intro h x h₁
    exact h ⟨x, ⟨h₁, by rfl⟩⟩
  · rintro h y ⟨x, h₁, rfl⟩
    exact h h₁

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  rintro x ⟨x', h₁, h₂⟩
  rwa [h h₂] at h₁

example : f '' (f ⁻¹' u) ⊆ u := by
  rintro y ⟨x, h, rfl⟩
  exact h

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  rintro y h₁
  obtain ⟨x, rfl⟩ := h y
  use x
  exact ⟨h₁, by rfl⟩

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  rintro y ⟨x, h₁, rfl⟩
  use x
  exact ⟨h h₁, by rfl⟩

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := fun _ h₁ ↦ h h₁

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  constructor
  repeat
    intro h
    assumption

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro y ⟨x, ⟨h₁, h₂⟩, rfl⟩
  constructor
  repeat use x

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro y ⟨⟨x₁, h₁, rfl⟩, ⟨x₂, h₂, h₃⟩⟩
  rw [h h₃] at h₂
  use x₁
  exact ⟨⟨h₁, h₂⟩, by rfl⟩

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  intro y ⟨⟨x, h, h₁⟩, h₂⟩
  use x
  have h₃ : x ∉ t := by
    intro h₃
    exact h₂ ⟨x, h₃, h₁⟩
  exact ⟨⟨h, h₃⟩, h₁⟩

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := fun _ ↦ id

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext y
  constructor
  · rintro ⟨⟨x, h, rfl⟩, h₁⟩
    use x
    exact ⟨⟨h, h₁⟩, by rfl⟩
  · rintro ⟨x, ⟨h, h₁⟩, rfl⟩
    exact ⟨(by use x), h₁⟩

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  rintro _ ⟨x, ⟨⟨h, h₁⟩, rfl⟩⟩
  constructor
  · use x
  · assumption

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  rintro x ⟨h, h₁⟩
  constructor
  · use x
  · assumption

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (h | h)
  · left; use x
  · right; assumption

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y
  constructor
  · rintro ⟨x, ⟨⟨xs, ⟨⟨i, rfl⟩, h⟩⟩, rfl⟩⟩
    simp
    use i, x
  · rintro ⟨ys, ⟨⟨i, rfl⟩, ⟨x, ⟨h, h₁⟩⟩⟩⟩
    use x
    constructor
    · use A i
      simp [h]
    · assumption


example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  rintro _ ⟨x, ⟨h, rfl⟩⟩ ys ⟨i, rfl⟩
  simp at h ⊢
  use x
  exact ⟨h i, by rfl⟩


example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  rintro y h
  simp at h ⊢
  obtain ⟨x, ⟨h₁, rfl⟩⟩ := h i
  use x
  constructor
  · intro i'
    obtain ⟨x', ⟨h₂, h₃⟩⟩ := h i'
    rcases injf h₃
    assumption
  · rfl

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  constructor
  · rintro ⟨ys, ⟨⟨i, rfl⟩, h⟩⟩
    simp
    use i
  · rintro ⟨xs, ⟨⟨i, rfl⟩, h⟩⟩
    simp at h ⊢
    use i

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  constructor
  repeat
    intro h
    simp at h ⊢
    assumption

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x₁ x₁pos x₂ x₂pos h
  have h₁ : ∀ x : ℝ, x ≥ 0 → x = √x ^ (2: ℝ) := by
    intro x xpos
    rw [sqrt_eq_rpow x, div_eq_inv_mul, mul_one]
    symm
    apply rpow_inv_rpow xpos two_ne_zero
  rw [h₁ x₁ x₁pos, h₁ x₂ x₂pos, h]

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  sorry

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  sorry

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  sorry

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f :=
  sorry

example : Surjective f ↔ RightInverse (inverse f) f :=
  sorry

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S
  sorry
  have h₃ : j ∉ S
  sorry
  contradiction

-- COMMENTS: TODO: improve this
end
