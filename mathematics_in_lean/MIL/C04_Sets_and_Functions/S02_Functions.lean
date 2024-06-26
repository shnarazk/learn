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
  { simp }
  { simp }

-- Injective =単射
example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x1
  simp
  intro x0 xh eq
  exact mem_of_eq_of_mem (h (Eq.symm eq)) xh
  done

example : f '' (f ⁻¹' u) ⊆ u := by
  simp
  intro x X
  exact X

-- Surjective = 全射
example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro y yu
  rcases h y with ⟨x, B⟩
  simp
  use x
  constructor
  { exact mem_of_eq_of_mem B yu }
  { exact B }

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  simp
  rw [← image_subset_iff]
  exact image_mono h

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x xh
  exact h xh

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  constructor
  { simp }
  { simp }

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  simp
  constructor
  {
    intro x hx
    simp
    use x
    simp
    exact mem_of_mem_inter_left hx
  }
  {
    intro x hx
    simp
    use x
    simp
    exact mem_of_mem_inter_right hx
  }

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  intro x xh
  rcases xh with ⟨xs, xt⟩
  simp at xs
  simp at xt
  rw [mem_image]
  simp
  rcases xs with ⟨y1, ⟨h1y0, h1y1⟩⟩
  rcases xt with ⟨y2, ⟨h2y0, h2y1⟩⟩
  rw [← h2y1] at h1y1  -- h を使うためにはf x = f yの形の式が必要
  rcases h h1y1 with ⟨A, B⟩
  use y1

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  intro x xf
  simp
  simp at xf
  rcases xf with ⟨⟨y, left⟩, right⟩
  use y
  constructor
  {
    constructor
    { exact left.left }
    { by_contra yt ; exact absurd left.right (right y yt) }
  }
  { exact left.right }

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  simp
  rfl

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext x
  constructor
  {
    intro ximage
    simp at ximage
    simp
    rcases ximage with ⟨left, right⟩
    rcases left with ⟨y, ⟨ya, left'⟩⟩
    use y
    constructor
    { rw [← left'] at right ; exact ⟨ya, right⟩ }
    { exact left' }
  }
  {
    intro ximage
    simp at ximage
    simp
    rcases ximage with ⟨y, ⟨⟨A, B⟩, C⟩⟩
    constructor
    { use y }
    { rw [C] at B ; exact B }
  }

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  simp
  intro x xh
  simp
  rcases xh with ⟨xs, p⟩
  simp at p
  use x

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  simp
  intro x hx
  rcases hx with ⟨A, _⟩
  simp
  use x

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  simp
  intro x xs
  simp
  constructor -- これをleftとしても同じ構成になる
  { use x }   -- 証明になっているのか？

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext xi
  simp
  constructor
  { simp ; intro yi i yh1 yh2 ; use i, yi }
  {
    simp
    intro x a ha fa
    use a
    constructor
    { use x }
    { exact fa }
  }

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro b hb
  simp at hb
  rcases hb with ⟨a, ⟨left, right⟩⟩
  simp
  intro x
  use a
  constructor
  { exact left x }
  { exact right }

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro a h
  simp at h
  simp
  rcases h i with ⟨a, ⟨_, _, _⟩⟩
  use a
  constructor
  {
    intro j
    rcases h j with ⟨b, ⟨hb, eq⟩⟩
    apply injf at eq
    rw [eq] at hb
    exact hb
  }
  { rfl }

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  simp

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  simp

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
  intro x xnonneg y ynonneg
  intro e
  calc
    x = √(x * x) := by rw [sqrt_mul_self xnonneg]
    _ = √x * √x := by rw [sqrt_mul xnonneg x]
    _ = √y * √y := by rw [e]
    _ = √(y * y) := by rw [← sqrt_mul ynonneg y]
    _ = y := by rw [sqrt_mul_self ynonneg]

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x xnonneg y ynonneg
  intro xy
  simp at xy
  rw [pow_eq_pow_iff_of_ne_zero _] at xy
  rcases xy with eq | ne
  { exact eq ; done }
  { simp at ne
    simp at xnonneg
    simp at ynonneg
    rw [le_iff_eq_or_lt] at xnonneg
    rcases xnonneg with Case | Case
    {
      rw [← Case] at ne
      simp at ne
      rw [Case] at ne
      exact ne.symm
      done
    }
    {
      rw [ne] at Case
      simp at Case
      rw [lt_iff_not_ge y 0] at Case
      exact absurd ynonneg Case
    }
  }
  { simp }

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext x
  simp
  constructor
  {
    intro h
    rcases h with ⟨y, _, C⟩
    have C': 0 ≤ √y := by exact sqrt_nonneg y
    rw [C] at C'
    exact C'
  }
  {
    intro zx
    use x ^ 2
    constructor
    { exact sq_nonneg x }
    { exact sqrt_sq zx }
  }

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext x
  simp
  constructor
  {
    intro Y
    rcases Y with ⟨y, Y2⟩
    rw [← Y2]
    exact sq_nonneg y
  }
  {
    intro zx
    use √x
    rw [sq_sqrt zx]
  }

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
