import Mathlib.Tactic
import Std.Data.HashMap
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet

open Nat Finset Real
open Std

namespace Hash

universe u v

variable {α : Type u} {β : Type v} {_ : BEq α} {_ : Hashable α}
variable {γ : Type v} [Inhabited γ]

def base : HashMap ℕ ℕ := HashMap.ofList [(0, 10), (1, 20)]

theorem base_hash_has_zero : 0 ∈ base := by
  rw [base]
  simp

theorem base_hash_has_one : 1 ∈ base := by
  rw [base]
  simp

theorem base_hash_has_only_them : ∀ k > 1, k ∉ base := by
  rw [base]
  simp
  rintro k h
  omega

theorem zero_gt_eq_NeZero (n : Nat) (h : 0 < n) : NeZero n := by
  have : n ≠ 0 := by omega
  exact { out := this }

@[simp]
theorem base_hash_size_eq_two : base.size = 2 := by
  apply HashMap.size_ofList
  simp

theorem base_hash_has_no_hole : ∀ k < base.size, k ∈ base := by
  simp
  intro n h
  have : n = 0 ∨ n = 1 := by omega
  rcases this with h0 | h1
  {rw [h0] ; exact base_hash_has_zero}
  {rw [h1] ; exact base_hash_has_one}

theorem base_hash_is_bounded : ∀ k ∈ base, k < base.size := by
  intro k h
  have h₁ : base.size = 2 := by
    apply HashMap.size_ofList
    simp
  rw [h₁]
  have : k ∈ base → k ≤ 1 := by
    simp [h]
    have : k ∈ base → k ≤ 1 := by
      have : ∀ k > 1, k ∉ base := by exact base_hash_has_only_them
      contrapose
      simp
      exact fun a ↦ this k a
    rcases this h with h₁
    exact h₁
  rcases this h with h₀
  omega

theorem nonempty_hash {h : HashMap ℕ β} : h.contains 0 → ¬h.isEmpty := by
  rintro h₁
  have : ∃ a : ℕ, a ∈ h := by
    exact Exists.intro 0 h₁
  have : h.isEmpty = false := by
    exact HashMap.isEmpty_eq_false_iff_exists_mem.mpr this
  exact ne_true_of_eq_false this

theorem nonempty_hash_size {h : HashMap ℕ β} : ¬h.isEmpty → NeZero h.size := by
  have h₁ : h.isEmpty = (h.size == 0) := by exact rfl
  have h₃ : ¬NeZero h.size ↔ h.size = 0 := by exact not_neZero
  contrapose!
  simp [h₃]
  simp [h₁]

theorem hash_with_zero_size {h : HashMap ℕ β} : h.contains 0 → NeZero h.size := by
  rintro h₁
  exact nonempty_hash_size (nonempty_hash h₁)

end Hash
