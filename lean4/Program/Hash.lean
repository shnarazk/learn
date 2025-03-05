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

theorem base_is_bounded : ∀ k ∈ base, k < base.size := by
  intro k h
  have : base.size = 2 := by
    apply HashMap.size_ofList
    simp
  have : k = 0 ∨ k = 1 := by sorry
  rcases this with k0 | k1 <;> { omega }

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
