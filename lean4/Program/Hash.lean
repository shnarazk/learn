import Mathlib.Tactic
import Std.Data.HashMap
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet

open Nat Finset Real
open Std

theorem size_of_hash_with_zero {α : Type} (l : HashMap Nat α) :
    l.contains 0 → NeZero l.size := by
  intro h
  have h₁ : 0 ∈ l := by exact h
  have size_erase : (l.erase 0).size = if 0 ∈ l then l.size - 1 else l.size := by
    exact HashMap.size_erase
  simp [h₁] at size_erase
  have : (l.erase 0).size + 1 = l.size := by
    sorry
  have size_ge_zero : ∀ h : HashMap Nat α, 0 ≤ h.size := by
    exact fun h ↦ Nat.zero_le h.size
  rcases size_ge_zero (l.erase 0) with l'_size
  have : 0 ≤ l.size - 1 := by exact Nat.zero_le (l.size - 1)
  have : 0 ≠ l.size := by
    sorry
  exact { out := id (Ne.symm this) }
