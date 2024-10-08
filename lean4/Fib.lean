import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic
open BigOperators
open Nat

section Playground
open Finset -- for `range`
variable (n : Nat)

#eval ∑ i < 5, i + 100
#eval Finset.range 5 = Finset.range 4 ⊔ Finset.mk {4} (by simp)

example : Finset.range 5 = Finset.range 4 ⊔ Finset.mk {4} (by simp) := by rfl
example : Finset.mk {4} (by simp) = { 4 } := by rfl
example : Finset.range 5 = Finset.range 4 ⊔ {4} := by rfl
example : ∑ i ∈ range 5, i = ∑ i ∈ (Finset.range 4 ⊔ {4}), i := by rfl
example : ∑ i ∈ (Finset.range 4 ⊔ {4}), i =
    ∑ i ∈ Finset.range 4, i + ∑ i ∈ {4}, i := by
  rfl

end Playground

def fib (n : ℕ) : ℕ :=
  match n with
  | zero => 0
  | succ zero => 1
  | succ (succ n₂) => fib (n₂ + 1) + fib n₂

#eval fib 0
#eval fib 1
#eval fib 2
#eval fib 3
#eval fib 4
#eval fib 5

lemma fib_is_fib (n : ℕ) : fib (succ (succ n)) = fib (succ n) + fib n := by
  rw [fib]
