import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic
open BigOperators
open Nat

section Playground
open Finset -- for `range`
variable (n : ℕ)

#eval ∑ i < 5, i + 100
#eval Finset.range 5 = Finset.range 4 ⊔ Finset.mk {4} (by simp)
#eval Finset.range 1 = Finset.range 0 ⊔ {0}
#eval Finset.range 1
#eval (Finset.range 0 ⊔ {0})

example : Finset.range 5 = Finset.range 4 ⊔ Finset.mk {4} (by simp) := by rfl
example : Finset.mk {4} (by simp) = { 4 } := by rfl
example : Finset.range 5 = Finset.range 4 ⊔ {4} := by rfl
example : ∑ i ∈ range 5, i = ∑ i ∈ (Finset.range 4 ⊔ {4}), i := by rfl
example : ∑ i ∈ (Finset.range 4 ⊔ {4}), i =
    ∑ i ∈ Finset.range 4, i + ∑ i ∈ {4}, i := by
  rfl
#check range_add_one
lemma range_add_one_eq_sup_self : Finset.range (n + 1) = Finset.range n ⊔ {n} := by
  refine Finset.ext_iff.mpr ?_
  intro k
  constructor
  {
    intro kn1
    by_cases kn : k ∈ range n
    { rw [sup_eq_union] ; exact mem_union_left {n} kn }
    {
      simp [range] at kn
      simp [range] at kn1
      rcases kn1 with a|b
      { simp ; right ; exact a }
      { contrapose! b ; exact kn }
    }
  }
  {
    intro H
    simp at H
    simp
    rcases H with A | B
    {
       exact Nat.lt_add_right 1 A
    }
    {
      rw [B] ; exact lt_add_one n
    }
  }

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
