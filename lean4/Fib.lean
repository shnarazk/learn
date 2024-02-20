import Mathlib.Data.Nat.Basic

open Nat

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
