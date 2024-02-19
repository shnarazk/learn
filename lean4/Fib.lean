import Mathlib.Data.Nat.Basic
#eval Lean.versionString

open Nat

def fib (n: Nat): Nat :=
  match n with
  | zero => 0
  | succ zero => 1
  | succ (succ n'') => fib n'' + fib (n'' + 1)

#eval fib 0
#eval fib 1
#eval fib 2
#eval fib 3
#eval fib 4
#eval fib 5

lemma fib_is_the_Fibonacchi(n : Nat) : fib (succ (succ n)) = fib (succ n) + fib n := sorry
