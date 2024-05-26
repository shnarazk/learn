import «Le»
import «Combinator»
-- import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic

def main : IO Unit := do
  IO.println s!"fib 20 = {fib 20} ."
  IO.println s!"pi = {leibniz 10000000} ."
  let lines ← readData "lakefile.lean"
  lines.forM IO.println
  let x ← IO.getEnv "HOME"
  match x with
  | some x => IO.println x
  | none => pure ()

#eval Nat.gcd 20 5
#eval Nat.lcm 20 5
-- theorem ConcrateMath (n m : Nat) : (n % m) = max (Nat.gcd n m) (Nat.gcd m n) := sorry

