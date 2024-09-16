import Aesop
import Mathlib.Data.Real.Basic
import «Le»
-- import «Combinator»
-- import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic

def leib (n : Nat): IO Float := do
  IO.println "ok"
  let x := leibniz n
  return x

def main : IO Unit := do
  -- IO.println s!"fib 20 = {fib 20} ."
  let (result, time) ← Aesop.time <| (leib (100 * 1000 * 1000))
  IO.println s!"pi = {result} in {time.printAsMillis}."
  /-
  let lines ← readData "lakefile.lean"
  lines.forM IO.println
  let x ← IO.getEnv "HOME"
  match x with
  | some x => IO.println x
  | none => pure ()
  -/

-- #eval Nat.gcd 20 5
-- #eval Nat.lcm 20 5
-- theorem ConcrateMath (n m : Nat) : (n % m) = max (Nat.gcd n m) (Nat.gcd m n) := sorry

