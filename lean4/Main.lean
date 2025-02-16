import Aesop
import Mathlib.Data.Real.Basic
-- import Mathlib.Data.Nat.Basic
import Math.Leibniz
-- import «Le»
-- import «Combinator»

def main : IO Unit := do
  let pairs : Nat := 10 * 1000 * 1000
  let (result, time) ← Aesop.time <| leibnizIO pairs
  IO.println s!"pi {pairs} = {result} in {time.printAsMillis}."

  let pairs : Nat := 100 * 1000 * 1000
  let (result, time) ← Aesop.time <| leibnizIO pairs
  IO.println s!"pi {pairs} = {result} in {time.printAsMillis}."
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

