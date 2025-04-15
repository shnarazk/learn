import Mathlib.Data.Real.Basic
-- import Mathlib.Data.Nat.Basic
import Math.Leibniz
-- import Lean
-- import «Le»
-- import «Combinator»

universe u

@[inline]
def elapsedTime {α : Type} {m : Type → Type u} [Monad m] [MonadLiftT BaseIO m] (x : m α) : m (α × Nat) := do
  let beg ← IO.monoNanosNow
  let val ← x
  let fin ← IO.monoNanosNow
  return (val, fin - beg)

def main : IO Unit := do
  let pairs : Nat := 10 * 1000 * 1000
  let (result, time) ← elapsedTime <| leibnizIO pairs
  IO.println s!"pi {pairs} = {result} in {time / 1000_000} msec."

  let pairs : Nat := 100 * 1000 * 1000
  let (result, time) ← elapsedTime <| leibnizIO pairs
  IO.println s!"pi {pairs} = {result} in {time / 1000_000} msec."
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
