import Mathlib.Tactic
open Nat

-- compute pi
def leibniz₁ (n : Nat) (k: Float) (sum : Float) : Float :=
  match n with
  | zero => sum + 8.0 / 3.0
  | succ n' => leibniz₁ n' (k - 4.0) (sum + 8.0 / ((k + 1.0) * (k + 3.0)))

def leibniz₂ (n : Nat) (sum : Float) : Float :=
  match n with
  | zero => sum + 8.0 / 3.0
  | succ n' =>
      let k := n.toFloat * 4.0
      leibniz₂ n' (sum + 8.0 / ((k + 1.0) * (k + 3.0)))

def leibniz (n : Nat) : Float := leibniz₁ n (n.toFloat * 4.0) 0.0
-- def leibniz (n : Nat) : Float := leibniz₂ n 0.0

def leibnizIO (n : Nat) : IO Float := do return leibniz n

#eval leibniz 1000

/-
-- This is the FUN part only on Lean4
-/

namespace this_is_pi_approximation

def leibniz (n : Nat) (k: Float) (sum : Float) : Float :=
  match n with
  | zero => sum + 8 / 3
  | succ n' => leibniz₁ n' (k - 4) (sum + 8 / ((k + 1) * (k + 3)))

def leibniz4 (n : Nat) (k: Float) (sum : Float) : Float :=
  match n with
  | zero => sum + 1/1 - 1 / 3
  | succ n' => leibniz₁ n' (k - 4) (sum + 1 / (k + 1) - 1 / (k + 3))

lemma leibniz4_mul_4_equals_to_leibniz : ∀ n : Nat,
    4 * leibniz4 n (4 * n.toFloat) 0 = leibniz n (4 * n.toFloat) 0 := by
  sorry
