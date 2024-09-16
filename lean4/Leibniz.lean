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

