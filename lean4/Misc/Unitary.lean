import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.UnitaryGroup

-- open Nat Finset Real

-- def m0 := Matrix.zero -- Matrix.of (fun _ _ ↦ 0)

def m : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of (fun (m n : Fin 3) ↦ if m = n then 1 else 0.5)
def m0 := m - m -- Matrix.of (fun _ _ ↦ 0)

#check m
-- #eval m
#eval (1 : Fin 2)
#eval m0 (0 : Fin 2) (1 : Fin 2)
#eval m (0 : Fin 2) (1 : Fin 2)

#eval m.det
