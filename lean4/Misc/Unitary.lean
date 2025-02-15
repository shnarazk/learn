import Mathlib.Tactic
/-
https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Data/Matrix/Basic.lean
 - 基本属性、転置など
-/
import Mathlib.Data.Matrix.Basic

/- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Data/Matrix/ConjTranspose.lean
- 随伴行列
 -/
import Mathlib.Data.Matrix.ConjTranspose

/- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/LinearAlgebra/Matrix/Basis.lean
- ベクトルと行列の関係など
-/
import Mathlib.LinearAlgebra.Matrix.Basis

/-- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean
- 逆行列A⁻¹の定義
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

-- 存在していない
-- import Mathlib.LinearAlgebra.Matrix.Unitary

/-- ユニタリ群の定義 -/
import Mathlib.LinearAlgebra.UnitaryGroup

/-- Real as Cauchy sequence -/
import Mathlib.Data.Real.Basic

-- open Nat Finset Real

/- `!`がベクターの、`!!`が配列の即値形式 -/
def m1 :=!![(0.0 : ℝ), 1, 0; 1, 1, 0; 0, 0, 1]
#check m1.det.cauchy.unquot.val
#eval m1.det.cauchy.unquot.val 10
-- #eval (repr (0 : ℝ)).cauchy

-- def m0 := Matrix.zero -- Matrix.of (fun _ _ ↦ 0)

def m : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of (fun (m n : Fin 3) ↦ if m = n then 1 else 0.5)
-- zeroがあるはずなのだがよくわからない
def m0 := m - m -- Matrix.of (fun _ _ ↦ 0)

#check m
-- #eval m
#eval (1 : Fin 2)

/- 実数はCauchy列として定義されているので、それっぽく表示するには皮を剥がないといけない -/
#eval m0 (0 : Fin 2) (1 : Fin 2) |>.cauchy.unquot.val 10
#eval m (0 : Fin 2) (1 : Fin 2) |>.cauchy.unquot.val 10

#eval m.det

open Matrix

/- ここから先はcopilotに聞きつつ進める -/

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
-- variable {R : Type*} [CommRing R] [IsDomain R] [StarRing R]

-- Define a unitary matrix on ℝ
def is_unitary (A : Matrix m m ℝ) : Prop := A * Aᴴ = 1

example (A : Matrix m m ℝ) : is_unitary A → A.det = 1 := by
  rintro h
  dsimp [is_unitary, conjTranspose] at h
  simp [Matrix.det]

  sorry
