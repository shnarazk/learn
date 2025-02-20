import Mathlib.Tactic

/-
- Field(体): 加法と乗法を持ち、以下を満たすもの
    - 加法についての閉包, 単位元、逆元
    - 乗法における単位減、逆元
    - 加法と乗法の結合法則、交換法則、分配法則、
- AddCommGroup(加法交換群, 加法群):
    - 加法に関する群(閉包、結合法則、単位減、逆元)である
    - 交換法則を満たす(= アーベル群, Abelian group)
    - 単位元、逆元
- Module K V (加群): 環K, アーベル群Vに対して
    - K • V → V が以下を満たす: Rに関する分配法則、Vに関する分配法則と結合法則, Rの単位元は(•)の単位元
    ※ 環に乗法単位元、乗法逆元、乗法交換法則を加えたものが体
-/
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]


-- 齋藤正彦、線形代数入門、東京大学出版会が手元にあるので、合わせてみたい　--
/-
- AddZeroClass V:
- DistribSMul K V:
-/
example (a : K) (u v : V) : a • (u + v) = a • u + a • v :=
  smul_add a u v

open Matrix

/- ベクトルは添字からの関数である! -/
#check ![(3 : ℝ), 2, 2] --  (![(0 : ℤ), 1] + ![1, 2])
#check (!![1, 2; 3, 4] *ᵥ ![1, 1])

example (a : ℝ) (u v : Fin 2 → ℝ) : a • (u + v) = a • u + a • v := by
  exact smul_add a u v

-- ℝⁿ が線型空間であることを証明するのは簡単 --
noncomputable example : Field ℝ := inferInstance
noncomputable example : AddCommGroup (Fin 2 → ℝ) := inferInstance
noncomputable example : Module ℝ (Fin 2 → ℝ) := inferInstance
