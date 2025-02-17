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
    - K • V → V が以下を満たす: Rに関する分配法則、Vに関する分配法則、結合法則, Rの単位元は(•)の単位元
-/
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-
- AddZeroClass V:
- DistribSMul K V:
-/
example (a : K) (u v : V) : a • (u + v) = a • u + a • v :=
  smul_add a u v
