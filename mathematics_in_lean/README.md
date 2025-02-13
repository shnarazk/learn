# Study [Mathematics in Lean](https://github.com/leanprover-community/mathematics_in_lean)

## 8
- The type of morphisms between monoids M and N is called `MonoidHom M N` and written `M →* N`.
- `inferInstance`
- `trivial`
- `suffices` ?

## 9
- `eaval` tactics?
- `![,]` -- concrete vector
- `!![,;]` -- concrete matrix
- `fin_cases` tactics

## 10
- `choose` tactics
- When both X and Y are R, `Tendsto f (N x₀0) (N y₀0)` is equivalent to the
familiar notion $$lim_{x→x_0} f(x) = y_0$$.


---
# patches to the repository

## 4.10rc2 against [df66203](https://github.com/leanprover-community/mathematics_in_lean/commit/df662034d2d23aa6aaf61dfd9ef53f7a852096cf)

```diff
diff --git a/mathematics_in_lean/MIL/C05_Elementary_Number_Theory/S01_Irrational_Roo
ts.lean b/mathematics_in_lean/MIL/C05_Elementary_Number_Theory/S01_Irrational_Roots.
lean
index 437a723..a6a75d7 100644
--- a/mathematics_in_lean/MIL/C05_Elementary_Number_Theory/S01_Irrational_Roots.lean
+++ b/mathematics_in_lean/MIL/C05_Elementary_Number_Theory/S01_Irrational_Roots.lean
@@ -110,9 +110,9 @@ example {m n p : ℕ} (coprime_mn : m.Coprime n) (prime_p : p.Prim
e) : m ^ 2 ≠
   exact absurd this step5
 #check Nat.factors
-#check Nat.prime_of_mem_factors
-#check Nat.prod_factors
-#check Nat.factors_unique
+#check Nat.prime_of_mem_primeFactorsList
+#check Nat.prod_primeFactorsList
+#check Nat.primeFactorsList_unique
 theorem factorization_mul' {m n : ℕ} (mnez : m ≠ 0) (nnez : n ≠ 0) (p : ℕ) :
     (m * n).factorization p = m.factorization p + n.factorization p := by
```
-------

## Obsoluted patches

### 4.10
```diff
diff --git a/mathematics_in_lean/MIL/C05_Elementary_Number_Theory/S01_Irrational_Roots.lean b/mathematics_in_lean/MIL/C05_Elementary_Number_Theory/S01_Irrational_Roots.lean
index 3fca006..437a723 100644
--- a/mathematics_in_lean/MIL/C05_Elementary_Number_Theory/S01_Irrational_Roots.lean
+++ b/mathematics_in_lean/MIL/C05_Elementary_Number_Theory/S01_Irrational_Roots.lean
@@ -1,6 +1,6 @@
 import MIL.Common
 import Mathlib.Data.Nat.Factorization.Basic
-import Mathlib.Data.Nat.Prime
+import Mathlib.Data.Nat.Prime.Defs

 #print Nat.Coprime

diff --git a/mathematics_in_lean/MIL/C03_Logic/S04_Conjunction_and_Iff.lean b/mathematics_in_lean/MIL/C03_Logic/S04_Conjunction_and_Iff.lean
index 5327aea..7764f93 100644
--- a/mathematics_in_lean/MIL/C03_Logic/S04_Conjunction_and_Iff.lean
+++ b/mathematics_in_lean/MIL/C03_Logic/S04_Conjunction_and_Iff.lean
@@ -1,6 +1,6 @@
 import MIL.Common
 import Mathlib.Data.Real.Basic
-import Mathlib.Data.Nat.Prime
+import Mathlib.Data.Nat.Prime.Defs

 namespace C03S04

diff --git a/mathematics_in_lean/MIL/C04_Sets_and_Functions/S01_Sets.lean b/mathematics_in_lean/MIL/C04_Sets_and_Functions/S01_Sets.lean
index f1e5233..fea4d75 100644
--- a/mathematics_in_lean/MIL/C04_Sets_and_Functions/S01_Sets.lean
+++ b/mathematics_in_lean/MIL/C04_Sets_and_Functions/S01_Sets.lean
@@ -1,5 +1,5 @@
 import Mathlib.Data.Set.Lattice
-import Mathlib.Data.Nat.Prime
+import Mathlib.Data.Nat.Prime.Defs
 import MIL.Common

 section
diff --git a/mathematics_in_lean/MIL/C05_Elementary_Number_Theory/S01_Irrational_Roots.lean b/mathematics_in_lean/MIL/C05_Elementary_Number_Theory/S01_Irrational_Roots.lean
index 3fca006..437a723 100644
--- a/mathematics_in_lean/MIL/C05_Elementary_Number_Theory/S01_Irrational_Roots.lean
+++ b/mathematics_in_lean/MIL/C05_Elementary_Number_Theory/S01_Irrational_Roots.lean
@@ -1,6 +1,6 @@
 import MIL.Common
 import Mathlib.Data.Nat.Factorization.Basic
-import Mathlib.Data.Nat.Prime
+import Mathlib.Data.Nat.Prime.Defs

 #print Nat.Coprime

diff --git a/mathematics_in_lean/MIL/C05_Elementary_Number_Theory/S03_Infinitely_Many_Primes.lean b/mathematics_in_lean/MIL/C05_Elementary_Number_Theory/S03_Infinitely_Many_Primes.lean
index 90f5f6c..816c82a 100644
--- a/mathematics_in_lean/MIL/C05_Elementary_Number_Theory/S03_Infinitely_Many_Primes.lean
+++ b/mathematics_in_lean/MIL/C05_Elementary_Number_Theory/S03_Infinitely_Many_Primes.lean
@@ -1,4 +1,4 @@
-import Mathlib.Data.Nat.Prime
+import Mathlib.Data.Nat.Prime.Defs
 -- import Mathlib.Algebra.BigOperators.Basic
 import MIL.Common
 ```

 ### 4.9.0

 ```diff
 diff --git a/mathematics_in_lean/MIL/C08_Groups_and_Rings/S01_Groups.lean b/mathematics_in_lean/MIL/C08_Groups_and_Ring
s/S01_Groups.lean
index f609a76..29ceee5 100644
--- a/mathematics_in_lean/MIL/C08_Groups_and_Rings/S01_Groups.lean
+++ b/mathematics_in_lean/MIL/C08_Groups_and_Rings/S01_Groups.lean
@@ -274,7 +274,7 @@ open MonoidHom
 #check Nat.eq_of_mul_eq_mul_right

 -- The following line is working around a Lean bug that will be fixed very soon.
-attribute [-instance] Subtype.instInhabited
+-- attribute [-instance] Subtype.instInhabited

 lemma aux_card_eq [Fintype G] (h' : card G = card H * card K) : card (G ⧸ H) = card K := by
   sorry
```
