# Study [Mathematics in Lean](https://github.com/leanprover-community/mathematics_in_lean)

# patches to the repository

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
