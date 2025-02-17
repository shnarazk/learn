# Study [Mathematics in Lean](https://github.com/leanprover-community/mathematics_in_lean)
## 3

- The pattern of unpacking an equation inside an existential quantifier and then using it to rewrite an expression in the goal comes up often, so much so that the rcases tactic provides an abbreviation: if you use the keyword rfl in place of a new identifier, rcases does the rewriting automatically (this trick doesn’t work with pattern-matching lambdas).
- field_simp
- It is often tedious to work with compound statements with a negation in front, and it is a common mathematical pattern to replace such statements with equivalent forms in which the negation has been pushed inward. To facilitate this, Mathlib offers a push_neg tactic, which restates the goal in this way.
- we use dsimp to expand the definitions of FnHasUb and FnUb. (We need to use dsimp rather
than rw to expand FnUb, because it appears in the scope of a quantifier.)
- Using contrapose! instead of contrapose applies push_neg to the goal and the relevant hypothesis as well.
- The [`exfalso`](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#exfalso) tactic replaces the current goal with the goal of proving False. Given h : P and h' : ¬ P, the term absurd h h' establishes any proposition.
- the `contradiction` tactic tries to close a goal by finding a contradiction in the hypotheses, such as a pair of the form h : P and h' : ¬ P.
- the `assumption` tactic tells Lean to find an assumption that will solve the goal.
- To prove an if-and-only-if statement, you can use `constructor` or angle brackets, just as you would if you were proving a conjunction.
- Sometimes in a proof we want to split on cases depending on whether some statement is true or not. For any proposition P, we can use `em P : P ∨ ¬ P`. The name em is short for “excluded middle.”
- The `ext` tactic enables us to prove an equation between functions by proving that their values are the same at all the values of their arguments.
- the `congr` tactic allows us to prove an equation between two expressions by reconciling the parts that are different:
- the `convert` tactic is used to apply a theorem to a goal when the conclusion of the theorem doesn’t quite match.

## 4
- If f : α → β is a function and p is a set of elements of type β, the library defines preimage f p, written `f ¹' p`, to be {x | f x ∈ p}.
- `wlog` tactic

## 5
- Another strategy is to use the tactic `interval_cases`, which automatically splits the goal into cases when the variable in question is contained in an interval of natural numbers or integers.
- `decide` tactic
- `revert` tactic
- Here, ordinary induction isn’t enough. We want to use strong induction, which allows us to prove that every natural number n has a property P by showing that for every number n, if P holds of all values less than n, it holds at n as well. In Lean, this principle is called `Nat.strong_induction_on`, and we can use the `using` keyword to tell the induction tactic to use it.
- `by_cases np : n.Prime` -- n.Primeが成立する場合としない場合に分割
- [`refine'`](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#refine___) tactic
- Reasoning about finite sets computationally requires having a procedure to test equality
on α, which is why the snippet below includes the assumption `[DecidableEq α]`.
- the `tauto` tactic (and a strengthened version, `tauto!`, which uses classical logic) can be
used to dispense with propositional tautologies.
- `m | n` -- nがmで割れるかどうか

## 6
- The `@[ext]` annotation tells Lean to automatically generate theorems that can be used
    to prove that two instances of a structure are equal when their components are equal,
    a property known as extensionality.
- we use the `protected` keyword so that the name of the theorem is Point.add_comm,
    even when the namespace is open.
- nontrivial types are types with at least two distinct elements.
- A nonzero element a is said to be **irreducible** if it cannot be written in the
    form a = bc where neither b nor c is a unit.
- 集合 S とその上の二項演算 • : S × S → S の対 (S, • ) が結合律（結合法則）を満たすとき、
    これを半群という。S を半群 (S, •) の台集合とよぶ。
- `whatsnew` command

## 7
- But the diamond we created with modules is definitely bad. The offending piece is the
    smul field which is data, not a proof, and we have two constructions that are not
    definitionally equal. The robust way of fixing this issue is to make sure that going
    from a rich structure to a poor structure is always done by forgetting data, not by
    defining data. This well-known pattern as been named "**forgetful inheritance**” and
    extensively discussed in https://inria.hal.science/hal-02463336.

## 8
- The type of morphisms between monoids M and N is called `MonoidHom M N` and written `M →* N`.
- `inferInstance`
- `trivial`
- `suffices` ?

## 9
- `eaval` tactic?
- `![,]` -- concrete vector
- `!![,;]` -- concrete matrix
- `fin_cases` tactic

## 10
- `choose` tactic
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
