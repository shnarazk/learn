import MIL.Common
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic

#print Nat.Coprime

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 :=
  h

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 := by
  rw [Nat.Coprime] at h
  exact h

example : Nat.Coprime 12 7 := by norm_num

example : Nat.gcd 12 8 = 4 := by norm_num

#check Nat.prime_def_lt

example (p : ℕ) (prime_p : Nat.Prime p) : 2 ≤ p ∧ ∀ m : ℕ, m < p → m ∣ p → m = 1 := by
  rwa [Nat.prime_def_lt] at prime_p

#check Nat.Prime.eq_one_or_self_of_dvd

example (p : ℕ) (prime_p : Nat.Prime p) : ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p :=
  prime_p.eq_one_or_self_of_dvd

example : Nat.Prime 17 := by norm_num

-- commonly used
example : Nat.Prime 2 :=
  Nat.prime_two

example : Nat.Prime 3 :=
  Nat.prime_three

#check Nat.Prime.dvd_mul
#check Nat.Prime.dvd_mul Nat.prime_two
#check Nat.prime_two.dvd_mul

theorem even_of_even_sqr {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  cases h <;> assumption

example {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m :=
  Nat.Prime.dvd_of_dvd_pow Nat.prime_two h

example (a b c : Nat) (h : a * b = a * c) (h' : a ≠ 0) : b = c :=
  -- apply? suggests the following:
  (mul_right_inj' h').mp h

/-
  Use `even_of_even_sqr` and `Nat.dvd_gcd`
  - `even_of_even_sqr : 2 ∣ m ^ 2 = 2 ∣ m`
-/
example {m n : ℕ} (coprime_mn : m.Coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq
  have step1 : 2 ∣ m := by
    have tmp1 : 2 ∣ 2 * n ^ 2 := by exact Nat.dvd_mul_right 2 (n ^ 2)
    rw [← sqr_eq] at tmp1
    apply Nat.Prime.dvd_of_dvd_pow Nat.prime_two tmp1
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp step1
  have step2 : 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have step2 : 2 * k ^ 2 = n ^ 2 := by
    have two_neq_zero : 2 ≠ 0 := by exact Ne.symm (Nat.zero_ne_add_one 1)
    rw [meq] at sqr_eq
    apply (mul_right_inj' two_neq_zero).mp at step2
    exact step2
  have step3 : 2 ∣ n := by
    have tmp2 : 2 ∣ 2 * k ^ 2 := Nat.dvd_mul_right 2 (k ^ 2)
    rw [step2] at tmp2
    exact even_of_even_sqr tmp2
  have step4 : 2 ∣ m.gcd n := by
    exact Nat.dvd_gcd step1 step3
  have : 2 ∣ 1 := by
    have tmp3 : m.gcd n = 1 := coprime_mn
    rw [tmp3] at step4
    exact step4
  norm_num at this

example {m n p : ℕ} (coprime_mn : m.Coprime n) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have step1 : p ∣ m := by
    have tmp1 : p ∣ p * n ^ 2 := by exact Nat.dvd_mul_right p (n ^ 2)
    rw [← sqr_eq] at tmp1
    apply Nat.Prime.dvd_of_dvd_pow prime_p tmp1
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp step1
  have step2 : p * (p * k ^ 2) = p * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have step2 : p * k ^ 2 = n ^ 2 := by
    have p_neq_zero : p ≠ 0 := by exact Nat.Prime.ne_zero prime_p
    rw [meq] at sqr_eq
    apply (mul_right_inj' p_neq_zero).mp at step2
    exact step2
  have step3 : p ∣ n := by
    have tmp2 : p ∣ p * k ^ 2 := Nat.dvd_mul_right p (k ^ 2)
    rw [step2] at tmp2
    exact Nat.Prime.dvd_of_dvd_pow prime_p tmp2
  have step4 : p ∣ m.gcd n := by
    exact Nat.dvd_gcd step1 step3
  have : p ∣ 1 := by
    have tmp3 : m.gcd n = 1 := coprime_mn
    rw [tmp3] at step4
    exact step4
  norm_num at this
  have step5 : ¬p = 1 := by exact (Nat.Prime.ne_one prime_p)
  exact absurd this step5

#check Nat.factors
#check Nat.prime_of_mem_primeFactorsList
#check Nat.prod_primeFactorsList
#check Nat.primeFactorsList_unique

theorem factorization_mul' {m n : ℕ} (mnez : m ≠ 0) (nnez : n ≠ 0) (p : ℕ) :
    (m * n).factorization p = m.factorization p + n.factorization p := by
  rw [Nat.factorization_mul mnez nnez]
  rfl

theorem factorization_pow' (n k p : ℕ) :
    (n ^ k).factorization p = k * n.factorization p := by
  rw [Nat.factorization_pow]
  rfl

theorem Nat.Prime.factorization' {p : ℕ} (prime_p : p.Prime) :
    p.factorization p = 1 := by
  rw [prime_p.factorization]
  simp

example {m n p : ℕ} (nnz : n ≠ 0) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have nsqr_nez : n ^ 2 ≠ 0 := by simpa
  have eq1 : Nat.factorization (m ^ 2) p = 2 * m.factorization p := by
    exact factorization_pow' m 2 p
  have eq2 : (p * n ^ 2).factorization p = 2 * n.factorization p + 1 := by
    rw [factorization_mul' (Nat.Prime.ne_zero prime_p) nsqr_nez p]
    rw [Nat.Prime.factorization' prime_p, factorization_pow' n 2 p]
    exact Nat.add_comm 1 _
  have : 2 * m.factorization p % 2 = (2 * n.factorization p + 1) % 2 := by
    rw [← eq1, sqr_eq, eq2]
  rw [add_comm, Nat.add_mul_mod_self_left, Nat.mul_mod_right] at this
  norm_num at this

example {m n k r : ℕ} (nnz : n ≠ 0) (pow_eq : m ^ k = r * n ^ k) {p : ℕ} :
    k ∣ r.factorization p := by
  rcases r with _ | r
  · simp
  have npow_nz : n ^ k ≠ 0 := fun npowz ↦ nnz (pow_eq_zero npowz)
  have eq1 : (m ^ k).factorization p = k * m.factorization p := by
    rw [factorization_pow' m _ _]
  have eq2 : ((r + 1) * n ^ k).factorization p =
      k * n.factorization p + (r + 1).factorization p := by
    rw [factorization_mul' (Ne.symm (Nat.zero_ne_add_one r)) _ _]
    rw [factorization_pow' n k _]
    -- rw [Nat.succ_eq_add_one]
    rw [add_comm ((r + 1).factorization p) (k * n.factorization p)]
    exact npow_nz
  have : r.succ.factorization p = k * m.factorization p - k * n.factorization p := by
    rw [← eq1, pow_eq, eq2, add_comm, Nat.add_sub_cancel]
  rw [this]
  /-
    Use below here
    - `Nat.dvd_sub (_ : m ≤ n) (_ : k ∣ m) (_ : k ∣ n) : k ∣ m - n`
    - `Nat.dvd_mul_right (a b : ℕ) : a ∣ a * b`
    この時点でeq1, eq2も使っている
  -/
  apply Nat.dvd_sub
  rw [← factorization_pow' n k p, ← factorization_pow' m k p]
  rw [pow_eq]
  rw [factorization_mul']
  simp
  have : r.succ ≠ 0 := by exact Nat.succ_ne_zero r
  rw [← Nat.succ_eq_add_one]
  . exact this
  . exact npow_nz
  . exact Nat.dvd_mul_right k (m.factorization p)
  . exact Nat.dvd_mul_right k (n.factorization p)

#check multiplicity
