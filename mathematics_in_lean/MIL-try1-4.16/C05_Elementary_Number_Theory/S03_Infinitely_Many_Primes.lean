import Mathlib.Data.Nat.Prime.Basic
import MIL.Common

open BigOperators

namespace C05S03

theorem two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  cases m; contradiction
  case succ m =>
    cases m; contradiction
    repeat' apply Nat.succ_le_succ
    apply zero_le

example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  interval_cases m <;> contradiction

example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  revert h0 h1
  revert h m
  decide

theorem exists_prime_factor {n : Nat} (h : 2 ≤ n) : ∃ p : Nat, p.Prime ∧ p ∣ n := by
  by_cases np : n.Prime
  · use n, np
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np h with ⟨m, mltn, mdvdn, mne1⟩
  have : m ≠ 0 := by
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have mgt2 : 2 ≤ m := two_le this mne1
  by_cases mp : m.Prime
  · use m, mp
  · rcases ih m mltn mgt2 mp with ⟨p, pp, pdvd⟩
    use p, pp
    apply pdvd.trans mdvdn

theorem primes_infinite : ∀ n, ∃ p > n, Nat.Prime p := by
  intro n
  have : 2 ≤ Nat.factorial (n + 1) + 1 := by
    have sub : 1 ≤ Nat.factorial (n + 1) := by
      induction' n with n0 ih
      { simp }
      {
        have fact_ord : Nat.factorial (n0 + 1) ≤ Nat.factorial (n0 + 2) := by
          refine Nat.factorial_le ?h
          exact Nat.le_add_right (n0 + 1) 1
        exact le_trans ih fact_ord
      }
    simp
    exact sub
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  -- refine' ⟨p, _, pp⟩
  use p
  refine ⟨?h.left, pp⟩
  show p > n
  by_contra ple
  push_neg at ple
  have : p ∣ Nat.factorial (n + 1) := by
    have p_pos : 0 < p := by exact Nat.Prime.pos pp
    have ple1 : p ≤ n + 1 := by exact Nat.le_add_right_of_le ple
    apply Nat.dvd_factorial p_pos ple1
  have : p ∣ 1 := by
    exact (Nat.dvd_add_iff_right this).mpr pdvd
  show False
  rw [@Nat.dvd_one] at this
  apply Nat.Prime.ne_one at this
  { exact this }
  { exact pp }

open Finset

section
variable {α : Type*} [DecidableEq α] (r s t : Finset α)

example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
  rw [subset_iff]
  intro x
  rw [mem_inter, mem_union, mem_union, mem_inter, mem_inter]
  tauto

example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
  simp [subset_iff]
  intro x
  tauto

example : r ∩ s ∪ r ∩ t ⊆ r ∩ (s ∪ t) := by
  simp [subset_iff]
  intro x
  tauto

example : r ∩ s ∪ r ∩ t = r ∩ (s ∪ t) := by
  ext x
  simp
  tauto

end

section
variable {α : Type*} [DecidableEq α] (r s t : Finset α)

example : (r ∪ s) ∩ (r ∪ t) = r ∪ s ∩ t := by
  ext x
  simp
  tauto

example : (r \ s) \ t = r \ (s ∪ t) := by
  ext x
  simp
  tauto

end

example (s : Finset ℕ) (n : ℕ) (h : n ∈ s) : n ∣ ∏ i in s, i :=
  Finset.dvd_prod_of_mem _ h

theorem _root_.Nat.Prime.eq_of_dvd_of_prime {p q : ℕ}
      (prime_p : Nat.Prime p) (prime_q : Nat.Prime q) (h : p ∣ q) :
    p = q := by
  by_contra contra
  apply Nat.Prime.eq_one_or_self_of_dvd at h
  { rcases h with h1 | ih
    { exact absurd h1 (by exact Nat.Prime.ne_one prime_p) }
    { exact absurd ih contra }
  }
  { exact prime_q }

theorem mem_of_dvd_prod_primes {s : Finset ℕ} {p : ℕ} (prime_p : p.Prime) :
    (∀ n ∈ s, Nat.Prime n) → (p ∣ ∏ n in s, n) → p ∈ s := by
  intro h₀ h₁
  induction' s using Finset.induction_on with a s ans ih
  · simp at h₁
    linarith [prime_p.two_le]
  simp [Finset.prod_insert ans, prime_p.dvd_mul] at h₀ h₁
  rw [mem_insert]
  rcases h₀ with ⟨h0, h1⟩
  rcases ih h1 with ih₀
  rcases h₁ with h₁₀ | h₁₁
  { left ; exact _root_.Nat.Prime.eq_of_dvd_of_prime prime_p h0 h₁₀ }
  { right ; exact ih₀ h₁₁ }

example (s : Finset ℕ) (x : ℕ) : x ∈ s.filter Nat.Prime ↔ x ∈ s ∧ x.Prime :=
  mem_filter

theorem primes_infinite' : ∀ s : Finset Nat, ∃ p, Nat.Prime p ∧ p ∉ s := by
  intro s
  by_contra h
  push_neg  at h
  set s' := s.filter Nat.Prime with s'_def
  have mem_s' : ∀ {n : ℕ}, n ∈ s' ↔ n.Prime := by
    intro n
    simp [s'_def]
    apply h
  have : 2 ≤ (∏ i in s', i) + 1 := by
    have s'1 : ∀ i ∈ s', 1 ≤ i := by
      have s2 : ∀ k ∈ s', k.Prime := by
        intros k' ks
        simp [mem_s'] at ks  -- なんだこれは?
        exact ks
      intros j ji
      simp [mem_s'] at s2 ji
      exact Nat.Prime.one_le ji
    have y : (∏ i in s', 1) ≤ (∏ i in s', i) := by exact prod_le_prod' s'1
    simp at y
    ring_nf
    exact Nat.sub_le_iff_le_add'.mp y
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  have : p ∣ ∏ i in s', i := by
    have p_in_s' : p ∈ s' := by
      apply mem_s'.mpr
      exact pp
    exact dvd_prod_of_mem (fun i ↦ i) p_in_s'
  have : p ∣ 1 := by
    convert Nat.dvd_sub' pdvd this
    simp
  show False
  rw [Nat.dvd_one] at this
  apply Nat.Prime.ne_one at pp
  exact absurd this pp

theorem bounded_of_ex_finset (Q : ℕ → Prop) :
    (∃ s : Finset ℕ, ∀ k, Q k → k ∈ s) → ∃ n, ∀ k, Q k → k < n := by
  rintro ⟨s, hs⟩
  use s.sup id + 1
  intro k Qk
  apply Nat.lt_succ_of_le
  show id k ≤ s.sup id
  apply le_sup (hs k Qk)

theorem ex_finset_of_bounded (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  rintro ⟨n, hn⟩
  use (range (n + 1)).filter Q
  intro k
  simp [Nat.lt_succ_iff]
  exact hn k

example : 27 % 4 = 3 := by norm_num

example (n : ℕ) : (4 * n + 3) % 4 = 3 := by
  rw [add_comm, Nat.add_mul_mod_self_left]

theorem mod_4_eq_3_or_mod_4_eq_3 {m n : ℕ} (h : m * n % 4 = 3) : m % 4 = 3 ∨ n % 4 = 3 := by
  revert h
  rw [Nat.mul_mod]
  have : m % 4 < 4 := Nat.mod_lt m (by norm_num)
  interval_cases m % 4 <;> simp [-Nat.mul_mod_mod]
  have : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  interval_cases n % 4 <;> simp

theorem two_le_of_mod_4_eq_3 {n : ℕ} (h : n % 4 = 3) : 2 ≤ n := by
  apply two_le <;>
    · intro neq
      rw [neq] at h
      norm_num at h

-- Use Nat.div_dvd_of_dvd and Nat.div_lt_self
theorem aux {m n : ℕ} (h₀ : m ∣ n) (h₁ : 2 ≤ m) (h₂ : m < n) : n / m ∣ n ∧ n / m < n := by
  constructor
  { exact Nat.div_dvd_of_dvd h₀ }
  { apply Nat.div_lt_self
    exact Nat.zero_lt_of_lt h₂
    exact h₁
   }

theorem exists_prime_factor_mod_4_eq_3 {n : Nat} (h : n % 4 = 3) :
    ∃ p : Nat, p.Prime ∧ p ∣ n ∧ p % 4 = 3 := by
  by_cases np : n.Prime
  · use n
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg  at np
  rcases np (two_le_of_mod_4_eq_3 h) with ⟨m, mltn, mdvdn, mne1⟩
  have mge2 : 2 ≤ m := by
    apply two_le _ mne1
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have neq : m * (n / m) = n := Nat.mul_div_cancel' mdvdn
  have : m % 4 = 3 ∨ n / m % 4 = 3 := by
    apply mod_4_eq_3_or_mod_4_eq_3
    rw [neq, h]
  rcases this with h1 | h1
  {
    by_cases mp : m.Prime
    { use m }
    {
      rcases ih m mltn h1 mp with ⟨p, pp, pm, p1⟩
      use p
      -- have : p ∣ n := by exact Nat.dvd_trans pm mdvdn
      exact ⟨pp, by exact Nat.dvd_trans pm mdvdn, p1⟩
    }
  }
  {
    by_cases mp : (n / m).Prime
    {
      use (n / m)
      exact ⟨mp, Nat.div_dvd_of_dvd mdvdn, h1⟩
    }
    {
      have zltn : 0 < n := by exact Nat.zero_lt_of_lt mltn
      have now : n / m < n := by exact Nat.div_lt_self zltn mge2
      rcases ih (n / m) now h1 mp with ⟨p, pp, pm, p1⟩
      use p
      have : n / m ∣ n := by exact Nat.div_dvd_of_dvd mdvdn
      -- have : p ∣ n := by exact Nat.dvd_trans pm this
      exact ⟨pp, by exact Nat.dvd_trans pm this, p1⟩
    }
  }

example (m n : ℕ) (s : Finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s := by
  rwa [mem_erase] at h  -- rwaはrwしてからassumptionを使う

example (m n : ℕ) (s : Finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s := by
  simp at h
  assumption

/-  Use them -/
#check Nat.dvd_add_iff_left
#check Nat.dvd_sub'

theorem primes_mod_4_eq_3_infinite : ∀ n, ∃ p > n, Nat.Prime p ∧ p % 4 = 3 := by
  by_contra h
  push_neg  at h
  rcases h with ⟨n, hn⟩
  have : ∃ s : Finset Nat, ∀ p : ℕ, p.Prime ∧ p % 4 = 3 ↔ p ∈ s := by
    apply ex_finset_of_bounded
    use n
    contrapose! hn
    rcases hn with ⟨p, ⟨pp, p4⟩, pltn⟩
    exact ⟨p, pltn, pp, p4⟩
  rcases this with ⟨s, hs⟩
  have h₁ : ((4 * ∏ i in erase s 3, i) + 3) % 4 = 3 := by
    -- have h₂ : (4 * ∏ i in erase s 3, i) % 4 = 0 := by
    --  exact Nat.mul_mod_right 4 (∏ i ∈ s.erase 3, i)
    rw [Nat.mul_add_mod]
  rcases exists_prime_factor_mod_4_eq_3 h₁ with ⟨p, pp, pdvd, p4eq⟩
  have ps : p ∈ s := by
    rcases hs p with pr
    exact pr.mp ⟨pp, p4eq⟩
  /- by_contra から導出できるかと思ったらnの取り扱いで袋小路　-/
  have pne3 : p ≠ 3 := by
    by_contra p3
    rw [p3] at pdvd
    rw [← Nat.dvd_add_iff_left (Nat.dvd_refl 3)] at pdvd
    rw [Nat.prime_three.dvd_mul] at pdvd
    norm_num at pdvd
    have : 3 ∈ s.erase 3 := by
      apply mem_of_dvd_prod_primes Nat.prime_three _ pdvd
      intro k
      simp [← hs k]
      exact fun _k_ne_3 a _k43 ↦ a
    simp at this
  have : p ∣ 4 * ∏ i in erase s 3, i := by
    have p4 : p ∈ erase s 3 := by exact mem_erase_of_ne_of_mem pne3 ps
    have p4' : p ∣ ∏ i in erase s 3, i := by exact dvd_prod_of_mem (fun i ↦ i) p4
    exact Dvd.dvd.mul_left p4' 4
  have : p ∣ 3 := by
    exact (Nat.dvd_add_iff_right this).mpr pdvd
  have : p = 3 := by
    rw [Nat.Prime.eq_of_dvd_of_prime pp Nat.prime_three this]
  contradiction
