import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  . rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h


example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  { rw [abs_of_nonneg h] }
  { rw [abs_of_neg h] ; linarith }

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  { rw [abs_of_nonneg h] ; linarith }
  { rw [abs_of_neg h]}

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 x with hx | hx
  {
    rcases le_or_gt 0 y with hy | hy
    { rw [abs_of_nonneg hx, abs_of_nonneg hy, abs_of_nonneg] ; linarith }
    {
      rcases le_or_gt 0 (x+y) with hxy | hxy
      { rw [abs_of_nonneg hx, abs_of_neg hy, abs_of_nonneg hxy]; linarith }
      { rw [abs_of_nonneg hx, abs_of_neg hy, abs_of_neg hxy] ; linarith }
    }
  }
  {
    rcases le_or_gt 0 y with hy | hy
    {
      rcases le_or_gt 0 (x+y) with hxy | hxy
      { rw [abs_of_neg hx, abs_of_nonneg hy, abs_of_nonneg hxy]; linarith }
      { rw [abs_of_neg hx, abs_of_nonneg hy, abs_of_neg hxy] ; linarith }
    }
    { rw [abs_of_neg hx, abs_of_neg hy, abs_of_neg] ; linarith ; linarith }
  }

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  {
    rcases le_or_gt 0 y with hy | hy
    { rw [abs_of_nonneg hy] ; intro xy ; left; exact xy }
    { rw [abs_of_neg hy] ; intro xy ; right; exact xy }
  }
  {
    rcases le_or_gt 0 y with hy | hy
    { rw [abs_of_nonneg hy]
      intro xy
      rcases xy with h1 | h2
      { exact h1 }
      { linarith }
    }
    { rw [abs_of_neg hy]
      intro xy
      rcases xy with h1 | h2
      { linarith }
      { exact h2 }
    }
  }

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  {
    rcases le_or_gt 0 x with hx | hx
    {
      rw [abs_of_nonneg hx]
      intro XY
      constructor
      { linarith }
      { exact XY }
      done
    }
    {
      rw [abs_of_neg hx]
      intro xy
      constructor
      { linarith }
      { linarith }
    }
  }
  {
    rcases le_or_gt 0 x with hx | hx
    {
      rw [abs_of_nonneg hx]
      intro XY
      exact XY.right
    }
    {
      rw [abs_of_neg hx]
      rintro ⟨xy1, _⟩
      linarith
    }
  }

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  . right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  . rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x,y,rfl | rfl⟩ <;> linarith [pow_two_nonneg x, pow_two_nonneg y]
  -- rcases h with ⟨x, h1⟩; rcases h1 with ⟨y, h2⟩; rcases h2 with h3 | h3; rw h3]; linarith [pow_two_nonneg x, pow_two_nonneg y]; rw [h3]; linarith [pow_two_nonneg x, pow_two_nonneg y]

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h1 : (x - 1) * (x + 1) = 0 := by linarith
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h1 with h2 | h2
  { left; linarith }
  { right; linarith }

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h1 : (x - y) * (x + y) = 0 := by linarith
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h1 with h2 | h2
  { left ; linarith }
  { right ; linarith }

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h0 : (1 : R) = 1 ^ 2 := by ring
  rw [h0] at h
  apply eq_or_eq_neg_of_sq_eq_sq x 1 at h
  rcases h with h1 | h1
  { left; exact h1 }
  { right; exact h1 }

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  apply eq_or_eq_neg_of_sq_eq_sq x y at h
  rcases h with h1 | h1
  { left; exact h1 }
  { right; exact h1 }

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  . contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  intro h
  { by_cases h1 : P
    { right ; exact h h1 }
    { left ; assumption }
  }
  { intro PQ P0
    rcases PQ with h1 | h2
    . contradiction
    . assumption
  }
