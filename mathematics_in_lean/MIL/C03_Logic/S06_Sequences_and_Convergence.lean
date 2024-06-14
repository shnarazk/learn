import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext  -- congrにはできない
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr  -- extにはできない, extは関数を「展開」するもの
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun _x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n _nge
  rw [sub_self, abs_zero]
  apply εpos

/-
  use:
   - le_of_max_le_left: max a b ≤ c → a ≤ c
   - le_of_max_le_right: max a b ≤ c → b ≤ c
   - norm_num to convert ε / 2 + ε / 2 = ε
   - congr to convert |s n + t n - (a + b)|
-/
theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro Nst P
  have P' : max Ns Nt ≤ Nst := P
  have hs0 : |s Nst - a| < ε / 2 := hs Nst (le_of_max_le_left P')
  have ht0 : |t Nst - b| < ε / 2 := ht Nst (le_of_max_le_right P')
  have Q : |s Nst + t Nst - (a + b)| ≤ |s Nst - a| + |t Nst - b| := by
    calc
      |s Nst + t Nst - (a + b)| = |s Nst + t Nst - a - b| := by ring_nf
      _ = |(s Nst - a) + (t Nst - b)| := by ring_nf
      _ ≤ |s Nst - a| + |t Nst - b| := abs_add (s Nst - a) (t Nst - b)
  have R :|s Nst - a| + |t Nst - b| < ε := by
    calc
     |s Nst - a| + |t Nst - b| < ε / 2 + ε / 2 := by apply add_lt_add hs0 ht0
      _ = ε := by linarith
  exact lt_of_le_of_lt Q R


theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε P
  dsimp
  have E0 : ε / |c| > 0 := by exact div_pos P acpos
  rcases cs (ε / |c|) E0 with ⟨N0, h1⟩
  use N0
  intro N NP
  rw [← mul_sub c _ _, abs_mul]
  apply (lt_div_iff' acpos).mp
  exact h1 N NP


theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n Nn
  have Q : |s n| ≤ |-a| + |- a + s n| := abs_add' (s n) (-a)
  calc
    |s n| ≤ |-a| + |-a + s n| := Q
    _ = |-a + s n| + |-a| := by rw [add_comm]
    _ = |s n + - a| + |-a| := by rw [add_comm (-a) (s n)]
    _ = |s n - a| + |-a| := by rw [@Mathlib.Tactic.RingNF.add_neg]
    _ = |s n - a| + |a| := by rw [abs_neg]
    _ < 1 + |a| := by exact (add_lt_add_iff_right |a|).mpr (h n Nn)
    _ = |a| + 1 := by rw [add_comm]
  done


theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro N NN
  have Nl : N₀ ≤ N := le_of_max_le_left NN
  have Nr : N₁ ≤ N := le_of_max_le_right NN
  have P : |s N| < B := h₀ N Nl
  have Q : |t N - 0| < ε / B := h₁ N Nr
  have Bnn : B ≠ 0 := by exact Ne.symm (ne_of_lt Bpos)
  calc
    |s N * t N - 0| = |s N * t N| := by rw [sub_zero (s N * t N)]
    _ ≤ |s N| * |t N| := by rw [abs_mul]
    _ = |s N| * |t N - 0| := by rw [sub_zero (t N)]
    _ < B * (ε / B) := by refine mul_lt_mul'' P Q (abs_nonneg _) (abs_nonneg _)
    _ = ε := mul_div_cancel₀ ε Bnn
  done

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by sorry
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by sorry
  have absb : |s N - b| < ε := by sorry
  have : |a - b| < |a - b| := by sorry
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
