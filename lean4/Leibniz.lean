import Mathlib.Tactic
open Nat

-- the most efficient vaviant
def leibniz₁ (n : Nat) (k: Float) (sum : Float) : Float :=
  match n with
  | zero => sum + 8 / 3
  | succ n' => leibniz₁ n' (k - 4) (sum + (8 / ((k + 1) * (k + 3))))

def leibniz₂ : Nat → Float
  | zero => 8 / 3
  | succ n' =>
      let k := (succ n').toFloat * 4
      leibniz₂ n' + 8 / ((k + 1) * (k + 3))

def leibniz (n : Nat) : Float := leibniz₁ n (n.toFloat * 4) 0
-- def leibniz (n : Nat) : Float := leibniz₂ n 0.0

def leibnizIO (n : Nat) : IO Float := do return leibniz n

#eval leibniz 1000

/-
-- This is the FUN part only on Lean4
-/
namespace this_is_pi_approximation
open Rat Finset

def leibniz₁R (n : Nat) (k: Rat) (sum : Rat) : Rat :=
  match n with
  | zero => sum + 8 / 3
  | succ n' => leibniz₁R n' (k - 4) (sum + (8 / ((k + 1) * (k + 3))))

def leibniz₂R : Nat → Rat
  | zero => 8 / 3
  | succ n' =>
      let k : Rat := (succ n') * 4
      leibniz₂R n' + 8 / ((k + 1) * (k + 3))

lemma leibniz₁R_sum (n : Nat) :
    ∀ sum : Rat, leibniz₁R n (4 * n) sum = leibniz₁R n (4 * n) 0 + sum := by
  induction' n with n0 ih
  { intro sum ; simp [leibniz₁R] ; exact Rat.add_comm sum (8 / 3) }
  {
    intro sum
    simp [leibniz₁R]
    calc
      leibniz₁R n0 (4 * (↑n0 + 1) - 4) (sum + 8 / ((4 * (↑n0 + 1) + 1) * (4 * (↑n0 + 1) + 3))) = leibniz₁R n0 (4 * ↑n0 + 4 * 1 - 4) (sum + 8 / ((4 * (↑n0 + 1) + 1) * (4 * (↑n0 + 1) + 3))) := by rw [Rat.mul_add]
      _ = leibniz₁R n0 (4 * ↑n0 + 4 - 4) (sum + 8 / ((4 * (↑n0 + 1) + 1) * (4 * (↑n0 + 1) + 3))) := by rw [Rat.mul_one]
      _ = leibniz₁R n0 (4 * ↑n0) (sum + 8 / ((4 * (↑n0 + 1) + 1) * (4 * (↑n0 + 1) + 3))) := by simp
      _ = leibniz₁R n0 (4 * ↑n0) 0 + (sum + 8 / ((4 * (↑n0 + 1) + 1) * (4 * (↑n0 + 1) + 3))) := by rw [ih]
      _ = leibniz₁R n0 (4 * ↑n0) 0 + sum + 8 / ((4 * (↑n0 + 1) + 1) * (4 * (↑n0 + 1) + 3)) := by rw [Rat.add_assoc]
      _ = leibniz₁R n0 (4 * ↑n0) 0 + 8 / ((4 * (↑n0 + 1) + 1) * (4 * (↑n0 + 1) + 3)) + sum := by rw [add_right_comm]
      _ = leibniz₁R n0 (4 * ↑n0) (8 / ((4 * (↑n0 + 1) + 1) * (4 * (↑n0 + 1) + 3))) + sum := by rw [←ih]
      _ = leibniz₁R n0 (4 * ↑n0 + 0) (8 / ((4 * (↑n0 + 1) + 1) * (4 * (↑n0 + 1) + 3))) + sum := by rw [Rat.add_zero]
      _ = leibniz₁R n0 (4 * ↑n0 + 4 - 4) (8 / ((4 * (↑n0 + 1) + 1) * (4 * (↑n0 + 1) + 3))) + sum := by simp
       _ = leibniz₁R n0 (4 * (↑n0 + 1) - 4) (8 / ((4 * (↑n0 + 1) + 1) * (4 * (↑n0 + 1) + 3))) + sum := by rw [@_root_.mul_add_one]
  }

lemma they_are_identical (n : Nat) :
    leibniz₁R n (4 * n) 0 = leibniz₂R n := by
  induction' n with n0 ih
  { dsimp [leibniz₁R, leibniz₂R] ; norm_num }
  {
    dsimp [leibniz₁R, leibniz₂R]
    have eq1 : ↑(n0 + 1) = ↑n0 + (1 : Rat) := by exact Mathlib.Tactic.Ring.inv_add rfl rfl
    calc
      leibniz₁R n0 (4 * ↑(n0 + 1) - 4) (0 + 8 / ((4 * ↑(n0 + 1) + 1) * (4 * ↑(n0 + 1) + 3))) = leibniz₁R n0 (4 * (↑n0 + 1) - 4) (0 + 8 / ((4 * ↑(n0 + 1) + 1) * (4 * ↑(n0 + 1) + 3))) := by rw [eq1]
      _ = leibniz₁R n0 (4 * ↑n0) (0 + 8 / ((4 * ↑(n0 + 1) + 1) * (4 * ↑(n0 + 1) + 3))) := by simp [Rat.mul_add]
      _ = leibniz₁R n0 (4 * ↑n0) 0 + (0 + 8 / ((4 * ↑(n0 + 1) + 1) * (4 * ↑(n0 + 1) + 3))) := by apply leibniz₁R_sum n0 _
      _ = leibniz₂R n0 + (0 + 8 / ((4 * ↑(n0 + 1) + 1) * (4 * ↑(n0 + 1) + 3)))
       := by rw [ih]
      _ = leibniz₂R n0 + 8 / ((4 * ↑(n0 + 1) + 1) * (4 * ↑(n0 + 1) + 3)) := by rw [Rat.zero_add]
      _ = leibniz₂R n0 + 8 / ((↑(n0 + 1) * 4 + 1) * (↑(n0 + 1) * 4 + 3)) := by simp [mul_comm]
  }

#check Fin 10
#eval ∑ x ∈ Finset.Iic 1, x

def L (n : Nat) : Rat := 4 * ∑ i ∈ Finset.range (n + 1), ((-1 : Rat) ^ i / (2 * i + 1 :Rat))
#eval (L 200).toFloat
#eval L 1

lemma range_add_one_eq_sup_self (n : Nat): Finset.range (n + 1) = Finset.range n ⊔ {n} := by
  refine Finset.ext_iff.mpr ?_
  intro k
  constructor
  {
    intro kn1
    by_cases kn : k ∈ range n
    { rw [sup_eq_union] ; exact mem_union_left {n} kn }
    {
      simp [range] at kn
      simp [range] at kn1
      rcases kn1 with a|b
      { simp ; right ; exact a }
      { contrapose! b ; exact kn }
    }
  }
  {
    intro H
    simp at H
    simp
    rcases H with A | B
    {
       exact Nat.lt_add_right 1 A
    }
    {
      rw [B] ; exact lt_add_one n
    }
  }

lemma range_sup_eq_add (n : Nat) (f : Nat → Rat) :
    ∑ i ∈ Finset.range n ⊔ {n}, f i = ∑ i ∈ Finset.range n, f i + ∑ i ∈ {n}, f i := by
  calc
    ∑ i ∈ Finset.range n ⊔ {n}, f i = ∑ i ∈ Finset.range n ∪ {n}, f i
      := by rfl
    _ = ∑ i ∈ Finset.range n, f i + ∑ i ∈ {n}, f i := by
      have : Disjoint (range n) {n} := by simp
      exact sum_union this

lemma L_is_Leibniz₂ (n : Nat) : L (2 * n + 1) = leibniz₂R n := by
  induction' n with n0 ih
  { simp [L, leibniz₂R] ; norm_num }
  {
    let r1 : Rat := 1 / (2 * n0 + 5)
    let r2 : Rat := (-1) / (2 * n0 + 7)
    have L_rec : L (2 * (n0 + 1) + 1) = L (2 * n0 + 1) + r1 + r2 := by
      sorry
    have l₂_rec : leibniz₂R (n0 + 1) = leibniz₂R n0 + r1 + r2 := by
      sorry
    simp only [L_rec, l₂_rec]
    rw [ih]
  }
