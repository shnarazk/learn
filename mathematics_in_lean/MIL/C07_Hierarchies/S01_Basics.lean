import MIL.Common
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Real.Basic

set_option autoImplicit true

-- 何を言っているのか
example (a : ℕ) : ℕ := by exact a

class One₁ (α : Type) where
  /-- The element one -/
  one : α


#check One₁.one -- One₁.one {α : Type} [self : One₁ α] : α

@[class] structure One₂ (α : Type) where
  /-- The element one -/
  one : α

#check One₂.one


example (α : Type) [One₁ α] : α := One₁.one

example (α : Type) [One₁ α] := (One₁.one : α)

@[inherit_doc]
notation "𝟙" => One₁.one

example {α : Type} [One₁ α] : α := 𝟙

example {α : Type} [One₁ α] : (𝟙 : α) = 𝟙 := rfl


class Dia₁ (α : Type) where
  dia : α → α → α

infixl:70 " ⋄ "   => Dia₁.dia


class Semigroup₁ (α : Type) where
  toDia₁ : Dia₁ α
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)


attribute [instance] Semigroup₁.toDia₁

example {α : Type} [Semigroup₁ α] (a b : α) : α := a ⋄ b
example {α : Type} [Semigroup₁ α] (a _b : α) : α := by exact a

class Semigroup₂ (α : Type) extends Dia₁ α where
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

example {α : Type} [Semigroup₂ α] (a b : α) : α := a ⋄ b

class DiaOneClass₁ (α : Type) extends One₁ α, Dia₁ α where
  /-- One is a left neutral element for diamond. -/
  one_dia : ∀ a : α, 𝟙 ⋄ a = a
  /-- One is a right neutral element for diamond -/
  dia_one : ∀ a : α, a ⋄ 𝟙 = a



set_option trace.Meta.synthInstance true in
example {α : Type} [DiaOneClass₁ α] (a b : α) : Prop := a ⋄ b = 𝟙


class Monoid₁ (α : Type) extends Semigroup₁ α, DiaOneClass₁ α


class Monoid₂ (α : Type) where
  toSemigroup₁ : Semigroup₁ α
  toDiaOneClass₁ : DiaOneClass₁ α


example {α : Type} [Monoid₁ α] :
  (Monoid₁.toSemigroup₁.toDia₁.dia : α → α → α) = Monoid₁.toDiaOneClass₁.toDia₁.dia := rfl


/- Monoid₂.mk {α : Type} (toSemigroup₁ : Semigroup₁ α) (toDiaOneClass₁ : DiaOneClass₁ α) : Monoid₂ α -/
#check Monoid₂.mk

/- Monoid₁.mk {α : Type} [toSemigroup₁ : Semigroup₁ α] [toOne₁ : One₁ α] (one_dia : ∀ (a : α), 𝟙 ⋄ a = a) (dia_one : ∀ (a : α), a ⋄ 𝟙 = a) : Monoid₁ α -/
#check Monoid₁.mk


#check Monoid₁.toSemigroup₁
#check Monoid₁.toDiaOneClass₁


class Inv₁ (α : Type) where
  /-- The inversion function -/
  inv : α → α

@[inherit_doc]
postfix:max "⁻¹" => Inv₁.inv

class Group₁ (G : Type) extends Monoid₁ G, Inv₁ G where
  inv_dia : ∀ a : G, a⁻¹ ⋄ a = 𝟙


lemma left_inv_eq_right_inv₁ {M : Type} [Monoid₁ M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  rw [← DiaOneClass₁.one_dia c, ← hba, Semigroup₁.dia_assoc, hac, DiaOneClass₁.dia_one b]


export DiaOneClass₁ (one_dia dia_one)
export Semigroup₁ (dia_assoc)
export Group₁ (inv_dia)


example {M : Type} [Monoid₁ M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  rw [← one_dia c, ← hba, dia_assoc, hac, dia_one b]


lemma inv_eq_of_dia [Group₁ G] {a b : G} (h : a ⋄ b = 𝟙) : a⁻¹ = b := by
  symm
  calc
    b = 𝟙 ⋄ b := by exact symm (one_dia b)
    _ = (a⁻¹ ⋄ a) ⋄ b := by rw [inv_dia]
    _ = a⁻¹ ⋄ (a ⋄ b) := by rw [dia_assoc]
    _ = a⁻¹ ⋄ 𝟙 := by rw [h]
    _ = a⁻¹ := by rw [dia_one]

lemma dia_inv [Group₁ G] (a : G) : a ⋄ a⁻¹ = 𝟙 := by
  have dbl : a⁻¹⁻¹ = a := by refine inv_eq_of_dia (inv_dia a)
  have inv : a⁻¹⁻¹ ⋄ a⁻¹ = 𝟙 := by exact inv_dia a⁻¹
  rw [dbl] at inv
  exact inv

class AddSemigroup₃ (α : Type) extends Add α where
/-- Addition is associative -/
  add_assoc₃ : ∀ a b c : α, a + b + c = a + (b + c)

@[to_additive AddSemigroup₃]
class Semigroup₃ (α : Type) extends Mul α where
/-- Multiplication is associative -/
  mul_assoc₃ : ∀ a b c : α, a * b * c = a * (b * c)

class AddMonoid₃ (α : Type) extends AddSemigroup₃ α, AddZeroClass α

@[to_additive AddMonoid₃]
class Monoid₃ (α : Type) extends Semigroup₃ α, MulOneClass α

attribute [to_additive existing] Monoid₃.toMulOneClass

export Semigroup₃ (mul_assoc₃)
export AddSemigroup₃ (add_assoc₃)

whatsnew in
@[to_additive]
lemma left_inv_eq_right_inv' {M : Type} [Monoid₃ M] {a b c : M} (hba : b * a = 1) (hac : a * c = 1) : b = c := by
  rw [← one_mul c, ← hba, mul_assoc₃, hac, mul_one b]

#check left_neg_eq_right_neg'

class AddCommSemigroup₃ (α : Type) extends AddSemigroup₃ α where
  add_comm : ∀ a b : α, a + b = b + a

@[to_additive AddCommSemigroup₃]
class CommSemigroup₃ (α : Type) extends Semigroup₃ α where
  mul_comm : ∀ a b : α, a * b = b * a

class AddCommMonoid₃ (α : Type) extends AddMonoid₃ α, AddCommSemigroup₃ α

@[to_additive AddCommMonoid₃]
class CommMonoid₃ (α : Type) extends Monoid₃ α, CommSemigroup₃ α

class AddGroup₃ (G : Type) extends AddMonoid₃ G, Neg G where
  neg_add : ∀ a : G, -a + a = 0

@[to_additive AddGroup₃]
class Group₃ (G : Type) extends Monoid₃ G, Inv G where
  inv_mul : ∀ a : G, a⁻¹ * a = 1


attribute [simp] Group₃.inv_mul AddGroup₃.neg_add



@[to_additive]
lemma inv_eq_of_mul [Group₃ G] {a b : G} (h : a * b = 1) : a⁻¹ = b := by
  have one : a⁻¹ * a = 1 := by exact Group₃.inv_mul a
  exact left_inv_eq_right_inv' one h

@[to_additive (attr := simp)]
lemma Group₃.mul_inv {G : Type} [Group₃ G] {a : G} : a * a⁻¹ = 1 := by
  have dbl : a⁻¹⁻¹ = a := by refine inv_eq_of_mul (inv_mul a)
  symm
  calc
    1 = a⁻¹⁻¹ * a⁻¹ := by rw [←inv_mul]
    _ = a * a⁻¹ := by rw [dbl]

@[to_additive]
lemma mul_left_cancel₃ {G : Type} [Group₃ G] {a b c : G} (h : a * b = a * c) : b = c := by
  rw [←one_mul b, ←one_mul c]
  rw [←Group₃.inv_mul a, mul_assoc₃, mul_assoc₃, h]

@[to_additive]
lemma mul_right_cancel₃ {G : Type} [Group₃ G] {a b c : G} (h : b * a = c * a) : b = c := by
  rw [←mul_one b, ←mul_one c]
  rw [←@Group₃.mul_inv _ _ a, ←mul_assoc₃, ←mul_assoc₃, h]

class AddCommGroup₃ (G : Type) extends AddGroup₃ G, AddCommMonoid₃ G

@[to_additive AddCommGroup₃]
class CommGroup₃ (G : Type) extends Group₃ G, CommMonoid₃ G



class Ring₃ (R : Type) extends AddGroup₃ R, Monoid₃ R, MulZeroClass R where
  /-- Multiplication is left distributive over addition -/
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  /-- Multiplication is right distributive over addition -/
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

instance {R : Type} [Ring₃ R] : AddCommGroup₃ R :=
{ Ring₃.toAddGroup₃ with
  add_comm := by
    intro a b
    have : a + (b + a) + b = a + (a + b) + b := by
      calc
        a + (b + a) + b = a + ((b + a) + b) := by rw [add_assoc₃]
        _ = a + (b + a + b) := by rw [add_assoc₃]
        _ = a + (b + (a + b)) := by rw [add_assoc₃]
        _ = (a + b) + (a + b) := by rw [add_assoc₃]
        _ = (a + b) * 1 + (a + b) * 1 := by rw [mul_one]
        _ = (a + b) * (1 + 1) := by rw [Ring₃.left_distrib]
        _ = a * (1 + 1) + b * (1 + 1) := by rw [Ring₃.right_distrib]
        _ = a * 1 + a * 1 + (b * 1 + b * 1) := by rw [Ring₃.left_distrib, Ring₃.left_distrib]
        _ = a + a + (b + b) := by simp
        _ = a + (a + (b + b)) := by rw [add_assoc₃]
        _ = a + ((a + b) + b) := by rw [add_assoc₃]
        _ = a + (a + b) + b := by rw [←add_assoc₃]
    apply add_right_cancel₃ at this
    apply add_left_cancel₃ at this
    exact symm this
}

instance : Ring₃ ℤ where
  add := (· + ·)
  add_assoc₃ := add_assoc
  zero := 0
  zero_add := by simp
  add_zero := by simp
  neg := (- ·)
  neg_add := by simp
  mul := (· * ·)
  mul_assoc₃ := mul_assoc
  one := 1
  one_mul := by simp
  mul_one := by simp
  zero_mul := by simp
  mul_zero := by simp
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul

class LE₁ (α : Type) where
  /-- The Less-or-Equal relation. -/
  le : α → α → Prop

@[inherit_doc] infix:50 " ≤₁ " => LE₁.le

/-
1. Reflexivity: ∀ a : α, a ≤₁ a
1. Transitivity (a b c : α) (ab : a ≤₁ b) (bc : b ≤₁ c) : a ≤₁ c
-/
class Preorder₁ (α : Type) extends LE₁ α where
  le_refl : ∀ a : α, a ≤₁ a
  le_trans : ∀ a b c : α, a ≤₁ b → b ≤₁ c → a ≤₁ c

/-
1. Extends Preorder
1. Antisymmetry (a b : α) (ab : a ≤₁ b) (ba : b ≤₁ a) : a = b
-/
class PartialOrder₁ (α : Type) extends Preorder₁ α, CommMonoid₃ α where
  le_antisymm : ∀ a b : α, a ≤₁ b → b ≤₁ a → a = b

/- a class for ordered commutative monoids, which have both a partial order and a commutative monoid structure such that
∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b.
-/
class OrderedCommMonoid₁ (α : Type) extends PartialOrder₁ α where
  le_of_mul : ∀ a b : α, a ≤₁ b → ∀ c : α, c * a ≤₁ c * b

instance : OrderedCommMonoid₁ ℕ where
  le := (· ≤ ·)
  le_refl := by simp
  le_trans := by intro a b c ; exact Nat.le_trans
  one_mul := by simp
  mul_one := by simp
  mul_assoc₃ := by intro a b c ; exact Nat.mul_assoc a b c
  mul_comm := by intro a b ; exact Nat.mul_comm a b
  le_antisymm := by intro a b ; simp ; exact Nat.le_antisymm
  le_of_mul := by
    intro a b ab
    intro c
    simp at ab
    simp
    exact Nat.mul_le_mul_left c ab

class SMul₃ (α : Type) (β : Type) where
  /-- Scalar multiplication -/
  smul : α → β → β

infixr:73 " • " => SMul₃.smul


class Module₁ (R : Type) [Ring₃ R] (M : Type) [AddCommGroup₃ M] extends SMul₃ R M where
  zero_smul : ∀ m : M, (0 : R) • m = 0
  one_smul : ∀ m : M, (1 : R) • m = m
  mul_smul : ∀ (a b : R) (m : M), (a * b) • m = a • b • m
  add_smul : ∀ (a b : R) (m : M), (a + b) • m = a • m + b • m
  smul_add : ∀ (a : R) (m n : M), a • (m + n) = a • m + a • n

instance selfModule (R : Type) [Ring₃ R] : Module₁ R R where
  smul := fun r s ↦ r*s
  zero_smul := zero_mul
  one_smul := one_mul
  mul_smul := mul_assoc₃
  add_smul := Ring₃.right_distrib
  smul_add := Ring₃.left_distrib

def nsmul₁ [Zero M] [Add M] : ℕ → M → M
  | 0, _ => 0
  | n + 1, a => a + nsmul₁ n a

def zsmul₁ {M : Type*} [Zero M] [Add M] [Neg M] : ℤ → M → M
  | Int.ofNat n, a => nsmul₁ n a
  | Int.negSucc n, a => -nsmul₁ n.succ a

/- You are not asked to replace those sorries with proofs
If you insist on doing it then you will probably want to state and prove several intermediate lemmas about nsmul1 and zsmul₁. -/

lemma neg_zero_eq_zero {A : Type} [AddCommGroup₃ A] : -(0 : A) = (0 : A) := by
  have : 0 + 0 = (0 : A) := by exact AddMonoid₃.zero_add 0
  exact neg_eq_of_add this

lemma neg_dist₁ (m n : A) [AddCommGroup₃ A] : -(m + n) = -m + -n := by
  apply neg_eq_of_add
  rw [AddCommGroup₃.add_comm m n]
  rw [←add_assoc₃]
  nth_rewrite 2 [add_assoc₃]
  simp

lemma neg_neg_eq_cancel (m : A) [AddCommGroup₃ A] : - -m = m := by
  rw [neg_eq_of_add]
  exact AddGroup₃.neg_add m

lemma zsmul_zero_eq_zero {m : A} [AddCommGroup₃ A] : zsmul₁ 0 m = 0 := rfl
lemma nsmul_zero_eq_zero {m : A} [AddCommGroup₃ A] : nsmul₁ 0 m = 0 := rfl

lemma zsmul_one_eq_cancel {m : A} [AddCommGroup₃ A] : zsmul₁ 1 m = m := by
  simp [zsmul₁]
  simp [nsmul₁]
lemma nsmul_one_eq_cancel {m : A} [AddCommGroup₃ A] : nsmul₁ 1 m = m := by
  simp [nsmul₁]

lemma zsmul_eq_nsmul {m : A} [AddCommGroup₃ A] (a : ℕ) : zsmul₁ ↑a m = nsmul₁ a m := by
  simp [zsmul₁]

lemma zsmul_eq_nsmul_of_nonneg {m : A} [AddCommGroup₃ A] (a : ℤ) (b : ℕ) (h : a = ↑b) :
    zsmul₁ a m = nsmul₁ b m := by
  rcases a with aN | aZ
  { rw [h] ; rfl }
  {
    have X : ¬ 0 ≤ Int.negSucc aZ := by exact of_decide_eq_false rfl
    have Y : 0 ≤ (↑b : ℤ) := by exact Int.ofNat_zero_le b
    rw [h] at X
    exact absurd Y X
  }

lemma nsmul_neg_eq_neg_nsmul {m : A} [AddCommGroup₃ A] (a : ℕ) :
    nsmul₁ a m = -nsmul₁ a (-m) := by
  induction' a with a0 a1
  { simp [nsmul₁] ; exact Eq.symm neg_zero_eq_zero }
  {
    simp [nsmul₁]
    simp only [neg_dist₁, a1]
    have : m = - -m := by
      refine Eq.symm (neg_eq_of_add ?h)
      exact AddGroup₃.neg_add m
    rw [←this]
  }

lemma add_left_dist₁ (a b : ℤ) (m : A) [AddCommGroup₃ A] : zsmul₁ (a + b) m = zsmul₁ a m + zsmul₁ b m := by
  have zinc {m : A} (n : ℤ) : m + zsmul₁ n m = zsmul₁ (n + 1) m := by
    induction' n with nnn nn
    {
      induction' nnn with n0 _
      { simp [zsmul₁] ; exact rfl }
      {
        have : Int.ofNat (n0 + 1) = Int.ofNat n0 + 1 := rfl
        rw [this]
        nth_rewrite 2 [zsmul₁.eq_def]
        have : Int.ofNat n0 + 1 + 1 = Int.ofNat (n0 + 1 + 1) := by rfl
        rw [this]
        have : ↑n0 + 1 = Int.ofNat (n0 + 1) := by rfl
        simp only [zsmul₁, this]
        rfl
      }
    }
    {
      induction' nn with n hn
      {
        simp [zsmul₁]
        nth_rewrite 2 [nsmul₁.eq_def]
        simp
        simp only [nsmul₁]
        rw [add_zero]
        simp
      }
      {
        have flip (n : ℕ) : zsmul₁ (Int.negSucc n) m = -nsmul₁ (n + 1) m := rfl
        by_cases n0 : n = 0
        {
          simp only [n0]
          rw [flip 1]
          have : Int.negSucc (0 + 1) + 1 = Int.negSucc 0 := rfl
          simp only [this]
          rw [flip 0]
          have : -nsmul₁ (1 + 1) m = -(m + nsmul₁ 1 m) := by exact flip 1
          simp [this]
          have : nsmul₁ 1 m = m := by simp [nsmul₁]
          simp only [this]
          apply @add_right_cancel₃ _ _ (m + m)
          rw [add_assoc₃ m, AddCommSemigroup₃.add_comm (-(m + m)), @AddGroup₃.add_neg A _ (m + m)]
          simp
          simp [←add_assoc₃]
        }
        {
          rw [flip] at hn
          rw [flip (n + 1)]
          have : Int.negSucc (n + 1) = Int.negSucc n - 1 := rfl
          rw [this]
          have : Int.negSucc n = Int.negSucc n - 1 + 1 := by exact rfl
          rw [← this]
          simp [flip]
          have val (n : ℕ) : nsmul₁ (n + 1) m = m + nsmul₁ n m := by exact rfl
          have : nsmul₁ (n + 1 + 1) m = m + nsmul₁ (n + 1) m := by exact val (n + 1)
          simp [this]
          apply @add_right_cancel₃ _ _ (m + nsmul₁ (n + 1) m)
          rw [add_assoc₃ m, AddCommSemigroup₃.add_comm (-(m + nsmul₁ (n + 1) m)), @AddGroup₃.add_neg A _ _]
          rw [add_zero]
          rw [←AddCommSemigroup₃.add_comm, add_assoc₃, ←AddCommSemigroup₃.add_comm]
          rw [@AddGroup₃.add_neg, zero_add]
        }
      }
    }
  have z_zero : zsmul₁ 0 m = 0 := by exact rfl
  rcases b with bN | bZ
  {
    induction' bN with b0 bP
    { simp [z_zero] }
    {
      have : Int.ofNat (b0 + 1) = Int.ofNat b0 + 1 := by rfl
      simp only [this]
      rw [← add_assoc₃]
      rw [← zinc]
      rw [bP]
      rw [← zinc]
      rw [← add_assoc₃]
      rw [← add_assoc₃]
      rw [AddCommSemigroup₃.add_comm _ m]
    }
  }
  {
    induction' bZ with b0 bP
    {
      simp
      have : m + zsmul₁ (a + -1) m = zsmul₁ (a + -1 + 1) m := by exact zinc (a + -1)
      simp [linarith] at this
      rw [← this]
      have : zsmul₁ (-1) m = -m := by exact Eq.symm (neg_eq_of_add (zinc (-1)))
      rw [this]
      rw [AddCommSemigroup₃.add_comm m]
      rw [add_assoc₃]
      simp
    }
    {
      let c : ℤ := Int.negSucc b0
      have as_c : c = Int.negSucc b0 := by rfl
      have : Int.negSucc (b0 + 1) = Int.negSucc b0 - 1 := rfl
      rw [this]
      rw [←as_c]
      rw [←as_c] at bP
      have : m + zsmul₁ (a + c - 1) m = zsmul₁ (a + c - 1 + 1) m := by exact zinc (a + c - 1)
      have sub1 : a + c - 1 = a + (c - 1) := by exact Int.add_sub_assoc a c 1
      have sub2 : a + c - 1 + 1 = a + c := by exact Int.sub_add_cancel (a + c) 1
      nth_rewrite 1 [sub1] at this
      rw [sub2] at this
      nth_rewrite 1 [←zero_add (zsmul₁ _ _)]
      rw [←@AddGroup₃.add_neg _ _ m, AddCommSemigroup₃.add_comm m, add_assoc₃, this]
      have : zsmul₁ (-1) m = -m := by exact Eq.symm (neg_eq_of_add (zinc (-1)))
      rw [bP, ←add_assoc₃, AddCommGroup₃.add_comm (-m), add_assoc₃]
      have last_one : -m + zsmul₁ c m = zsmul₁ (c - 1) m := by
        symm
        simp [zsmul₁]
        have : c - 1 = Int.negSucc b0 - 1 := by rw [as_c]
        simp [this]
        simp [nsmul₁]
        have dist (a b : A) : -(a + b) = -a + -b := by
          have : a + b + (-a + -b) = 0 := by
            calc
              a + b + (-a + -b) = a + (b + (-a + -b)) := by exact add_assoc₃ a b (-a + -b)
              _ = a + (b + (-b + -a)) := by rw [AddCommGroup₃.add_comm (-a)]
              _ = a + (b + -b + -a) := by rw [add_assoc₃ b]
              _ = a + -a := by simp
              _ = 0 := by simp
          exact neg_eq_of_add this
        rw [←dist]
      rw [last_one]
    }
  }

lemma add_left_distℕ₁ (a b : ℕ) (m : A) [AddCommGroup₃ A] : nsmul₁ (a + b) m = nsmul₁ a m + nsmul₁ b m := by
  let az : ℤ := Int.ofNat a
  let bz : ℤ := Int.ofNat b
  have : zsmul₁ (az + bz) m = zsmul₁ az m + zsmul₁ bz m := by exact add_left_dist₁ az bz m
  exact this

lemma add_right_dist₁ (a : ℤ) (m n : A) [AddCommGroup₃ A] :
    zsmul₁ a (m + n) = zsmul₁ a m + zsmul₁ a n := by
  by_cases aN : 0 ≤ a
  {
    induction' a with a0 ia
    {
      induction' a0 with a00 ia0
      { simp [zsmul₁, nsmul₁] }
      {
        simp only [zsmul₁]
        have : 0 ≤ Int.ofNat a00 := by exact Int.zero_le_ofNat a00
        simp [this] at ia0
        simp [zsmul₁] at ia0
        simp [add_left_distℕ₁]
        rw [ia0]
        simp [nsmul_one_eq_cancel]
        rw [←add_assoc₃]
        nth_rewrite 1 [←add_assoc₃]
        nth_rewrite 5 [AddCommGroup₃.add_comm]
        rw [←add_assoc₃]
        nth_rewrite 6 [AddCommGroup₃.add_comm]
        rfl
      }
    }
    {
      have aNN : ¬0 ≤ Int.negSucc ia := by exact of_decide_eq_false rfl
      exact absurd aN aNN
    }
  }
  {
    simp only [zsmul₁]
    rcases a with an | ap
    {
      have aNN : 0 ≤ Int.ofNat an := by exact Int.zero_le_ofNat an
      exact absurd aNN aN
    }
    {
      simp
      induction' ap with a0 ia
      { simp [nsmul₁] ; exact neg_dist₁ m n }
      {
        simp at ia
        -- left hand
        rw [add_left_distℕ₁]
        simp only [neg_dist₁, ia]
        rw [nsmul_one_eq_cancel]
        rw [neg_dist₁, ←add_assoc₃]
        -- right hand
        nth_rewrite 3 [add_left_distℕ₁]
        rw [neg_dist₁]
        nth_rewrite 4 [add_left_distℕ₁]
        rw [neg_dist₁]
        simp only [nsmul_one_eq_cancel]
        nth_rewrite 3 [add_assoc₃]
        nth_rewrite 5 [AddCommGroup₃.add_comm]
        nth_rewrite 3 [add_assoc₃]
        nth_rewrite 6 [AddCommGroup₃.add_comm]
        nth_rewrite 2 [←add_assoc₃]
        nth_rewrite 1 [←add_assoc₃]
        nth_rewrite 1 [←add_assoc₃]
        rfl
      }
    }
  }

lemma add_right_distℕ₁ (a : ℕ) (m n : A) [AddCommGroup₃ A] :
    nsmul₁ a (m + n) = nsmul₁ a m + nsmul₁ a n := by
  exact add_right_dist₁ ↑a m n

lemma mul_dist₁ (a b : ℤ) (m : A) [AddCommGroup₃ A] : zsmul₁ (a * b) m = zsmul₁ a (zsmul₁ b m) := by
  have one_mul_eq_cancel (a : ℤ) (m : A) : zsmul₁ a m = zsmul₁ (Int.ofNat 1) (zsmul₁ a m) := by
    nth_rewrite 2 [zsmul₁.eq_def]
    simp
    simp [nsmul₁]
  by_cases aN : 0 ≤ a
  {
    by_cases  bN : 0 ≤ b
    {
      have ap : 0 ≤ a * b := by exact Int.mul_nonneg aN bN
      rcases a with an | az
      {
        rcases b with bn | bz
        {
          induction' an with a0 ia
          { simp [zsmul₁, nsmul₁] }
          {
            have xx : 0 ≤ Int.ofNat a0 := by exact Int.zero_le_ofNat a0
            have xy : 0 ≤ Int.ofNat a0 * Int.ofNat bn := by exact Int.mul_nonneg xx bN
            rcases ia xx xy with ia'
            have : ∀ x y z : ℤ, (x + y) * z = x * z + y * z := by exact add_mul
            /- もしかしてzincを使えばいいだけじゃなかろか -/
            calc
              zsmul₁ (Int.ofNat (a0 + 1) * Int.ofNat bn) m =
                zsmul₁ ((Int.ofNat a0 + Int.ofNat 1) * Int.ofNat bn) m := by exact rfl
              _ = zsmul₁ (Int.ofNat a0 * Int.ofNat bn + Int.ofNat 1 * Int.ofNat bn) m := by rw [add_mul]
              _ = zsmul₁ (Int.ofNat a0 * Int.ofNat bn) m + zsmul₁ (Int.ofNat 1 * Int.ofNat bn) m := by rw [add_left_dist₁ (Int.ofNat a0 * Int.ofNat bn) (Int.ofNat 1 * Int.ofNat bn) m]
              _ = zsmul₁ (Int.ofNat a0) (zsmul₁ (Int.ofNat bn) m) + zsmul₁ (Int.ofNat 1 * Int.ofNat bn) m := by rw [ia']
              _ = zsmul₁ (Int.ofNat a0) (zsmul₁ (Int.ofNat bn) m) + zsmul₁ (Int.ofNat bn) m := by simp
              _ = zsmul₁ (Int.ofNat a0) (zsmul₁ (Int.ofNat bn) m) + zsmul₁ (Int.ofNat 1) (zsmul₁ (Int.ofNat bn) m) := by
                nth_rewrite 2 [one_mul_eq_cancel (Int.ofNat bn) m]
                rfl
              _ = zsmul₁ (Int.ofNat a0 + Int.ofNat 1) (zsmul₁ (Int.ofNat bn) m) := by rw [
                ←add_left_dist₁ (Int.ofNat a0) (Int.ofNat 1) (zsmul₁ (Int.ofNat bn) m)]
              _ = zsmul₁ (Int.ofNat (a0 + 1)) (zsmul₁ (Int.ofNat bn) m) := by exact rfl
          }
        }
        {
          induction' an with a0 ia
          { simp [zsmul₁,nsmul₁] }
          {
            have : Int.ofNat (a0 + 1) = Int.ofNat a0 + Int.ofNat 1 := rfl
            rw [this]
            rw [add_mul]
            rw [add_left_dist₁]
            have : zsmul₁ (Int.ofNat a0 * Int.negSucc bz) m = zsmul₁ (Int.ofNat a0) (zsmul₁ (Int.negSucc bz) m) := by
              have an' : 0 ≤ Int.ofNat a0 := by exact Int.zero_le_ofNat a0
              have ap' : 0 ≤ Int.ofNat a0 * Int.negSucc bz := by exact Int.mul_nonneg an' bN
              exact ia an' ap'
            rw [this]
            rw [add_left_dist₁]
            simp
            have : 1 = Int.ofNat 1 := rfl
            rw [this, ←one_mul_eq_cancel (Int.negSucc bz)]
          }
        }
      }
      {
        have aNN : ¬ 0≤ Int.negSucc az := by exact of_decide_eq_false rfl
        exact absurd aN aNN
      }
    }
    {
      rcases a with a_N | a_Z
      {
        induction' a_N with a0 ia
        { simp [zsmul₁,nsmul₁] }
        {
          have : Int.ofNat (a0 + 1) = Int.ofNat a0 + Int.ofNat 1 := rfl
          simp only [this]
          have : (Int.ofNat a0 + Int.ofNat 1) * b = (Int.ofNat a0) * b + b := by exact add_one_mul (↑a0) b
          simp only [this]
          rw [add_left_dist₁]
          have : 0 ≤ Int.ofNat a0 := by exact Int.zero_le_ofNat a0
          rw [ia this]
          nth_rewrite 3 [one_mul_eq_cancel]
          rw [add_left_dist₁]
        }
      }
      {
        have aNN : ¬0≤ Int.negSucc a_Z := by exact of_decide_eq_false rfl
        exact absurd aN aNN
      }
    }
  }
  {
    -- case: a < 0
    induction' b with bN0 bNp
    {
      {
        induction' bN0 with bNN0 bNNN
        {
          simp
          simp [zsmul_zero_eq_zero]
          have nsmul_zero : ∀ n : ℕ, nsmul₁ n (0 : A) = 0 := by
            intro n
            induction' n with n0 hn
            { simp [nsmul₁] }
            { simp [nsmul₁] ; exact hn }
          have zsmul_zero (a : ℤ) : zsmul₁ a (0 : A) = 0 := by
            rcases a with aN | aZ
            { exact nsmul_zero aN }
            {
              induction' aZ with aZ0 aZZ
              {
                simp [zsmul₁, nsmul₁]
                exact neg_zero_eq_zero
              }
              {
                have dec (a : ℕ) : Int.negSucc (a + 1) = Int.negSucc a + -1 := rfl
                simp only [dec]
                simp [add_left_dist₁, aZZ]
                simp [zsmul₁]
                have : (-1 : ℤ) = Int.negSucc 0 := rfl
                simp only [this, nsmul_zero]
                exact neg_zero_eq_zero
              }
            }
          simp only [zsmul_zero]
        }
        have ds : a * Int.ofNat (bNN0 + 1) = a * Int.ofNat bNN0 + a := by
          calc
            a * Int.ofNat (bNN0 + 1) = a * (Int.ofNat bNN0 + Int.ofNat 1) := rfl
            _ = a * Int.ofNat bNN0 + a * Int.ofNat 1 := by
              rw [Ring₃.left_distrib a (Int.ofNat bNN0) (Int.ofNat 1)]
            _ = a * Int.ofNat bNN0 + a * 1 := rfl
            _ = a * Int.ofNat bNN0 + a := by rw [Monoid₃.mul_one a]
        rw [ds]
        have : Int.ofNat (bNN0 + 1) = Int.ofNat bNN0 + Int.ofNat 1 := rfl
        rw [this]
        rw [add_left_dist₁]
        rw [add_left_dist₁]
        rw [bNNN]
        simp only [add_right_dist₁]
        have : zsmul₁ (Int.ofNat 1)  m = m := by simp [zsmul₁, nsmul₁]
        rw[this]
      }
    }
    {
      induction' bNp with bN0 ib
      {
        simp
        simp [zsmul₁]
        induction' a with aN0 aNN
        {
          induction' aN0 with aN0' ia
          { simp [nsmul₁] }
          {
            simp at ia
            have : 0 ≤ Int.ofNat (aN0' + 1) := by exact Int.zero_le_ofNat (aN0' + 1)
            exact absurd this aN
          }
        }
        {
          simp at aN
          simp
          have : -Int.negSucc aNN = Int.ofNat (aNN + 1) := rfl
          simp only [this]
          have : -1 = Int.negSucc 0 := rfl
          simp only [this]
          simp [nsmul_one_eq_cancel]
          rw [nsmul_neg_eq_neg_nsmul]
        }
      }
      {
        have : a * (Int.negSucc (bN0 + 1)) = a * Int.negSucc bN0 + -a := by
          calc
            a * (Int.negSucc (bN0 + 1)) = a * (Int.negSucc bN0 + -1) := rfl
            _ = a * Int.negSucc bN0 - a := by exact mul_sub_one a (Int.negSucc bN0)
        simp only [this]
        rw [add_left_dist₁ (a * Int.negSucc bN0)]
        simp only [ib]
        -- right hand
        have : Int.negSucc (bN0 + 1) = Int.negSucc bN0 + -1 := rfl
        simp only [this]
        simp only [add_left_dist₁]
        rw [add_right_dist₁]
        have : (zsmul₁ (-1) m) = -m := by
          simp [zsmul₁]
          have : -1 = Int.negSucc 0 := rfl
          rw [this]
          simp [nsmul₁]
        simp only [this]
        have : zsmul₁ a (-m) = zsmul₁ (-a) m := by
          simp [zsmul₁]
          induction' a with a_N a_Z
          {
            have aNN : 0 ≤ Int.ofNat a_N := by exact Int.zero_le_ofNat a_N
            exact absurd aNN aN
          }
          {
            induction' a_Z with a_Z0 ia
            {
              simp [nsmul₁]
              rw [neg_eq_of_add]
              exact AddGroup₃.neg_add m
            }
            {
              simp at ia
              simp at ib
              have : -Int.negSucc (a_Z0 + 1) = Int.ofNat (a_Z0 + 2) := rfl
              simp [nsmul₁]
              simp only [this]
              rw [neg_dist₁, neg_dist₁]
              simp only [neg_neg_eq_cancel]
              rw [←add_assoc₃]
              have : a_Z0 + 2 = (a_Z0 + 1) + 1 := rfl
              simp only [this]
              rw [add_left_distℕ₁ (a_Z0 + 1) 1 m]
              rw [nsmul_one_eq_cancel]
              rw [add_left_distℕ₁ a_Z0 1 m]
              rw [nsmul_one_eq_cancel]
              rw [nsmul_neg_eq_neg_nsmul]
              simp only [neg_neg_eq_cancel]
              rw [AddCommGroup₃.add_comm, add_assoc₃]
           }
          }
        simp only [this]
      }
    }
  }

instance abGrpModule (A : Type) [AddCommGroup₃ A] : Module₁ ℤ A where
  smul := zsmul₁
  zero_smul := by intro _ ; simp [zsmul₁, nsmul₁]
  one_smul := by intro x ; simp [zsmul₁, nsmul₁]
  mul_smul := by intro x y m ; simp ; exact mul_dist₁ x y m
  add_smul := by intro a b c ; simp ; exact add_left_dist₁ a b c
  smul_add := by intro a b c ; simp ; exact add_right_dist₁ a b c

#synth Module₁ ℤ ℤ -- abGrpModule ℤ


class AddMonoid₄ (M : Type) extends AddSemigroup₃ M, AddZeroClass M where
  /-- Multiplication by a natural number. -/
  nsmul : ℕ → M → M := nsmul₁
  /-- Multiplication by `(0 : ℕ)` gives `0`. -/
  nsmul_zero : ∀ x, nsmul 0 x = 0 := by intros; rfl
  /-- Multiplication by `(n + 1 : ℕ)` behaves as expected. -/
  nsmul_succ : ∀ (n : ℕ) (x), nsmul (n + 1) x = x + nsmul n x := by intros; rfl

instance mySMul {M : Type} [AddMonoid₄ M] : SMul ℕ M := ⟨AddMonoid₄.nsmul⟩

instance (M N : Type) [AddMonoid₄ M] [AddMonoid₄ N] : AddMonoid₄ (M × N) where
  add := fun p q ↦ (p.1 + q.1, p.2 + q.2)
  add_assoc₃ := fun a b c ↦ by ext <;> apply add_assoc₃
  zero := (0, 0)
  zero_add := fun a ↦ by ext <;> apply zero_add
  add_zero := fun a ↦ by ext <;> apply add_zero

instance : AddMonoid₄ ℤ where
  add := (· + ·)
  add_assoc₃ := Int.add_assoc
  zero := 0
  zero_add := Int.zero_add
  add_zero := Int.add_zero
  nsmul := fun n m ↦ (n : ℤ) * m
  nsmul_zero := Int.zero_mul
  nsmul_succ := fun n m ↦ show (n + 1 : ℤ) * m = m + n * m
    by rw [Int.add_mul, Int.add_comm, Int.one_mul]

example (n : ℕ) (m : ℤ) : SMul.smul (self := mySMul) n m = n * m := rfl
