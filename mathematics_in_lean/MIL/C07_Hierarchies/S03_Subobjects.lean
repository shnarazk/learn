import MIL.Common
import Mathlib.GroupTheory.QuotientGroup.Basic

set_option autoImplicit true


@[ext]
structure Submonoid₁ (M : Type) [Monoid M] where
  /-- The carrier of a submonoid. -/
  carrier : Set M
  /-- The product of two elements of a submonoid belongs to the submonoid. -/
  mul_mem {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  /-- The unit element belongs to the submonoid. -/
  one_mem : 1 ∈ carrier

/-- Submonoids in `M` can be seen as sets in `M`. -/
instance [Monoid M] : SetLike (Submonoid₁ M) M where
  coe := Submonoid₁.carrier
  coe_injective' _ _ := Submonoid₁.ext



example [Monoid M] (N : Submonoid₁ M) : 1 ∈ N := N.one_mem

example [Monoid M] (N : Submonoid₁ M) (α : Type) (f : M → α) := f '' N


example [Monoid M] (N : Submonoid₁ M) (x : N) : (x : M) ∈ N := x.property


instance SubMonoid₁Monoid [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun x y ↦ ⟨x*y, N.mul_mem x.property y.property⟩
  mul_assoc := fun x y z ↦ SetCoe.ext (mul_assoc (x : M) y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun x ↦ SetCoe.ext (one_mul (x : M))
  mul_one := fun x ↦ SetCoe.ext (mul_one (x : M))


example [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨x*y, N.mul_mem hx hy⟩
  mul_assoc := fun ⟨x, _⟩ ⟨y, _⟩ ⟨z, _⟩ ↦ SetCoe.ext (mul_assoc x y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun ⟨x, _⟩ ↦ SetCoe.ext (one_mul x)
  mul_one := fun ⟨x, _⟩ ↦ SetCoe.ext (mul_one x)


class SubmonoidClass₁ (S : Type) (M : Type) [Monoid M] [SetLike S M] : Prop where
  mul_mem : ∀ (s : S) {a b : M}, a ∈ s → b ∈ s → a * b ∈ s
  one_mem : ∀ s : S, 1 ∈ s

instance [Monoid M] : SubmonoidClass₁ (Submonoid₁ M) M where
  mul_mem := Submonoid₁.mul_mem
  one_mem := Submonoid₁.one_mem

/-!
As an exercise you should define a Subgroup1 structure, endow it with a SetLike
instance and a SubmonoidClass1 instance, put a Group instance on the subtype
associated to a Subgroup1 and define a SubgroupClass1 class.

Here are the key characteristics of a subgroup:

1.  **Closure**: The result of combining any two elements from the subset using
the group operation must also be in the subset.
2.  **Identity**: The subset must contain the identity element of the original
group.
3.  **Inverse**: For each element in the subset, its inverse (i.e., the result of
applying the group operation to itself) must also be in the subset.
4.  **Associativity**: The group operation on the elements within the subset must
still satisfy associativity.
-/
@[ext]
-- structure Subgroup₁ (G : Type) [Monoid G] [Inv G] extends Submonoid₁ G where
structure Subgroup₁ (G : Type) [Group G] extends Submonoid₁ G where
  -- inv
  -- inv {a} : ∃ b ∈ carrier, a * b = 1
  inv_mem {a} : a ∈ carrier → a⁻¹ ∈ carrier

/-- Subgroups in `G` can be seen as sets in `G`. -/
instance [Group G] : SetLike (Subgroup₁ G) G where
  coe := fun self ↦ self.toSubmonoid₁.carrier
  coe_injective' _ _ := Subgroup₁.ext

/-- 何を要求されているのか? --/
instance [Group G] : SubmonoidClass₁ (Subgroup₁ G) G where
  mul_mem := fun self ↦ self.toSubmonoid₁.mul_mem
  one_mem := fun self ↦ self.toSubmonoid₁.one_mem

/-- 何を要求されているのか? --/
instance [Group G] (H : Subgroup₁ G) : Group H where
  mul := fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨x*y, H.mul_mem hx hy⟩
  mul_assoc := fun ⟨x, _⟩ ⟨y, _⟩ ⟨z, _⟩ ↦ SetCoe.ext (mul_assoc x y z)
  one := ⟨1, H.one_mem⟩
  one_mul := fun ⟨x, _⟩ ↦ SetCoe.ext (one_mul x)
  mul_one := fun ⟨x, _⟩ ↦ SetCoe.ext (mul_one x)
  inv := fun ⟨x, hx⟩ ↦ ⟨x⁻¹, H.inv_mem hx⟩
  inv_mul_cancel := fun ⟨x, hx⟩ ↦ SetCoe.ext (inv_mul_cancel x)

/-- define a SubgroupClass1 class. --/
class SubgroupClass₁ (S : Type) (G : Type) [Group G] [SetLike S G] : Prop where
  -- inv_mem {a} {s : S} : a ∈ s → a⁻¹ ∈ s
  inv_mem : ∀ (a : G) (s : S), a ∈ s → a⁻¹ ∈ s

instance [Monoid M] : Inf (Submonoid₁ M) :=
  ⟨fun S₁ S₂ ↦
    { carrier := S₁ ∩ S₂
      one_mem := ⟨S₁.one_mem, S₂.one_mem⟩
      mul_mem := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ ↦ ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩


example [Monoid M] (N P : Submonoid₁ M) : Submonoid₁ M := N ⊓ P


def Submonoid.Setoid [CommMonoid M] (N : Submonoid M) : Setoid M  where
  r := fun x y ↦ ∃ w ∈ N, ∃ z ∈ N, x*w = y*z
  iseqv := {
    refl := fun x ↦ ⟨1, N.one_mem, 1, N.one_mem, rfl⟩
    symm := fun ⟨w, hw, z, hz, h⟩ ↦ ⟨z, hz, w, hw, h.symm⟩
    trans := by
      intro x y z
      intro xy
      rcases xy with ⟨a, A, xy⟩
      rcases xy with ⟨b, B, xy⟩
      intro yz
      rcases yz with ⟨c, C, yz⟩
      rcases yz with ⟨d, D, yz⟩
      have left : x * c * a = y * b * c := by
        calc
          x * c * a = x * a * c := by exact mul_right_comm x c a
          _ = y * b * c := by rw [xy]
      have right : y * b * c = z * d * b := by
        calc
          y * b * c = y * c * b := by rw [@mul_right_comm]
          _ = z * d * b := by rw [yz]
      have : x * c * a = z * d * b := by
        calc
          x * c * a = y * b * c := by exact left
          _ = z * d * b := by rw [right]
      use c * a
      simp [by exact Submonoid.mul_mem N C A]
      use d * b
      simp [by exact Submonoid.mul_mem N D B]
      rw [←mul_assoc, ←mul_assoc]
      exact this
  }

instance [CommMonoid M] : HasQuotient M (Submonoid M) where
  quotient' := fun N ↦ Quotient N.Setoid

def QuotientMonoid.mk [CommMonoid M] (N : Submonoid M) : M → M ⧸ N := Quotient.mk N.Setoid

/- In the last example, you can use Setoid.refl but it won’t automatically pick up
the relevant Setoid structure. You can fix this issue by providing all arguments
using the @ syntax, as in @Setoid.refl M N.Setoid.
-/
instance [CommMonoid M] (N : Submonoid M) : Monoid (M ⧸ N) where
  mul := Quotient.map₂' (· * ·) (by
      sorry
        )
  mul_assoc := by
      sorry
  one := QuotientMonoid.mk N 1
  one_mul := by
      sorry
  mul_one := by
      sorry
