import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬x < x)
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  . apply le_inf
    . exact inf_le_right
    . exact inf_le_left
  . apply le_inf
    . exact inf_le_right
    . exact inf_le_left

#check le_trans

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  . apply le_inf
    . have L1 : (x ⊓ y) ⊓ z ≤ x ⊓ y := inf_le_left
      have L2 : x ⊓ y ≤ x := inf_le_left
      exact le_trans L1 L2
    . -- this branch requires le_inf
      have L1 : (x ⊓ y) ⊓ z ≤ y := by
        have L11 : (x ⊓ y) ⊓ z ≤ x ⊓ y := inf_le_left
        have L12 : x ⊓ y ≤ y := inf_le_right
        exact le_trans L11 L12
      have L2 : (x ⊓ y) ⊓ z ≤ z := inf_le_right
      exact le_inf L1 L2
  . apply le_inf
    . have L1 : x ⊓ (y ⊓ z) ≤ x := inf_le_left
      have L2 : x ⊓ (y ⊓ z) ≤ y := by
        have L21 : x ⊓ (y ⊓ z) ≤ y ⊓ z := inf_le_right
        have L22 : y ⊓ z ≤ y := inf_le_left
        exact le_trans L21 L22
      exact le_inf L1 L2
    . have L1 : x ⊓ (y ⊓ z) ≤ y ⊓ z := inf_le_right
      have L2 : y ⊓ z ≤ z := inf_le_right
      exact le_trans L1 L2

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  . have L1 : x ≤ y ⊔ x := le_sup_right
    have L2 : y ≤ y ⊔ x := le_sup_left
    exact sup_le L1 L2
  . have L1 : y ≤ x ⊔ y := le_sup_right
    have L2 : x ≤ x ⊔ y := le_sup_left
    exact sup_le L1 L2

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  . have L1 : x ⊔ y ≤ x ⊔ (y ⊔ z) := by
      have L11 : x ≤ x ⊔ (y ⊔ z) := le_sup_left
      have L12 : y ≤ x ⊔ (y ⊔ z) := by
        have L121 : y ≤ y ⊔ z := le_sup_left
        have L122 : y ⊔ z ≤ x ⊔ (y ⊔ z) := le_sup_right
        exact le_trans L121 L122
      exact sup_le L11 L12
    have L2 : z ≤ x ⊔ (y ⊔ z) := by
      have L21 : z ≤ y ⊔ z := le_sup_right
      have L22 : y ⊔ z ≤ x ⊔ (y ⊔ z) := le_sup_right
      exact le_trans L21 L22
    apply sup_le L1 L2
  . have L1 : x ≤ x ⊔ y ⊔ z := by
      have L11 : x ≤ x ⊔ y := le_sup_left
      have L12 : x ⊔ y ≤ x ⊔ y ⊔ z := le_sup_left
      apply le_trans L11 L12
    have L2 : y ⊔ z ≤ x ⊔ y ⊔ z := by
      have L21 : y ≤ x ⊔ y ⊔ z := by
        have L211 : y ≤ x ⊔ y := le_sup_right
        have L212 : x ⊔ y ≤ x ⊔ y ⊔ z := le_sup_left
        apply le_trans L211 L212
      have L22 : z ≤ x ⊔ y ⊔ z := le_sup_right
      apply sup_le L21 L22
    apply sup_le L1 L2

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  . apply inf_le_left
  . apply le_inf
    . apply le_refl
    . apply le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  . apply sup_le
    . apply le_refl
    . apply inf_le_left
  . apply le_sup_left

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw [h]
  rw [@inf_comm _ _ (a ⊔ b) a, absorb1]
  rw [@inf_comm _ _ (a ⊔ b), h, ← sup_assoc]
  rw [@inf_comm _ _ c a, sup_inf_self]
  rw [@inf_comm _ _ c b]

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  rw [h]
  rw [@sup_comm _ _ (a ⊓ b) a, sup_inf_self]
  rw [@sup_comm _ _ (a ⊓ b) c, h]
  rw [← inf_assoc]
  rw [@sup_comm _ _ c a, inf_sup_self]
  rw [@sup_comm _ _ c b]

end

section
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  sorry

example (h: 0 ≤ b - a) : a ≤ b := by
  sorry

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  sorry

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  sorry

end
