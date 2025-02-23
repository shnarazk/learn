import Mathlib.Tactic
import Mathlib.Data.Nat.Defs

namespace withFin

variable {size : Nat} [nonZeroSize: NeZero size]

def toDim2 (n : Nat) : Nat × Fin size := (n / size, Fin.ofNat' size (n % size))

example : NeZero 4 := by exact Nat.instNeZeroSucc
example : @toDim2 4 (by exact Nat.instNeZeroSucc) 10 = (2, 2) := by
  simp [toDim2]

example : NeZero size := by exact nonZeroSize

def fromDim2 (d : Nat × Fin size) : Nat := d.1 * size + d.2.val

lemma from_to_eq_id (n : Nat) : @fromDim2 size (@toDim2 size nonZeroSize n) = n := by
  simp [toDim2, fromDim2]
  exact Nat.div_add_mod' n size

end withFin

namespace withoutFin

variable {size : Nat}

def toDim2 (n : Nat) : Nat × Nat := (n / size, n % size)

example : @toDim2 4 10 = (2, 2) := by
  simp [toDim2]

def fromDim2 (d : Nat × Nat) : Nat := d.1 * size + d.2

lemma from_to_eq_id (n : Nat) : @fromDim2 size (@toDim2 size n) = n := by
  simp [toDim2, fromDim2]
  exact Nat.div_add_mod' n size

end withoutFin
