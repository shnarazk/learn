import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic

import MIL.Common

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

variable {W : Type*} [AddCommGroup W] [Module K W]

open Polynomial Module LinearMap

example (φ ψ : End K V) : φ * ψ = φ ∘ₗ ψ :=
  LinearMap.mul_eq_comp φ ψ -- `rfl` would also work

-- evaluating `P` on `φ`
example (P : K[X]) (φ : End K V) : V →ₗ[K] V :=
  aeval φ P

-- evaluating `X` on `φ` gives back `φ`
example (φ : End K V) : aeval φ (X : K[X]) = φ :=
  aeval_X φ

#check Submodule.eq_bot_iff
#check Submodule.mem_inf
#check LinearMap.mem_ker

example (P Q : K[X]) (h : IsCoprime P Q) (φ : End K V) : ker (aeval φ P) ⊓ ker (aeval φ Q) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro x hx
  rw [Submodule.mem_inf, mem_ker, mem_ker] at hx
  rcases h with ⟨U, V, hUV⟩
  have := congr((aeval φ) $hUV.symm x)
  simp at this
  rcases hx with ⟨P0, Q0⟩
  simp [P0,Q0] at this
  exact this

#check Submodule.add_mem_sup
#check map_mul
#check LinearMap.mul_apply
#check LinearMap.ker_le_ker_comp

example (P Q : K[X]) (h : IsCoprime P Q) (φ : End K V) :
    ker (aeval φ P) ⊔ ker (aeval φ Q) = ker (aeval φ (P*Q)) := by
  apply le_antisymm
  {
    apply sup_le
    {
      rw [mul_comm, map_mul]
      intro h hx
      rw [mem_ker] at *
      simp [hx]
    }
    {
      rw [map_mul]
      intro h hx
      rw [mem_ker] at *
      simp [hx]
    }
  }
  {
    intro x hx
    rcases h with ⟨P1, Q1, hPQ⟩
    have key : x = aeval φ (P1*P) x + aeval φ (Q1*Q) x := by simpa using congr((aeval φ) $hPQ.symm x)
    rw [key, add_comm]
    apply Submodule.add_mem_sup <;> rw [mem_ker] at *
    { rw [← mul_apply, ← map_mul, show P*(Q1*Q) = Q1*(P*Q) by ring, map_mul, mul_apply, hx, map_zero] }
    { rw [← mul_apply, ← map_mul, show Q*(P1*P) = P1*(P*Q) by ring, map_mul, mul_apply, hx, map_zero] }
  }

example (φ : End K V) (a : K) : φ.eigenspace a = LinearMap.ker (φ - a • 1) :=
  End.eigenspace_def

example (φ : End K V) (a : K) : φ.HasEigenvalue a ↔ φ.eigenspace a ≠ ⊥ :=
  Iff.rfl

example (φ : End K V) (a : K) : φ.HasEigenvalue a ↔ ∃ v, φ.HasEigenvector a v  :=
  ⟨End.HasEigenvalue.exists_hasEigenvector, fun ⟨_, hv⟩ ↦ φ.hasEigenvalue_of_hasEigenvector hv⟩

example (φ : End K V) : φ.Eigenvalues = {a // φ.HasEigenvalue a} :=
  rfl

-- Eigenvalue are roots of the minimal polynomial
example (φ : End K V) (a : K) : φ.HasEigenvalue a → (minpoly K φ).IsRoot a :=
  φ.isRoot_of_hasEigenvalue

-- In finite dimension, the converse is also true (we will discuss dimension below)
example [FiniteDimensional K V] (φ : End K V) (a : K) :
    φ.HasEigenvalue a ↔ (minpoly K φ).IsRoot a :=
  φ.hasEigenvalue_iff_isRoot

-- Cayley-Hamilton
example [FiniteDimensional K V] (φ : End K V) : aeval φ φ.charpoly = 0 :=
  φ.aeval_self_charpoly
