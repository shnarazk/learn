import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime.Basic
import MIL.Common

section
variable {α : Type*}
variable (s t u : Set α)
open Set

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, mem_inter_iff] at *
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  exact ⟨h xsu.1, xsu.2⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun _x ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x hx
  have xs : x ∈ s := hx.1
  have xtu : x ∈ t ∪ u := hx.2
  rcases xtu with xt | xu
  · left
    show x ∈ s ∩ t
    exact ⟨xs, xt⟩
  . right
    show x ∈ s ∩ u
    exact ⟨xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  . right; exact ⟨xs, xu⟩

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rintro x (⟨left, right⟩ | other)
  {
    simp only [mem_inter_iff, mem_union]
    constructor
    { exact left }
    { left; exact right }
  }
  {
    rcases other with ⟨l,r⟩
    constructor
    { exact l }
    { right ; exact r }
  }

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x xstu
  have xs : x ∈ s := xstu.1.1
  have xnt : x ∉ t := xstu.1.2
  have xnu : x ∉ u := xstu.2
  constructor
  · exact xs
  intro xtu
  -- x ∈ t ∨ x ∈ u
  rcases xtu with xt | xu
  · show False; exact xnt xt
  . show False; exact xnu xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  use xs -- 条件付きの導入されている変数も指定できる
  -- 存在しないオブジェクトを導入したらゴールはFalseになる？
  rintro (xt | xu) <;> contradiction

-- reverse inclusion
example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  rintro x ⟨xx, xntu⟩
  constructor
  {
    use xx
    intro xt
    have xtu : x ∈ t ∪ u := by exact mem_union_left u xt
    exact absurd xtu xntu
  }
  {
    by_contra xu
    have xtu : x ∈ t ∪ u := by exact mem_union_right t xu
    exact absurd xtu xntu
  }

example : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  . rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
  Set.ext fun _x ↦ ⟨fun ⟨xs, xt⟩ ↦ ⟨xt, xs⟩, fun ⟨xt, xs⟩ ↦ ⟨xs, xt⟩⟩

example : s ∩ t = t ∩ s := by ext x; simp [and_comm]

example : s ∩ t = t ∩ s := by
  apply Subset.antisymm
  · rintro x ⟨xs, xt⟩; exact ⟨xt, xs⟩
  . rintro x ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
    Subset.antisymm (fun _ ⟨s, t⟩ ↦ ⟨t, s⟩) (fun _ ⟨s, t⟩ ↦ ⟨t, s⟩)

example : s ∩ (s ∪ t) = s := by
  apply Subset.antisymm
  { rintro x xs; exact xs.left } -- ∩ はleft/rightで分離できる
  {
    rintro x xs
    constructor
    { exact xs }
    { left; exact xs }
  }

example : s ∪ s ∩ t = s := by
  apply Subset.antisymm
  {
    rintro x xs
    simp at xs
    rcases xs with a | b
    { exact a }
    { exact b.left }
  }
  {
    rintro x xs
    left
    exact xs
  }

example : s \ t ∪ t = s ∪ t := by
  apply Subset.antisymm
  {
    rintro x h
    rcases h with (⟨xs, _⟩ | xt)
    { constructor; exact xs }
    { right; exact xt }
  }
  {
    rintro x h
    contrapose! h
    intro ax
    simp at h
    rcases ax with c | c
    { exact absurd c h.left }
    { exact absurd c h.right }
  }

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  apply Subset.antisymm
  {
    rintro x h
    simp
    simp at h
    constructor
    {
      rcases h with ⟨xs, _xnt⟩ | ⟨xt, _xns⟩
      { left; exact xs }
      { right; exact xt }
    }
    {
      intro xss
      rcases h with ⟨_xs, xnt⟩ | ⟨_xt, xns⟩
      { exact xnt }
      { contradiction }
    }
  }
  {
    rintro x h1
    simp
    rcases h1 with ⟨(xs | xt), cap⟩
    {
      simp at cap
      -- have xnt : x ∉ t := cap xs
      left
      constructor
      { exact xs }
      -- { exact xnt }
      { exact (cap xs : x ∉ t) }
   }
    {
      simp at cap
      -- have xns : x ∉ s := by exact fun a ↦ cap a xt
      right
      constructor
      { exact xt }
      -- { exact xns }
      { exact (by exact fun a ↦ cap a xt : x ∉ s) }
   }
  }

def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

example : evens ∪ odds = univ := by
  rw [evens, odds]
  ext n
  simp [-Nat.not_even_iff_odd]
  apply Classical.em

example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False :=
  h

example (x : ℕ) : x ∈ (univ : Set ℕ) :=
  trivial

-- use `Nat.Prime.eq_two_or_odd` and `Nat.even_iff`
example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  intro x h
  simp
  simp at h
  rcases h with ⟨xp, xn2⟩
  rcases Nat.Prime.eq_two_or_odd xp with case1 | case2
  { linarith }
  {
    -- intro st
    exact Nat.odd_iff.mpr case2
    -- have : x % 2 = 0 := Nat.even_iff.mp st
    -- linarith
  }

#print Prime

#print Nat.Prime

example (n : ℕ) : Prime n ↔ Nat.Prime n :=
  Nat.prime_iff.symm

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rw [Nat.prime_iff]
  exact h

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rwa [Nat.prime_iff]

end

section

variable (s t : Set ℕ)

example (h₀ : ∀ x ∈ s, ¬Even x) (h₁ : ∀ x ∈ s, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  constructor
  · apply h₀ x xs
  apply h₁ x xs

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ s, Prime x := by
  rcases h with ⟨x, xs, _, prime_x⟩
  use x, xs

section
variable (ssubt : s ⊆ t)

example (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  have xt : x ∈ t := by exact ssubt xs
  constructor
  { exact h₀ x xt }
  { exact h₁ x xt }

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  rcases h with ⟨x, xs, p⟩
  -- have xt : x ∈ t := ssubt xs
  use x
  constructor
  { exact (ssubt xs : x ∈ t) }
  { exact p.right }

end

end

section
variable {α I : Type*}   -- Type* は識別子それぞれに個別の型を割り当てる
variable (A B : I → Set α)
variable (s : Set α)

open Set

example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by  -- i の型はここでのコンテキストでの型推論から決まる？
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨xs, ⟨i, xAi⟩⟩
    exact ⟨i, xAi, xs⟩
  rintro ⟨i, xAi, xs⟩
  exact ⟨xs, ⟨i, xAi⟩⟩

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · intro h
    constructor
    · intro i
      exact (h i).1
    intro i
    exact (h i).2
  rintro ⟨h1, h2⟩ i
  constructor
  · exact h1 i
  exact h2 i

-- using `by_cases xs : x ∈ s
example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  ext x
  simp
  constructor
  {
    intro h
    rcases h with xs | h'
    {
      intro i
      right
      exact xs
    }
    {
      intro i
      by_cases xs : x ∈ s
      { right ; exact xs }
      { left ; exact h' i }
    }
   }
  {
    rintro iI
    by_cases xs : x ∈ s
    { left ; exact xs }
    {
      right
      rintro i
      have iI1 : ∀ (i : I), (x ∈ A i) ∨ (x ∈ s) := by exact fun i ↦ iI i
      rcases iI1 i with h | h
      { exact h }
      { exact absurd h xs }
    }
  }

def primes : Set ℕ :=
  { x | Nat.Prime x }

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } :=by
  ext
  rw [mem_iUnion₂]
  simp

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } := by
  ext
  simp

example : (⋂ p ∈ primes, { x | ¬p ∣ x }) ⊆ { x | x = 1 } := by
  intro x
  contrapose!
  simp
  apply Nat.exists_prime_and_dvd

/-
If you start typing eq_univ, tab completion will tell you that
`apply eq_univ_of_forall` is a good way to start the proof.
We also recommend using the theorem `Nat.exists_infinite_primes`.
-/
example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  ext x
  simp
  have p1 : ∃i, x ≤ i ∧ i.Prime := Nat.exists_infinite_primes x
  exact inter_nonempty_iff_exists_right.mp p1

end

section

open Set

variable {α : Type*} (s : Set (Set α))

example : ⋃₀ s = ⋃ t ∈ s, t := by
  ext x
  rw [mem_iUnion₂]
  simp

example : ⋂₀ s = ⋂ t ∈ s, t := by
  ext x
  rw [mem_iInter₂]
  rfl

end
