import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S03

section
variable (a b : ℝ)

example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)

example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  intro fnhl
  rcases fnhl with ⟨a, fnhl'⟩
  rcases h a with ⟨x, hx⟩
  have xh: a ≤ f x := by apply fnhl' x
  linarith

/-
  b > a について証明したかったのだが、具体例を挙げないといけない。
-/
example : ¬FnHasUb fun x ↦ x := by
  intro fnhu
  rcases fnhu with ⟨a, fnhu'⟩
  have y : a + 1 ≤ a := by apply fnhu' (a + 1)
  linarith
  done

#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)

example (h : Monotone f) (h' : f a < f b) : a < b := by
  apply lt_of_not_ge
  intro AB
  apply absurd h'   -- 矛盾を前提にとれるなら任意の命題をゴールとして残す？
  apply not_lt_of_ge (h AB)

/-
  別解(absurdが必要かと思ったら、linarithで整理するうちに解けてしまった)
-/
example (h : Monotone f) (h' : f a < f b) : a < b := by
  apply lt_of_not_ge
  intro AB
  have h'': f a ≥ f b := by apply h AB
  linarith

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro h1
  have : f a ≤ f b := h1 h
  linarith

-- use counterexample
example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun _ : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := monotone_const
  have h' : f 1 ≤ f 0 := le_refl _
  -- have : 1 ≤ 0 := by apply h monof h' -- 型制約が解消できない!
  have : (1 : ℝ) ≤ 0 := by apply h monof h'
  linarith

/- Use le_of_not_gt
    > In addition to equations and inequalities in the context, linarith will use additional inequalities that you pass as arguments.
-/
example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro xp
  linarith [h x xp]

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  have x0: x ≤ 0 := by exact forall_lt_iff_le'.mp h
  exact x0

/-
  `h x xp`　とはなんなのか展開してみる
-/
example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro xp
  -- h に適切なパラメータを与えてinstantiateしていく
  let _ε3 := h (3 : ℝ) -- 3 > 0 → x < 3
  let _ε0 := h (0 : ℝ) -- 0 > 0 → x < 0
  let _εx := h x       -- x > 0 → x < x := h x xp
  -- 従って2つのパラメータを与えることで矛盾命題を導出できる
  let p := h x xp -- = x < x := h x xj u
  linarith

end

section
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro x p0
  apply h   -- これがわからん
  use x

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  intro x
  rcases x with ⟨x0, p0⟩
  exact absurd p0 (h x0)

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  exact not_forall.mp h


example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  intro pa
  rcases h with ⟨x0, p0⟩
  exact absurd (pa x0) p0

/- 別解作れず -/
example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  by_contra h''
  -- 存在しないと主張する命題に存在する事実を食わせた
  let _panic := h' ⟨x, h''⟩
  exact h' ⟨x, h''⟩  -- `h'に対するrcases`の逆操作のようだ

example (h : ¬¬Q) : Q := by
  apply not_not.mp -- これは `by_contra` と同じこと
  exact h

example (h : ¬¬Q) : Q := by
  by_contra h'
  exact h h'

example (h : Q) : ¬¬Q := by
  by_contra h'
  exact absurd h h'

example (h : Q) : ¬¬Q := by
  intro x
  exact x h

end

section
variable (f : ℝ → ℝ)

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  intro x0
  by_contra h'
  apply h
  use x0
  intro x1
  apply le_of_not_gt
  intro h''
  apply h'
  use x1

example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h

example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  dsimp only [Monotone] at h
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith -- 次節にて説明

end

section
variable (a : ℕ)

example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have _h' : ¬0 < 0 := lt_irrefl 0
  contradiction

end
