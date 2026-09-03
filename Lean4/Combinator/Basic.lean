module

set_option autoImplicit true

public def I (a : α) := a
public def K (a : α) (_b : β) := a
public def S (x : α → β → γ) (y : α → β) (z : α) := x z (y z)
public def before (y : α → β) (x : β → α → γ) (z : α) : γ := x (y z) z
public def after  (x : α → β → γ) (y : α → β) (z : α) : γ := x z (y z)
public def train (x : α → β) (z : β → γ → ε) (y : α → γ) (a : α) : ε := z (x a) (y a)

infix:80    " ⊸ " => before
infixl:80   " ⟜ " => after

notation:80 " ◀️ " lhs:80 " | " mhs:80 " | " rhs:80 " ▶️ " => train lhs mhs rhs
