set_option autoImplicit true

def I (a : α) := a
def K (a : α) (_b : β) := a
def S (x : α → β → γ) (y : α → β) (z : α) := x z (y z)
def before (y : α → β) (x : β → α → γ) (z : α) : γ := x (y z) z
def after  (x : α → β → γ) (y : α → β) (z : α) : γ := x z (y z)
def train (x : α → β) (z : β → γ → ε) (y : α → γ) (a : α) : ε := z (x a) (y a)

infix:80    " ⊸ " => before
infixl:80   " ⟜ " => after

notation:80 " ◀️ " lhs:80 " | " mhs:80 " | " rhs:80 " ▶️ " => train lhs mhs rhs
