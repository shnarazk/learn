import «Le»

-- def onePlusOneIsThree : 1 + 1 = 3 := rfl
def onePlusOneIsTwo : 1 + 1 = 2 := by
  simp

theorem add : 1 + 1 = 2 := by
  simp

theorem append : "Str".append "ing" = "String" := by
  rfl

theorem andImpliesOr : A ∧ B → A ∨ B :=
  fun andEvidence =>
    match andEvidence with
    | And.intro a _ => Or.inl a

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"
