import «Le»

def main : IO Unit := do
  IO.println s!"fib 20 = {fib 20} ."
  IO.println s!"pi = {leibniz 10000000} ."
  let lines ← readData "lakefile.lean"
  lines.forM IO.println
  let x ← IO.getEnv "HOME"
  match x with
  | some x => IO.println x
  | none => pure ()
