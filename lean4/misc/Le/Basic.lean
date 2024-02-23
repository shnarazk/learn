import Mathlib.Data.Nat.Basic
import Lean

open Nat
open USize

-- Fibonacchi
def fib : Nat → Nat
  | zero => 0
  | succ zero => 1
  | succ (succ n₂) => fib (n₂ + 1) + fib n₂

-- #eval fib 0
-- #eval fib 1
-- #eval fib 2
-- #eval fib 3
-- #eval fib 4
-- #eval fib 5

lemma fib_is_fib2 (n : Nat) : fib (n + 2) = fib (n + 1) + fib n := by
  induction n with
  | zero => repeat rw [fib]
  | succ n' _ => rw [fib]

-- compute pi
def leibniz₁ (n : Nat) (k: Float) (sum : Float) : Float :=
  match n with
  | zero => sum + 8.0 / 3.0
  | succ n' => leibniz₁ n' (k - 4.0) (sum + 8.0 / ((k + 1.0) * (k + 3.0)))

def leibniz₂ (n : Nat) (sum : Float) : Float :=
  match n with
  | zero => sum + 8.0 / 3.0
  | succ n' =>
      let k := n.toFloat * 4.0
      leibniz₂ n' (sum + 8.0 / ((k + 1.0) * (k + 3.0)))

def leibniz (n : Nat) : Float := leibniz₁ n (n.toFloat * 4.0) 0.0
-- def leibniz (n : Nat) : Float := leibniz₂ n 0.0

def bufsize : USize := 20 * 1024

partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    let stdout ← IO.getStdout
    stdout.write buf
    dump stream

def fileStream (filename : System.FilePath) : IO (Option IO.FS.Stream) := do
  let fileExists ← filename.pathExists
  if not fileExists then
    let stderr ← IO.getStderr
    stderr.putStrLn s!"File not found: {filename}"
    pure none
  else
    let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
    pure (some (IO.FS.Stream.ofHandle handle))

def process (datafilename : String) : IO Unit := do
  let stream ← fileStream ⟨datafilename⟩
  match stream with
    | none => pure ()
    | some stream => dump stream

def readData (datafilename : String) : IO (Array String) := do
     IO.FS.lines datafilename

#eval readData "lakefile.lean"
