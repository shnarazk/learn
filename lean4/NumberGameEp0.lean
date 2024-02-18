import Mathlib.Data.Nat.Basic
#eval "Hello, World!"
#eval Lean.versionString

-- Natural Number Game in Lean 4 -- ep0

inductive MyNat where
  | zero : MyNat
  | succ : MyNat -> MyNat
  deriving Repr

#check MyNat.zero
#eval MyNat.succ MyNat.zero

open MyNat

def nat_to_mynat (n: Nat): MyNat :=
  match n with
  | Nat.zero => MyNat.zero
  | Nat.succ n' => MyNat.succ (nat_to_mynat n')

def mynat_to_nat (n: MyNat): Nat :=
  match n with
  | MyNat.zero => Nat.zero
  | MyNat.succ n' => Nat.succ (mynat_to_nat n')
  
instance : OfNat MyNat n where
 ofNat := nat_to_mynat n

#eval succ zero

def add (m: MyNat) (n : MyNat) : MyNat :=
  match m with
    | zero => n
    | succ m' => succ (add m' n)

#eval add (succ (succ zero)) (succ zero)
#eval add (nat_to_mynat 7) (nat_to_mynat 3)

example : add 7 3 = 10 := rfl
example : mynat_to_nat (add 7 3) = 10 := rfl

def mul (m n : MyNat) : MyNat :=
  match m with
  | zero => zero
  | succ m' => add n (mul m' n)

example : mul 5 3 = 15 := rfl
example : mul 5 0 = 0 := rfl
example : mul 0 5 = 0 := rfl
