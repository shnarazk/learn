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

instance : Add MyNat where
  add := add

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

instance : Mul MyNat where
  mul := mul

lemma example1 (x y z : MyNat) : x * y + z = x * y + z := by
  rfl

lemma example2 (x y : MyNat) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  rewrite [h]
  rfl

lemma example3 (a b : MyNat) (h : succ a = b) : succ (succ a) = succ b := by
  rewrite [h]
  rfl

lemma my_add_zero_left (a : MyNat) : zero + a = a := by
  rfl

lemma my_add_succ_left (a b : MyNat) : succ a + b = succ (a + b) := by
  rfl

lemma my_add_zero_right (a : MyNat) : a + zero = a := by
  induction a with
  | zero => rfl
  | succ a' ih => rewrite [my_add_succ_left, ih]; rfl

lemma my_add_succ_right (a b : MyNat) : a + succ b = succ (a + b) := by
  induction a with
    | zero => rewrite [my_add_zero_left, my_add_zero_left]; rfl
    | succ a' ih => rewrite [my_add_succ_left, ih]; rfl

lemma my_add_succ_zero (a : MyNat) : (succ zero) + a = succ a := by
  rewrite [my_add_succ_left, my_add_zero_left]
  rfl

lemma my_add_is_commutive (x y : MyNat) : x + y = y + x := by
  induction x with
  | zero => rewrite [my_add_zero_left, my_add_zero_right]; rfl
  | succ x' ih => rewrite [my_add_succ_right, my_add_succ_left, ih]; rfl

lemma my_add_assoc (a b c : MyNat) : (a + b) + c = a + (b + c) := by
  induction c with
    | zero => rewrite [my_add_zero_right, my_add_zero_right]; rfl
    | succ c' ih => rewrite [my_add_succ_right, my_add_succ_right, my_add_succ_right, ih]; rfl

example : 2 + (5 + 8) = (2 + 5) + 8 := rfl
