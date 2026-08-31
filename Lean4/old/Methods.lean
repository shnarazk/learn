structure Foo where
  -- mk ::
  val: Nat
deriving Repr

#eval Foo.mk 3

namespace Foo

def inc (self : Foo) : Nat := 1 + self.val
def Foo.inc (self : Foo) : Nat := 1 + self.val
def add (self : Foo) (i : Nat := 1) : Nat := self.val + i
def sub (self : Foo) (i : Nat := 1) : Nat := self.val - i
def merge (self : Foo) (other : Foo): Nat := self.val + other.val

end Foo

#eval (Foo.mk 3).inc
#eval Foo.Foo.inc (Foo.mk 3)
#eval (Foo.mk 3).add 2
#eval (Foo.mk 3).add
#eval (Foo.mk 3).sub 2
#eval (Foo.mk 3).merge (Foo.mk 10)
