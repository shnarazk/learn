structure Foo where
  new ::
  val: Nat
deriving Repr

#eval Foo.new 3

namespace Foo

def inc (self : Foo) : Nat := 1 + self.val
def Foo.inc (self : Foo) : Nat := 1 + self.val
def add (self : Foo) (i : Nat) : Nat := self.val + i
def sub (i : Nat) (self : Foo) : Nat := self.val - i
def merge (self : Foo) (other : Foo): Nat := self.val + other.val

end Foo

#eval (Foo.new 3).inc
#eval Foo.Foo.inc (Foo.new 3)
#eval (Foo.new 3).add 2
#eval (Foo.new 3).sub 2
#eval (Foo.new 3).merge (Foo.new 10)
