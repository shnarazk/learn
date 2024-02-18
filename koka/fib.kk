pub fun main()
  val n = 10000
  println("The " ++ n.show ++ "th fib = " ++ fib(n).show)

fun fib(n: int): div int
  fib_aux(n, 0, 1)

fun fib_aux(n: int, x1: int, x2: int): div int
   if n <= 0 then x1 else fib_aux(n - 1, x2, x1 + x2)
