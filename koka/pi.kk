import std/num/float64

pub fun main()
  println("The " ++ pi(0, 0.0).show)

fun pi(n: int, sum : float64): pure float64
  if 100_000_000 < n
  then 4.0 * sum
  else
    val n4 = n.float64 * 4.0;
    pi(n + 1, sum + 2.0 / ((n4 + 1.0) * (n4 + 3.0)))
