effect when<a>
  ctl when(test : bool, block: () -> a ()): ()

fun main(): console ()
  with ctl when(test, block)
    if test then block()
    resume(())
  when(True)
    println("reachable")
  when(False)
    println("unreachable!")
