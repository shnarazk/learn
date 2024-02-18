import std/core/string
import std/os/file
import std/os/path

effect<a> ctl yield(item: a): ()

fun iterate(xs: list<a>) : yield<a>()
  match xs
    Cons(x,xx) -> { yield(x); iterate(xx) }
    Nil -> ()

fun foreach(f: a -> e (), action: () -> <yield<a>|e> ()): e ()
  with ctl yield(x) resume(f(x))
  action()

fun foreach2(action: () -> <yield<a>|e> (), f: a -> e ()) : e ()
  with ctl yield(x) resume(f(x))
  action()

fun for-each(xs: list<a>, f: a -> e ()) : e ()
  with ctl yield(x) resume(f(x))
  iterate(xs)

pub fun main(): <fsys,console|_e> ()
  val path = string/realpath("when.kk")
  println("path: " ++ path.show)
  val s = path.read-text-file
  val v = s.split("\n") // .map(fn(l)
  // println(v)
  // foreach(fn(x: int) { println(x) })
  //   list(1, 5).iterate
  // foreach(fn(x: int) { println(x) }, fn() { list(1, 5).iterate })
  foreach2(fn() {list(1, 5).iterate},  fn(x: int) { println(x) })
  // foreach2(fn() {v.iterate},  fn(x: string) { println("> " ++ x) })
  for-each(v, fn(x: string) { println("> " ++ x) })
