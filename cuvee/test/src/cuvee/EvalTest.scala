package cuvee

import cuvee.test.TestSuite
import cuvee.testutils.Implicits._

object EvalTest extends TestSuite {
  private val a: Id = Id("a")
  private val b: Id = Id("b")
  private val x: Id = Id("x")
  private val y: Id = Id("y")
  private val z: Id = Id("z")
  private val int: Sort = Sort("Int")

  test("wp old value with double reassign") {
    // x = x * 2; x = x * 2; y = x;
    val code = Block(List(x := x * 2, x := x * 2, y := x))

    val wp = WP(code, y === Old(x) * 2 * 2)

    val env = Env.empty.bind(List(Formal(x, int), Formal(y, int)))
    val evald = Eval(State.default, None).eval(wp, env, List(env)).asInstanceOf[Eq]

    assertEquals(evald.left, x * 2 * 2)
    assertEquals(evald.left, evald.right)
  }

  test("function call") {
    // define function forward(x) = x
    val state = State.default.define("forward", Proc(formal(a, int), formal(b, int), True, b === a, b := a))
    val env = Env.empty.bind(formal(x, int) ++ formal(y, int))
    val code = Call(Id("forward"), List(x * 2), List(y))
    val wp = WP(code, y === Old(x) * 2)
    val evald = Eval(state, None).eval(wp, env, List(env))
  }

  test("access form") {
    assertEquals(
      Assign.shift(Select(Select(a, x), y), z),
      Pair(a, Store(a, x, Store(Select(a, x), y, z))))
  }

  def formal(id: Id, sort: Sort) = List(Formal(id, sort))

}
