package cuvee.ai

import cuvee.pure._
import cuvee.imp._
import cuvee.State
import cuvee.smtlib.DefineProc
import cuvee.smtlib.Cmd
import cuvee.pipe.Stage

case class CState(vars: Map[Var, Any])

object CState {
  val empty = CState(Map.empty)
}

class Concrete(state: State) {
  object Known {
    val list = state.cons("list")
    val nil = state.funs("nil", 0)
    val cons = state.funs("cons", 2)
    val head = state.funs("head", 1)
    val tail = state.funs("tail", 1)
    val contains = state.funs("contains", 2) 
  }

  def init(typ: Type): Any = typ match {
    case Sort.int => BigInt(1)
    case Sort.bool => true
    case Sort.real => BigDecimal(1.0)
    case Sort(_, List(a)) => List(init(a))
  }

  def init(x: Var, typ: Type, st: CState): CState = {
    val value = init(typ)
    assign(x, value, st)
  }

  def init(x: Var, value: Any, st: CState): CState = {
    st.copy(vars = st.vars + (x -> value))
  }

  def local(xs: List[Var], rhs: List[Expr], states: List[CState]): List[CState] = {
    states.flatMap { s =>
      var s_ = s

      if (rhs.isEmpty) {
        xs.foreach { x =>
          val temp = init(x, x.typ, s_)
          s_ = s_.copy(vars = s_.vars + (x -> temp.vars(x)))
        }
      } else {
        xs.zip(rhs).foreach { case (x, r) =>
          val value = eval(r, s_) 
          s_ = s_.copy(vars = s_.vars + (x -> value))
        }
      }

      if (s_ != CState(Map.empty)) {
        List(s_)
      } else {
        List()
      }
    }
  }

  def assign(x: Var, value: Any, st: CState): CState = {
    st.copy(vars = st.vars + (x -> value)) 
  }

  def assign(xs: List[Var], rhs: List[Expr], states: List[CState]): List[CState] = {
    states.map { s =>
      xs.zip(rhs).foldLeft(s) { (currentState, assignment) =>
        val (variable, expression) = assignment
        val value = eval(expression, currentState)
        currentState.copy(vars = currentState.vars + (variable -> value))
      }
    }
  }

  def eval(expr: Expr, st: CState): Any = expr match {
    case Lit(value, _) => value
    case x: Var => st.vars.getOrElse(x, throw new RuntimeException(s"Variable $x not found"))
    case App(inst, args) =>  apply(inst, args map (eval(_, st)),st)
  }

  def apply(inst: Inst, args: List[Any], st: CState): Any = (inst.fun, args) match {
    //Boolean
    case (Fun.true_, Nil) => true
    case (Fun.false_, Nil) => false
    case (Fun.and, List(arg1: Boolean, arg2: Boolean)) => arg1 && arg2
    case (Fun.or, List(arg1: Boolean, arg2: Boolean)) => arg1 || arg2
    case (Fun.imp, List(arg1: Boolean, arg2: Boolean)) => !arg1 || arg2
    case (Fun.eq_, List(arg1: Boolean, arg2: Boolean)) => arg1 == arg2
    case (Fun.not, List(arg1: Boolean, arg2: Boolean)) => arg1 != arg2
    case (Fun.not, List(arg1: Boolean)) => !arg1

    // BigInt
    case (Fun.uminus, List(arg: BigInt)) => -arg
    case (Fun.plus, List(arg1: BigInt, arg2: BigInt)) => arg1 + arg2
    case (Fun.minus, List(arg1: BigInt, arg2: BigInt)) => arg1 - arg2
    case (Fun.times, List(arg1: Int, arg2: BigInt)) => arg1 * arg2
    case (Fun.div, List(arg1: BigInt, arg2: BigInt)) => arg1 / arg2
    case (Fun.gt, List(arg1: BigInt, arg2: BigInt)) => arg1 > arg2
    case (Fun.ge, List(arg1: BigInt, arg2: BigInt)) => arg1 >= arg2
    case (Fun.lt, List(arg1: BigInt, arg2: BigInt)) => arg1 < arg2
    case (Fun.le, List(arg1: BigInt, arg2: BigInt)) => arg1 <= arg2
    case (Fun.eq_, List(arg1: BigInt, arg2: BigInt)) => arg1 == arg2
    case (Fun.not, List(arg1: BigInt, arg2: BigInt)) => arg1 != arg2

    //List
    case (Known.nil, Nil) => Nil
    case (Known.cons, List(arg1: Any, arg2: List[_])) => arg1 :: arg2
    case (Known.head, List(arg1: List[Any])) => arg1.head
    case (Known.tail, List(arg1: List[Any])) => arg1.tail
    case (Known.contains, List(arg1: List[Any], arg2: Any)) => arg1.contains(arg2)
    case (Fun.eq_, List(arg1: List[Any], arg2: List[Any])) => arg1 == arg2
    case (Fun.not, List(arg1: List[Any], arg2: List[Any])) => arg1 != arg2
  }

  //Testing
  def and_positive(phis: List[Expr], st: List[CState]): List[CState] = phis match {
    case Nil => st
    case first :: rest => and_positive(rest, positive(first, st))
  }

  def and_negative(phis: List[Expr], st: List[CState]): List[CState] = phis match {
    case Nil => List()
    case first :: rest => negative(first, st) ++ and_negative(rest, positive(first, st))
  }

  def or_positive(phis: List[Expr], st: List[CState]): List[CState] = phis match {
    case Nil => List()
    case first :: rest => positive(first, st) ++ or_positive(rest, negative(first, st))
  }

  def or_negative(phis: List[Expr], st: List[CState]): List[CState] = phis match {
    case Nil => st
    case first :: rest => or_negative(rest, negative(first, st))
  }

  def positive(phi: Expr, st: List[CState]): List[CState] = phi match {
    case True =>
      st

    case False =>
      List()

    case x: Var =>
      st flatMap { s =>
        s.vars(x) match {
          case true  => List(s)
          case false => List()
        }
      }

    case And(phis) =>
      and_positive(phis, st)

    case Or(phis) =>
      or_positive(phis, st)

    case Imp(phi, psi) =>  // with (A => B) <=> (¬A ∨ B)
      val notPhi = Not(phi) // ¬A
      val orResult = Or(List(notPhi, psi)) // ¬A ∨ B
      or_positive(List(orResult), st)

    case Not(phi) =>
      negative(phi, st)

    case Eq(x: Expr, y: Expr) =>
      st.flatMap { s =>
        val xVal = eval(x, s)
        val yVal = eval(y, s)
        if (xVal == yVal) List(s) else List()
      }
      
    case Le(x: Expr, y: Expr) =>
      st.flatMap { s =>
        (eval(x, s), eval(y, s)) match {
          case (xVal: BigInt, yVal: BigInt) =>
            if (xVal <= yVal) List(s) else List()
          case _ => List()
        }
      }

    case Lt(x: Expr, y: Expr) =>
      st.flatMap { s =>
        (eval(x, s), eval(y, s)) match {
          case (xVal: BigInt, yVal: BigInt) =>
            if (xVal < yVal) List(s) else List()
          case _ => List()
        }
      }

    case Ge(x: Expr, y: Expr) => 
      val phi_le : Expr = Le(y,x) 
      positive(phi_le, st)

    case Gt(x: Expr, y: Expr) => 
      val phi_lt : Expr = Lt(y,x) 
      positive(phi_lt, st) 
  }

  def negative(phi: Expr, st: List[CState]): List[CState] = phi match {
    case True =>
      List()

    case False =>
      st

    case x: Var =>
      st flatMap { s =>
        s.vars(x) match {
          case true  => List()
          case false => List(s)
        }
      }

    case And(phis) =>
      and_negative(phis, st)

    case Or(phis) =>
      or_negative(phis, st)

    case Imp(phi, psi) => // with (A => B) <=> (¬A ∨ B)
      val notPhi = Not(phi) // ¬A
      val orResult = Or(List(notPhi, psi)) // ¬A ∨ B
      or_negative(List(orResult), st)

    case Not(phi) =>
      positive(phi, st)

    case Eq(x: Expr, y: Expr) =>
      st.flatMap { s =>
        val xVal = eval(x, s)
        val yVal = eval(y, s)
        if (xVal != yVal) List(s) else List()
      }

    case Le(x: Expr, y: Expr) =>
      st.flatMap { s =>
        (eval(x, s), eval(y, s)) match {
          case (xVal: BigInt, yVal: BigInt) =>
            if (xVal > yVal) List(s) else List()
          case _ => List()
        }
      }

    case Lt(x: Expr, y: Expr) =>
      st.flatMap { s =>
        (eval(x, s), eval(y, s)) match {
          case (xVal: BigInt, yVal: BigInt) =>
            if (xVal >= yVal) List(s) else List()
          case _ => List()
        }
      }

    case Ge(x: Expr, y: Expr) => 
      val phi_le : Expr = Le(y,x) 
      negative(phi_le, st)

    case Gt(x: Expr, y: Expr) => 
      val phi_lt : Expr = Lt(y,x) 
      negative(phi_lt, st)  
  }

  def execIf(test: Expr, left: Prog, right: Prog, state: CState): List[CState] = {
    if (eval(test, state).asInstanceOf[Boolean]) {
      exec(left, List(state))
    } else {
      exec(right, List(state))
    }
  }

  def execWhile(test: Expr, body: Prog, state: CState): List[CState] = {
    var currentState = state
    while (eval(test, currentState).asInstanceOf[Boolean]) {
      currentState = exec(body, List(currentState)).head
    }
    List(currentState)
  }

  def exec(prog: Prog, states: List[CState]): List[CState] = prog match {
    case Assign(xs, rhs) => assign(xs, rhs, states)
    case If(test, left, right) => states.flatMap(s => execIf(test, left, right, s))
    case While(test, body, _, _, _, _) => states.flatMap(s => execWhile(test, body, s))
    case Block(progs) => progs.foldLeft(states)((st, p) => exec(p, st))
    case Local(xs, rhs) => local(xs, rhs, states)
    case Spec(Nil, True, psi) => positive(psi, states) //assume
    case Spec(Nil, phi, True) => // assert
      val ps = positive(phi, states)
      val ng = negative(phi, states)
      if (ng.isEmpty) ps
      else throw new Exception("Exception occured while executing Assert. Reason: negative Test is not empty is not empty: " + ng)
  }
}

object Concrete extends Stage {

  def exec(prefix: List[Cmd], cmds: List[Cmd], last: Cmd, state: cuvee.State): List[Cmd] = {
    cmds.flatMap {
      case DefineProc(name, params, in, out, spec, body) =>
        val proc = Proc(name, params, in, out, spec)
        val c = new Concrete(state)
        var st_c: CState = CState.empty

        for (x <- in ++ out) {
          st_c = c.init(x, x.typ, st_c)
        }

        var s_c: List[CState] = List(st_c)
        val res_c = c.exec(body, s_c)
        println("\nConcrete: exec " + name + " = ")
        for (r <- res_c) println(r)
        println()

        List(DefineProc(name, params, in, out, spec, body))

      case cmd =>
        List(cmd)
    }
  }
}