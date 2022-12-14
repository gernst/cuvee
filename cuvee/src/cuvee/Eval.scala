package cuvee

case class Env(su: Map[Id, Expr], ty: Map[Id, Type]) {
  def contains(id: Id) = su contains id
  def apply(id: Id) = su apply id

  def now = {
    val re = Expr.id(su.keys)
    Env(re, ty)
  }

  def eqs = {
    Eq.zip(su.toList)
  }

  def check(xs: Iterable[Id]) {
    for (x <- xs) {
      ensure(su contains x, "undeclared variable", x, su.keySet)
      ensure(ty contains x, "no type for variable", x, ty.keySet)
    }
  }

  def bind(fs: List[Formal]): Env = {
    val xs = fs map (_.id)
    val bound = xs filter su.contains
    if (bound.nonEmpty) {
      error(s"already bound: $bound")
    }
    val ts = fs map (_.typ)
    val re = Expr.id(xs)
    val xt = xs zip ts
    Env(su ++ re, ty ++ xt)
  }

  def assignUnchecked(xs: List[Id], es: List[Expr]): Env = {
    Env(su ++ (xs zip es), ty)
  }

  def assign(xs: List[Id], es: List[Expr]): Env = {
    check(xs)
    assignUnchecked(xs, es)
  }

  def havoc(xs: Iterable[Id]): (List[Formal], Env) = {
    check(xs)
    val re = Expr.fresh(xs)
    val formals = xs map (x => Formal(x rename re, ty(x)))
    val env = Env(su ++ re, ty)
    (formals.toList, env)
  }

  override def toString = {
    val strings = su map { case (x, e) => Pair(x, e) }
    strings.mkString("(", " ", ")")
  }
}

object Env {
  val empty = Env(Map.empty, Map.empty)
}

case class Path(fresh: List[Formal], path: List[Expr], env: Env) {
  def ::(phi: Expr) = {
    Path(fresh, phi :: path, env)
  }

  def bind(fs: List[Formal]) = {
    Path(fresh ++ fs, path, env)
  }

  def toExpr = {
    Exists(fresh, And(env.eqs ++ path))
  }
}

object Path {
  val empty = Path(List.empty, List.empty, Env.empty)
}

object Eval {
  var inferInvariants = false
}

case class Eval(st: State, context: Option[Obj]) {
  def inContext(ctx: Option[Option[Obj]]): Eval = ctx.map(Eval(st, _)).getOrElse(this)

  def eval(expr: Expr): Expr = {
    val old = Nil
    val env = st.env
    eval(expr, env, old)
  }

  def eval(let: Pair, env: Env, old: List[Env]): (Id, Expr) = let match {
    case Pair(x, e) => (x, eval(e, env, old))
  }

  def eval(expr: Expr, env: Env, old: List[Env]): Expr = expr match {
    case num: Num =>
      num

    case id: Id if (env contains id) =>
      env(id)

    case id: Id if (st.funs contains id) =>
      val (args, res) = st funs id
      ensure(args.isEmpty, "not constant", expr, env)
      id

    case _: Id =>
      error("unknown identifier", expr, env)

    case Old(inner) =>
      old match {
        case Nil =>
          error("no old state", expr, env)
        case env :: old =>
          eval(inner, env, old)
      }

    case Note(expr, attrs) =>
      val _expr = eval(expr, env, old)
      Note(_expr, attrs)

    case Eq(left, right) =>
      Eq(eval(left, env, old), eval(right, env, old))

    case Ite(test, left, right) =>
      Ite(eval(test, env, old), eval(left, env, old), eval(right, env, old))

    /* case Let(lets, body) =>
      val pairs = lets map (eval(_, env, old))
      val (xs, _es) = pairs.unzip
      eval(body, env assignUnchecked (xs, _es), old) */

    case Select(array, index) =>
      Select(eval(array, env, old), eval(index, env, old))

    case Store(array, index, value) =>
      Store(eval(array, env, old), eval(index, env, old), eval(value, env, old))

    case Distinct(args) =>
      Distinct(args map (eval(_, env, old)))

    case UMinus(arg) =>
      UMinus(eval(arg, env, old))

    case App(id, args) if (st.funs contains id) =>
      val (types, res) = st funs id
      ensure(args.length == types.length, "wrong number of arguments", expr, env)
      App(id, args map (eval(_, env, old)))

    case App(id, args) =>
      error("unknown function", id, expr, env)

    case bind@Bind(_, _, _) =>
      val avoid = bind.avoid(env.su.keySet)
      val Bind(quant, formals, body) = bind.rename(avoid, avoid)
      quant(formals, eval(body, env bind formals, old))

    case expr @ Match(arg, cases) =>
      ???

    case WP(prog, post) =>
      wp(List(prog), None, post, env, old)

    case Box(prog, post) =>
      box(List(prog), None, post, env, old)

    case Dia(prog, post) =>
      dia(List(prog), None, post, env, old)

    case Refines(a, c, r) =>
      eval(Verify.refinementCondition(st.objects(a), st.objects(c), r), env, old)
  }

  def wp(progs: List[Prog], break: Option[Expr], post: Expr, env0: Env, old: List[Env]): Expr = progs match {
    case Nil =>
      eval(post, env0, old)

    case Break :: rest =>
      break match {
        case Some(post) =>
          eval(post, env0, old)
        case None =>
          error("break not within while", break, env0)
      }

    case Block(progs, withOld, ctx) :: rest =>
      val old_ = if (withOld) env0 :: old else old
      inContext(ctx).wp(progs ++ rest, break, post, env0, old_)

    case Assign(lets) :: rest =>
      val pairs = lets map (eval(_, env0, old))
      val (xs, _es) = pairs.unzip
      val env1 = env0 assign (xs, _es)
      wp(rest, break, post, env1, old)

    case Spec(xs, phi, psi) :: rest =>
      val (formals, env1) = env0 havoc xs
      val _phi = eval(phi, env0, old)
      val _psi = eval(psi, env1, env0 :: old)
      _phi && Forall(formals, _psi ==> wp(rest, break, post, env1, old))

    case Choose(xs, phi) :: rest =>
      val (formals, env1) = env0 havoc xs
      val _phi = eval(phi, env1, env0 :: old)
      Exists(formals, _phi) && Forall(formals, _phi ==> wp(rest, break, post, env1, old))

    case If(test, left, right) :: rest =>
      val _test = eval(test, env0, old)
      val _left = _test ==> wp(left :: rest, break, post, env0, old)
      val _right = !_test ==> wp(right :: rest, break, post, env0, old)
      _left && _right

    case While(test, body, after, term, phi, psi) :: rest =>
      val mod = body.mod
      val mod_ = mod.toList

      val (formals, env1) = env0 havoc mod

      val _test = eval(test, env1, env1 :: old)
      val decrease = test ==> (0 <= term && term < Old(term))

      val hyp = Spec(mod_, decrease && phi, /* !test && */ psi)

      val _phi0 = eval(phi, env0, old)
      val _psi0 = eval(psi, env1, env0 :: old)

      val _phi1 = eval(phi, env1, old)
      val _psi1 = eval(psi, env1, env1 :: old)

      val use = _phi0 && Forall(formals, _psi0 ==> wp(rest, break, post, env1, old))
      val base = Forall(formals, (!_test && _phi1) ==> wp(List(after), break, psi, env1, env1 :: old))
      val step = Forall(formals, (_test && _phi1) ==> wp(List(body, hyp), Some(psi), psi, env1, env1 :: old))

      use && base && step

    case Call(name, in, out) :: rest if isProcDefined(name) =>
      val (formals, prog) = contract(name, out, in)
      Forall(formals, wp(prog :: rest, break, post, env0 bind formals, old))

    case Call(name, _, _) :: _ =>
      error("unknown procedure", name)
  }

  private def isProcDefined(name: Id) = {
    context.flatMap(ctx => ctx.op(name)).isDefined || (st.procdefs contains name)
  }

  def contract(name: Id, out: List[Id], in: List[Expr]): (List[Formal], Prog) = {
    val (inObj, proc) = (context.flatMap(_.op(name)), st.procdefs.get(name)) match {
      case (Some(objProc), _) => (true, objProc)
      case (_, Some(globalProc)) => (false, globalProc)
      case _ => ??? // we checked that this cannot be the case
    }

    val Proc(xs, ys, pre, post, body) = proc

    val su1 = Expr.subst(xs, in)
    val _pre = pre subst su1
    post match {
      case True =>
        val Some(Body(locals, body_)) = body

        // rename everything in body except for possibly class variables
        val xs_ = xs.fresh
        val locals_ = locals.fresh
        val ys_ = ys.fresh
        val oldVars: List[Id] = xs ++ locals ++ ys
        val newVars: List[Id] = xs_ ++ locals_ ++ ys_
        val re = oldVars zip newVars toMap
        val body__ : List[Prog] = body_ map (_.replace(re))

        // assign inputs before body and outputs after body
        val assIn: List[Assign] = if(xs_.isEmpty) Nil else List(Assign.zip(xs_, in))
        val assOut: List[Assign] = if(ys_.isEmpty) Nil else List(Assign.zip(out, ys_))

        val inlined: List[Prog] = Spec.assert(_pre) :: assIn ++ body__ ++ assOut
        val prog: Prog = Block(inlined, false, if (inObj) Some(context) else None)
        (xs_ ++ locals_ ++ ys_, prog: Prog)
      case post =>
        val su2 = Expr.subst(ys, out)
        val _post = post subst (su1 ++ su2)

        (Nil, Spec(out, _pre, _post))
    }
  }

  def box(progs: List[Prog], break: Option[Expr], post: Expr, env0: Env, old: List[Env]): Expr = progs match {
    case Nil =>
      eval(post, env0, old)

    case Break :: rest =>
      break match {
        case Some(post) =>
          eval(post, env0, old)
        case None =>
          error("break not within while", break, env0)
      }

    case Block(progs, withOld, ctx) :: rest =>
      val old_ = if (withOld) env0 :: old else old
      inContext(ctx).box(progs ++ rest, break, post, env0, old_)

    case Assign(lets) :: rest =>
      val pairs = lets map (eval(_, env0, old))
      val (xs, _es) = pairs.unzip
      val env1 = env0 assign (xs, _es)
      box(rest, break, post, env1, old)

    case Spec(mod, phi, psi) :: rest =>
      val (formals, env1) = env0 havoc mod
      val _phi = eval(phi, env0, old)
      val _psi = eval(psi, env1, env0 :: old)
      _phi && Forall(formals, _psi ==> box(rest, break, post, env1, old))

    case Choose(xs, phi) :: rest =>
      val (formals, env1) = env0 havoc xs
      val _phi = eval(phi, env1, env0 :: old)
      Forall(formals, _phi ==> box(rest, break, post, env1, old))

    case If(test, left, right) :: rest =>
      val _test = eval(test, env0, old)
      val _left = _test ==> box(left :: rest, break, post, env0, old)
      val _right = !_test ==> box(right :: rest, break, post, env0, old)
      _left && _right

    /* case While(test, body, Skip, term, phi, True) :: rest =>
      val mod = body.mod
      val mod_ = mod.toList

      var inv = phi

      val (formals, env1) = env0 havoc mod

      val _test1 = eval(test, env1, env1 :: old)

      if (inferInvariants) {
        val (others, env2) = env0 havoc mod
        // ??? s'. ?? test s' ??? I s' ??? Q s s' ??? Q s0 s'
        val _test2 = eval(test, env2, env1 :: old)
        val _inv2 = eval(phi, env2, env1 :: old)

        val post1 = eval(post, ???)
        // s0 == env0
        // s  == env1
        // s' == env2
        /* Forall(
            others,
          */
      }

      val _inv0 = eval(inv, env0, old)
      val _inv1 = eval(inv, env1, old)

      val init = Forall(formals, (!_test1 && _inv1) ==> box(rest, break, post, env1, env1 :: old))
      val step = Forall(formals, (_test1 && _inv1) ==> box(List(body), Some(inv), inv, env1, env1 :: old))

      _inv0 && init && step */

    case While(test, body, after, term, phi, psi) :: rest =>
      val mod = body.mod
      val mod_ = mod.toList

      val (formals, env1) = env0 havoc mod

      val _test = eval(test, env1, env1 :: old)

      val hyp = Spec(mod_, phi, /* !test && */ psi)

      val _phi0 = eval(phi, env0, old)
      val _psi0 = eval(psi, env1, env0 :: old)

      val _phi1 = eval(phi, env1, old)
      val _psi1 = eval(psi, env1, env1 :: old)

      val use = _phi0 && Forall(formals, _psi0 ==> box(rest, break, post, env1, old))
      val base = Forall(formals, (!_test && _phi1) ==> box(List(after), break, psi, env1, env1 :: old))
      val step = Forall(formals, (_test && _phi1) ==> box(List(body, hyp), Some(psi), psi, env1, env1 :: old))

      use && base && step

    case Call(name, in, out) :: rest if isProcDefined(name) =>
      val (formals, prog) = contract(name, out, in)
      Forall(formals, box(prog :: rest, break, post, env0 bind formals, old))

    case Call(name, _, _) :: rest =>
      error("unknown procedure", name)
  }

  def dia(progs: List[Prog], break: Option[Expr], post: Expr, env0: Env, old: List[Env]): Expr = progs match {
    case Nil =>
      eval(post, env0, old)

    case Break :: rest =>
      break match {
        case Some(post) =>
          eval(post, env0, old)
        case None =>
          error("break not within while", break, env0)
      }

    case Block(progs, withOld, ctx) :: rest =>
      val old_ = if (withOld) env0 :: old else old
      inContext(ctx).dia(progs ++ rest, break, post, env0, old_)

    case Assign(lets) :: rest =>
      val pairs = lets map (eval(_, env0, old))
      val (xs, _es) = pairs.unzip
      val env1 = env0 assign (xs, _es)
      dia(rest, break, post, env1, old)

    case Spec(mod, phi, psi) :: rest =>
      val (formals, env1) = env0 havoc mod
      val _phi = eval(phi, env0, old)
      val _psi = eval(psi, env1, env0 :: old)
      _phi && Exists(formals, _psi && dia(rest, break, post, env1, old))

    case Choose(xs, phi) :: rest =>
      val (formals, env1) = env0 havoc xs
      val _phi = eval(phi, env1, env0 :: old)
      Exists(formals, _phi && dia(rest, break, post, env1, old))

    case If(test, left, right) :: rest =>
      val _test = eval(test, env0, old)
      val _left = _test && dia(left :: rest, break, post, env0, old)
      val _right = !_test && dia(right :: rest, break, post, env0, old)
      _left || _right

    case While(test, body, after, term, phi, psi) :: rest =>
      val mod = body.mod
      val mod_ = mod.toList

      val (formals, env1) = env0 havoc mod

      val _test = eval(test, env1, env1 :: old)
      val decrease = test ==> (0 <= term && term < Old(term))

      val hyp = Spec(mod_, decrease && phi, /* !test && */ psi)

      val _phi0 = eval(phi, env0, old)
      val _psi0 = eval(psi, env1, env0 :: old)

      val _phi1 = eval(phi, env1, old)
      val _psi1 = eval(psi, env1, env1 :: old)

      error("loop rule for dia likely incorrect")
      val use = _phi0 && Exists(formals, _psi0 && dia(rest, break, post, env1, old))
      val base = Forall(formals, (!_test && _phi1) ==> dia(List(after), break, psi, env1, env1 :: old))
      val step = Forall(formals, (_test && _phi1) ==> dia(List(body, hyp), Some(psi), psi, env1, env1 :: old))

      use && base && step

    case Call(name, in, out) :: rest if isProcDefined(name) =>
      val (formals, prog) = contract(name, out, in)
      Forall(formals, dia(prog :: rest, break, post, env0 bind formals, old))

    case Call(name, _, _) :: rest =>
      error("unknown procedure", name)
  }

  def rel(body: Body, env0: Env, old: List[Env]): List[Path] = {
    val Body(locals, progs) = body
    val env1 = env0 bind locals
    rel(progs, env1, old)
  }

  def rel(progs: List[Prog], env0: Env, old: List[Env]): List[Path] = progs match {
    case Nil =>
      List(Path(List.empty, List.empty, env0))

    case Break :: rest =>
      error("break not within while", env0)

    case Block(progs, withOld, ctx) :: rest =>
      val old_ = if (withOld) env0 :: old else old
      inContext(ctx).rel(progs ++ rest, env0, old_)

    case Assign(lets) :: rest =>
      val pairs = lets map (eval(_, env0, old))
      val (xs, _es) = pairs.unzip
      val env1 = env0 assign (xs, _es)
      rel(rest, env1, old)

    case Spec(mod, phi, psi) :: rest =>
      val (formals, env1) = env0 havoc mod
      val _phi = eval(phi, env0, old)
      val _psi = eval(psi, env1, env0 :: old)
      for (path <- rel(rest, env1, old))
        yield _phi :: _psi :: path bind formals

    case Choose(xs, phi) :: rest =>
      val (formals, env1) = env0 havoc xs
      val _phi = eval(phi, env1, env0 :: old)
      for (path <- rel(rest, env1, old))
        yield _phi :: path bind formals

    case If(test, left, right) :: rest =>
      val _test = eval(test, env0, old)
      val _left = for (path <- rel(left :: rest, env0, old))
        yield _test :: path
      val _right = for (path <- rel(right :: rest, env0, old))
        yield !_test :: path
      _left ++ _right

    case While(test, body, after, term, phi, psi) :: rest =>
      val mod = body.mod ++ after.mod
      val mod_ = mod.toList
      val spec = Spec(mod_, phi, /* !test && */ psi)
      rel(spec :: rest, env0, old)

    case Call(name, in, out) :: rest if isProcDefined(name) =>
      val (formals, prog) = contract(name, out, in)
      rel(prog :: rest, env0 bind formals, old).map(p => Path(p.fresh ++ formals, p.path, p.env))

    case Call(name, _, _) :: rest =>
      error("unknown procedure", name)
  }

  /**
   * Determine all paths through proc (splitting conditionals)
   *  wrt. state parameters ps, such that the path takes a transition from xs0 to xs1.
   *  Return the instantiated precondition as well as the paths,
   *  which store constraints and variable assignments for xs1 in the successor states.
   */
  def forward(proc: Proc, ps: List[Formal], in: List[Formal], out: List[Formal], init: List[Expr]): List[(Expr, Path)] = {
    val xs: List[Id] = ps
    val (pre, post, body) = proc call (ps, xs, in, out)

    val env0 = Env.empty
    val env1 = env0 bind (ps ++ in ++ out)
    val env2 = env1.assign(xs, init)
    val old = Nil
    val _pre = eval(pre, env2, old)
    val paths = rel(body, env2, old)

    for (path <- paths)
      yield (_pre, path)
  }

  def paths(proc: Proc, ps: List[Formal], init: List[Expr], in: List[Expr]): (Expr, List[Path]) = {
    val (xi, xo, pre, post, body) = proc call ps
    var env = Env.empty
    env = env bind (ps ++ xi ++ xo)
    env = env assign (ps, init)
    env = env assign (xi, in)
    val old = Nil

    val _pre = eval(pre, env, old)
    val paths = rel(body, env, old)

    (_pre, paths)
  }
}