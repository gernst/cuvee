package cuvee.ai
import cuvee.util._
import cuvee.pure._
import cuvee.State
import cuvee.imp._
import cuvee.pipe.Stage
import cuvee.smtlib.DefineProc
import cuvee.smtlib.Cmd

//State
case class AState(vars: Map[Var, ARef], refs: Map[ARef, AVal]){
  
  def format(r: ARef): String =
    format(refs(r))

  def format(v: AVal): String = v match {
    case ACons(a, as) =>
      "ACons("+ format(a) + "," + format(as) + ")"
    case AMany(a) =>
      "AMany("+ format(a) + ")"
    case _ =>
      v.toString()
  }

  override def toString =
     (vars map { case (x, r) => x -> format(r)}).mkString("AState(", ", ", ")")
}

object AState {
  val empty = AState(Map(), Map())
}

class Abstract(state: State) extends Interpreter[AState]{

  object Known {
    val list = state.cons("list")
    val nil = state.funs("nil", 0)
    val cons = state.funs("cons", 2)
    val head = state.funs("head", 1)
    val tail = state.funs("tail", 1)
    val contains = state.funs("contains", 2) 
  }
  
  //refines a reference value
  def refine(r: ARef, v: AVal, st: AState) = {
   st.copy(refs = st.refs + (r -> v)) 
  }

  // Refines reference values for multiple references and values
  def refine(refsAndValues: List[(ARef, AVal)], st: AState): AState = {
    st.copy(refs = st.refs ++ refsAndValues.toMap)
  }

  def reference(): ARef = {
    ARef.fresh()
  }

  // creates a new reference (ARef -> AVal)
  def reference(a: AVal, st: AState): (ARef, AState) = {
    val ref = reference()
    (ref, refine(ref, a, st))
  }

  // updates a reference (Name -> ARef)
  def assign(a: Var, value: ARef, st: AState): AState = {
    st.copy(vars = st.vars + (a -> value)) 
  }

  def assign(xs: List[Var], rhs: List[Expr], states: List[AState]): List[AState] = {
    xs.zip(rhs).foldLeft(states) { (currentStates, pair) =>
      val (a, expr) = pair
      currentStates.map { st =>
        val (ref, st_) = eval(expr, st)
        assign(a, ref, st_)
      }
    }
  }

  def init(typ: Type, st: AState): (ARef, AState) = typ match {
    case Sort.bool =>
      val ref = reference()
      (ref, refine(ref, AUnknown, st)) 

    case Sort.int =>
      val ref = reference()
      (ref, refine(ref, AInt.top, st)) 

    case Sort(Known.list, List(a)) =>
      val ref = reference()
      val (ref_a, st_) = init(a, st)
      (ref, refine(ref, AMany(ref_a), st_))
  }

  // init variable with a default value
  def init(a: Var, typ: Type, st: AState): AState = {
    val (ref, st_) = init(typ, st)
    assign(a, ref, st_)
  }

  // init variable with a specific value
  def init(a: Var, value: AVal, st: AState): AState = {
    val ref = reference()
    st.copy(vars = st.vars + (a -> ref), refs = st.refs + (ref -> value))
  }

  def local(xs: List[Var], rhs: List[Expr], states: List[AState]): List[AState] = {
    var st_ : List[AState] = List()
    for (s <- states) yield {
      var s_ = s
      
      if (rhs.isEmpty) {
        for (x <- xs) {
          s_ = init(x, x.typ, s_)
          st_ = st_ :+ s_
        }
      } else {
        for ((x, r) <- xs zip rhs) {
          val (v_, s__) = eval(r, s_)
          s_ = assign(x, v_, s__)
          st_ = st_ :+ s_
        }
      }
    }
    st_
  }

  def lit(a: Any): AVal = a match{
    case i: BigInt => AInt(i)
  }

  def lookup(a: Var, st: AState): ARef = {
    st.vars(a)
  }

  def apply(inst: Inst, args: List[ARef], st: AState): (ARef, AState) = (inst.fun, args map st.refs) match {
    // ABool
    case (Fun.true_, Nil) =>
      reference(ATrue, st)

    case (Fun.false_, Nil) =>
      reference(AFalse, st)

    case (Fun.and, List(arg1: ABool, arg2: ABool)) =>
      reference(arg1 && arg2, st)

    case (Fun.or, List(arg1: ABool, arg2: ABool)) =>
      reference(arg1 || arg2, st)

    case (Fun.imp, List(arg1: ABool, arg2: ABool)) =>
      reference(!arg1 || arg2, st)

    case (Fun.eq_, List(arg1: ABool, arg2: ABool)) =>
      reference(arg1 eq arg2, st)

    case (Fun.not, List(arg1: ABool, arg2: ABool)) =>
      reference(arg1 noneq arg2, st)

    case (Fun.not, List(arg1: ABool)) =>
      reference(!arg1, st)

    // AInt
    case (Fun.uminus, List(arg: AInt)) =>
      reference(- arg, st)

    case (Fun.plus, List(arg1: AInt, arg2: AInt)) =>
      reference(arg1 + arg2, st)

    case (Fun.minus, List(arg1: AInt, arg2: AInt)) =>
      reference(arg1 - arg2, st)

    case (Fun.times, List(arg1: AInt, arg2: AInt)) =>
      reference(arg1 * arg2, st)

    case (Fun.div, List(arg1: AInt, arg2: AInt)) =>
      reference(arg1 / arg2, st)

    case (Fun.gt, List(arg1: AInt, arg2: AInt)) =>
      reference(arg1 > arg2, st)

    case (Fun.ge, List(arg1: AInt, arg2: AInt)) =>
      reference(arg1 >= arg2, st)

    case (Fun.lt, List(arg1: AInt, arg2: AInt)) =>
      reference(arg1 < arg2, st)

    case (Fun.le, List(arg1: AInt, arg2: AInt)) =>
      reference(arg1 <= arg2, st)

    case(Fun.eq_, List(arg1: AInt, arg2: AInt)) =>
      reference(arg1 == arg2, st)

    case (Fun.not, List(arg1: AInt, arg2: AInt)) =>
      reference(arg1 != arg2, st)

    // AList
    case (Known.nil, Nil) =>
      reference(ANil, st)

    case (Known.cons, List(hd: AVal, tl: AVal)) =>
      reference(ACons(args(0), args(1)), st)

    case (Known.head, List(ACons(x, xs))) =>
      (x, st)

    case (Known.head, List(AMany(e))) => 
      reference(st.refs(e),st)

    case (Known.tail, List(ACons(x, xs))) =>
      (xs, st)

    case (Known.tail, List(AMany(e))) => 
      val ref_elem = reference()
      val st_ = refine(ref_elem, st.refs(e), st)
      reference(AMany(ref_elem), st_)   

    case _ if state.fundefs contains(inst.fun.name, inst.fun.args.length) => 
      val(params, body) = state.fundefs (inst.fun.name, inst.fun.args.length)

      var st_params: AState = AState.empty
      var args_params: List[ARef] = List()

      val combinedParamsArgs = params.zip(args)

      for ((v, ref) <- combinedParamsArgs) {
        st_params = init(v, st.refs(ref), st_params)
        args_params = args_params :+ st_params.vars(v)
      }

      val (ref_, st_) = eval(body, st_params)
      val ref = ARef.fresh()
      (ref, st.copy(refs = st.refs + (ref -> st_.refs(ref_))))
  }

  // Testing
  def and_positive(phis: List[Expr], st: List[AState]): List[AState] = phis match {
    case Nil => st
    case first :: rest => and_positive(rest, positive(first, st))
  }

  def and_negative(phis: List[Expr], st: List[AState]): List[AState] = phis match {
    case Nil => List()
    case first :: rest => negative(first, st) ++ and_negative(rest, positive(first, st))
  }

  def or_positive(phis: List[Expr], st: List[AState]): List[AState] = phis match {
    case Nil => List()
    case first :: rest => positive(first, st) ++ or_positive(rest, negative(first, st))
  }

  def or_negative(phis: List[Expr], st: List[AState]): List[AState] = phis match {
    case Nil => st
    case first :: rest => or_negative(rest, negative(first, st))
  }

  def equals_positive(a: ARef, b: ARef, st: AState): List[AState] = (st.refs(a), st.refs(b)) match {
    // ABool
    case (AFalse, AFalse) =>
      List((st))

    case (AFalse, ATrue) =>
      List()

    case (AFalse, AUnknown) =>
      List(refine(b, AFalse, st))

    case (ATrue, AFalse) =>
      List()

    case (ATrue, ATrue) =>
      List((st))

    case (ATrue, AUnknown) =>
      List(refine(b, ATrue, st))

    case (AUnknown, AFalse) =>
      List(refine(a, AFalse, st))

    case (AUnknown, ATrue) =>
      List(refine(a, ATrue, st))

    case (AUnknown, AUnknown) =>
      List(refine(List((a, AFalse),(b, AFalse)), st), refine(List((a, ATrue),(b, ATrue)), st) )

    //AInt
    case (x: AInt, y: AInt) => 
      val eq1 = le_positive(a,b, st)
      val eq2 = le_positive(b,a, st)
      if (areListsEqual(eq1, eq2)) eq1 else List()

    // AList
    case (ANil, ANil) =>
      List((st))

    case (ANil, ACons(y, ys)) =>
      List()

    case (ANil, AMany(f)) =>
      List(refine(b, ANil, st))

    case (ACons(x, xs), ANil) =>
      List()

    case (ACons(x: ARef, xs: ARef), ACons(y: ARef, ys: ARef)) =>
      for (st_ <- equals_positive(x, y, st); st__ <- equals_positive(xs, ys, st_))
        yield st__

    case (ACons(x: ARef, xs: ARef), AMany(f: ARef)) => 
      val ref_list = reference()
      val ref_elem = reference()
      val st_temp = refine(List((ref_elem, st.refs(f)), (ref_list, AMany(f)), (b, ACons(ref_elem, ref_list))), st)
      for (st_ <- equals_positive(x, f, st_temp); st__ <- equals_positive(xs, ref_list, st_)) yield st__

    case (AMany(e), ANil) =>
      List(refine(a, ANil, st))

    case (AMany(e: ARef), ACons(y: ARef, ys: ARef)) => 
      val ref_list = reference()
      val ref_elem = reference()
      val st_temp = refine(List((ref_elem, st.refs(e)),(ref_list, AMany(e)),(a, ACons(ref_elem, ref_list))), st)
      for (st_ <- equals_positive(e, y, st_temp); st__ <- equals_positive(ref_list, ys, st_))
        yield st__

    case (AMany(e), AMany(f)) =>
      List((st)) // -> we don't know anything
  }

  def equals_negative(a: ARef, b: ARef, st: AState): List[AState] = (st.refs(a), st.refs(b)) match {
    // ABool
    case (AFalse, AFalse) =>
      List()

    case (AFalse, ATrue) =>
      List((st))

    case (AFalse, AUnknown) =>
      List(refine(b, ATrue, st))

    case (ATrue, AFalse) =>
      List((st))

    case (ATrue, ATrue) =>
      List()

    case (ATrue, AUnknown) =>
      List(refine(b, AFalse, st))

    case (AUnknown, AFalse) =>
      List(refine(a, ATrue, st))

    case (AUnknown, ATrue) =>
      List(refine(a, AFalse, st))

    case (AUnknown, AUnknown) =>
      List( (refine(List((a, ATrue),(b, AFalse)), st)), (refine(List((a, AFalse),(b, ATrue)), st)) )

     //AInt
    case (x: AInt, y: AInt) => 
      val eq1 = le_negative(a,b, st)
      val eq2 = le_negative(b,a, st)
      eq1 ++ eq2

    // AList
    case (ANil, ANil) =>
      List()

    case (ANil, ACons(y, ys)) =>
      List((st))

    case (ANil, AMany(f)) => 
      val ref_list = reference()
      val ref_elem = reference()
      List(refine(List((ref_elem, st.refs(f)), (ref_list, AMany(f)), (b, ACons(ref_elem, ref_list))), st))

    case (ACons(x, xs), ANil) =>
      List((st))

    case (ACons(x: ARef, xs: ARef), ACons(y: ARef, ys: ARef)) =>
      val hd = for (st_ <- equals_negative(x, y, st)) yield st_
      val tl = for (st_ <- equals_positive(x, y, st); st__ <- equals_negative(xs, ys, st_)) yield st__
      hd ++ tl

    case (ACons(x: ARef, xs: ARef), AMany(f: ARef)) => 
      val nil = List(refine(b, ANil, st))

      val ref_list = reference()
      val ref_elem = reference()

      val st_ = refine(List((ref_elem, st.refs(f)),(ref_list, AMany(f)), (b, ACons(ref_elem, ref_list))), st)
      val cons = equals_negative(a, b, st_)
      cons ++ nil

    case (AMany(e), ANil) => 
      val ref_list = reference()
      val ref_elem = reference()
    
      List(refine(List((ref_elem, st.refs(e)),(ref_list, AMany(e)),(b, ACons(ref_elem, ref_list))), st))

    case (AMany(e: ARef), ACons(y: ARef, ys: ARef)) => 
      val nil = List(refine(a, ANil, st))

      val ref_list = reference()
      val ref_elem = reference()

      val st_ = refine(List((ref_elem, st.refs(e)),(ref_list, AMany(e)),(a, ACons(ref_elem, ref_list))), st)
      val cons = equals_negative(a, b, st_)
      cons ++ nil

    case (AMany(e), AMany(f)) => List((st)) // we do not know anything
  }

  //[l1,u1] ≤ [l2,u2] = ([l1,u1] meet [NegInf,u2], [l1,PosInf] meet [l2,u2])
  def le_positive(a: ARef, b: ARef, st: AState): List[AState] = (st.refs(a), st.refs(b)) match {
    case (x: AInt, y: AInt) =>  
      for(int1 <- x meet AInt(NegInf, y.ub);
          int2 <- AInt(x.lb, PosInf) meet y)
          yield {
            refine(List((a, int1),(b, int2)), st)
          }
  }

  def le_negative(a: ARef, b: ARef, st: AState): List[AState] = (st.refs(a), st.refs(b)) match {
    case (x: AInt, y: AInt) => lt_positive(b, a, st)
  }

  //[a,b] < J iff [a+1, b+1] ≤ J
  def lt_positive(a: ARef, b: ARef, st: AState): List[AState] = (st.refs(a), st.refs(b)) match {
    case (x: AInt, y: AInt) => 
      val x_ = x + AInt.one

      for(int1 <- x_ meet AInt(NegInf, y.ub);
          int2 <- AInt(x_.lb, PosInf) meet y)
          yield {
            val int1_ = int1 - AInt.one
            refine(List((a, int1_),(b, int2)),st)          
          }
  }

  def lt_negative(a: ARef, b: ARef, st: AState): List[AState] = (st.refs(a), st.refs(b)) match {
    case (x: AInt, y: AInt) => le_positive(b,a,st)
  }

  def positive(phi: Expr, st: List[AState]): List[AState] = phi match {
    case True =>
      st

    case False =>
      List()

    case x: Var =>
      st flatMap { s =>
        s.refs(s.vars(x)) match {
          case ATrue  => List(s)
          case AFalse => List()
          case AUnknown => List(refine(s.vars(x), ATrue, s))
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
      var st_ : List[AState] = List()
      for (s <- st) {
        val (x_, s_) = eval(x, s)
        val (y_, s__) = eval(y, s_)
        val temp_eq = equals_positive(x_, y_, s__)
        st_ = st_ ++ temp_eq        
      }
      st_

    case Le(x: Expr, y: Expr) =>
      var st_ : List[AState] = List()
      for (s <- st) {
        val (x_, s_) = eval(x, s)
        val (y_, s__) = eval(y, s_)
        st_ = st_ ++ le_positive(x_, y_, s__)
      }
      st_

    case Lt(x: Expr, y: Expr) =>
      var st_ : List[AState] = List()
      for (s <- st) {
        val (x_, s_) = eval(x, s)
        val (y_, s__) = eval(y, s_)
        st_ = st_ ++ lt_positive(x_, y_, s__)
      }
      st_

    case Ge(x: Expr, y: Expr) => 
      val phi_le : Expr = Le(y,x) 
      positive(phi_le, st)

    case Gt(x: Expr, y: Expr) => 
      val phi_lt : Expr = Lt(y,x) 
      positive(phi_lt, st)

    case _ => 
      var st_ : List[AState] = List()
      for (s <- st){
        val (e, s_) = eval(phi, s)
        if (s_.refs(e).equals(ATrue)) st_ = st_ :+ s //only ATrue cases -> can't make a statement in case of AUnknown
      }
      st_
  }

  def negative(phi: Expr, st: List[AState]): List[AState] = phi match {
    case True =>
      List()

    case False =>
      st

    case x: Var =>
      st flatMap { s =>
        s.refs(s.vars(x)) match {
          case ATrue  => List()
          case AFalse => List(s)
          case AUnknown => List(refine(s.vars(x), AFalse, s))
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
      var st_ : List[AState] = List()
      for (s <- st) {
        val (x_, s_) = eval(x, s)
        val (y_, s__) = eval(y, s_)
        st_ = st_ ++ equals_negative(x_, y_, s__)
      }
      st_

    case Le(x: Expr, y: Expr) =>
      var st_ : List[AState] = List()
      for (s <- st) {
        val (x_, s_) = eval(x, s)
        val (y_, s__) = eval(y, s_)
        st_ = st_ ++ le_negative(x_, y_, s__)
      }
      st_

    case Lt(x: Expr, y: Expr) =>
      var st_ : List[AState] = List()
      for (s <- st) {
        val (x_, s_) = eval(x, s)
        val (y_, s__) = eval(y, s_)
        st_ = st_ ++ lt_negative(x_, y_, s__)
      }
      st_

    case Ge(x: Expr, y: Expr) => 
      val phi_le : Expr = Le(y,x) 
      negative(phi_le, st)

    case Gt(x: Expr, y: Expr) => 
      val phi_lt : Expr = Lt(y,x) 
      negative(phi_lt, st)
    
    case _ => 
      var st_ : List[AState] = List()
      for (s <- st){
        val (e, s_) = eval(phi, s)
        if (s_.refs(e).equals(AFalse)) st_ = st_ :+ s //only AFalse cases -> can't make a statement in case of AUnknown
      }
      st_
  }

  def widen(init: List[AState], states: List[AState]) : List[AState] = {
    if(states.isEmpty) return init
    else{
      for(st <- init) yield widen (st, union(states))
    }
  }

  def widen(st1: AState, st2: AState): AState = {
    val merger = new Merge(st1, st2)
    var resultState = AState(Map(), Map())

    st1.vars.keys.foreach { varName =>
      val ref1 = st1.vars(varName)
      val ref2 = st2.vars(varName)

      val widenedRef = merger.widen(ref1, ref2)
      
      resultState = resultState.copy(vars = resultState.vars + (varName -> widenedRef))
      resultState = resultState.copy(refs = resultState.refs ++ merger.result)
    }
    resultState
  }


  def union(states: List[AState]): AState = states match {
    case Nil => ??? //should not occure

    case singleState :: Nil =>
      singleState

    case _ => 
      var resultState = states.head
      
      for (currentState <- states.tail) {
        // initialize the merger with the current result state and the current state
        val merger = new Merge(resultState, currentState)
        
        val allVars = (resultState.vars.keys ++ currentState.vars.keys).toSet

        //use a temporary state to store the result of the union
        var tempState = AState.empty

        for (variable <- allVars) {
          // get the references for the variable in both states
          val refInResult = resultState.vars(variable)
          val refInCurrent = currentState.vars(variable)

          //use the merger to join the references and get the joined reference
          val newRef = merger.join(refInResult, refInCurrent)
          val ref = reference() 

          //tempState = tempState.copy(vars = tempState.vars + (variable -> ref), refs = tempState.refs + (ref -> newVal))
          tempState = tempState.copy(vars = tempState.vars + (variable -> ref), refs = tempState.refs + (ref -> merger.result(newRef)))
          tempState = tempState.copy(refs = tempState.refs ++ merger.result)       
        }
        resultState = tempState
      }
    resultState
  }

  //narrowing
  def narrow(init: List[AState], states: List[AState]) : List[AState] = {
    if(states.isEmpty) states 
    else{
      for(st <- init) yield narrow (st, union(states))
    }
  }

  def narrow(st1: AState, st2: AState): AState = {
    val merger = new Merge(st1, st2)
    var resultState = AState(Map(), Map())

    st1.vars.keys.foreach { varName =>
      val ref1 = st1.vars(varName)
      val ref2 = st2.vars(varName)
      
      val widenedRef = merger.narrow(ref1, ref2)
      
      resultState = resultState.copy(vars = resultState.vars + (varName -> widenedRef))
      resultState = resultState.copy(refs = resultState.refs ++ merger.result)
    }
    resultState
  }

  def createInv(name: Var, value: AVal, s: AState) : Expr = value match {
    //ABool
    case ATrue => name
    case AFalse => !name
    case AUnknown => True
    
    //case AInt
    case AInt(Fin(lb), PosInf) => Le(Lit(lb, Sort.int), name)
    case AInt(NegInf, Fin(ub)) =>  Le(name, Lit(ub, Sort.int))
    case AInt(Fin(lb), Fin(ub)) => And(List(Le(Lit(lb, Sort.int), name), Le(name, Lit(ub, Sort.int))))
    case AInt(NegInf, PosInf) => True

    //AList
    case ANil => Eq(name, Known.nil()) 

    case ACons(hd, tl) => 
      val list_typ = name.typ
      val Sort(_, List(typ)) = list_typ

      val hd_elem : Var = Expr.fresh("hd", typ) //head element
      val tl_elem : Var = Expr.fresh("tl", list_typ) //tail element

      //invariant head elements
      val inv_head : Expr = createInv(hd_elem, s.refs(hd), s)
      val inv_tail : Expr = createInv(tl_elem, s.refs(tl), s)

      //Invariant shape/constructor
      val inv_shape : Expr = Eq(name,Known.cons(hd_elem, tl_elem))
      Exists(List(hd_elem, tl_elem), And(List(inv_shape, inv_head, inv_tail))) 

    case AMany(elems) => 
      val list_typ = name.typ
      val Sort(_, List(typ)) = list_typ

      val e : Var = Expr.fresh("elem", typ)
      val inv_elem : Expr = createInv(e, s.refs(elems), s)

      Forall(List(e), Imp(Known.contains(e, name), inv_elem))
  }

  def invariants(st: List[AState]): Expr = {
    val invariants = for (s <- st) yield {
      val formulas = for ((name, ref) <- s.vars) yield {
        createInv(name, s.refs(ref), s)  
      }
      And(formulas.toList)
    }
    Or(invariants.toList) // return list of invariants
  }

  def eval(expr: Expr, st: AState): (ARef, AState) = expr match {
    case Lit(any, typ) => //only for int
      val aint = lit(any)
      reference(aint, st)

    case x: Var =>
      (lookup(x, st), st)

    case App(inst, args) =>
      val (args_, st_) = args.foldRight((Nil: List[ARef], st)) {
        case (expr, (args_, st_)) =>
          val (arg, st__) = eval(expr, st_)
          (arg :: args_, st__)
      }
      apply(inst, args_, st_)
  }

  def areRefsEqual(ref1: ARef,ref2: ARef,st1: AState,st2: AState): Boolean = (st1.refs(ref1), st2.refs(ref2)) match {
    //ABool
    case (ATrue, ATrue) => true
    case (AFalse, AFalse) => true
    case (AUnknown, AUnknown) => true 
    case (_: ABool, _: ABool) => false 

    //AList
    case (ANil, ANil) => true
    case (AMany(e), AMany(f)) => areRefsEqual(e, f, st1, st2)
    case (ACons(x,xs), ACons(y, ys)) => areRefsEqual(x, y, st1, st2) && areRefsEqual(xs, ys, st1, st2)
    case (_: AList, _: AList) => false

    //AInt
    case (i: AInt, j: AInt) => i == j
  }

  def areRefsSubsetOrEqual(ref1: ARef,ref2: ARef,st1: AState,st2: AState): Boolean = (st1.refs(ref1), st2.refs(ref2)) match {
    //ABool
    case (ATrue, ATrue) => true
    case (AFalse, AFalse) => true
    case (_: ABool, AUnknown) => true 
    case (AUnknown, _: ABool) => false

    //AList
    case (ANil, ANil) => true
    case (ACons(x,xs), ACons(y, ys)) => areRefsSubsetOrEqual(x, y, st1, st2) && areRefsSubsetOrEqual(xs, ys, st1, st2)
    case (ANil, AMany(f)) => true
    case (ACons(x,xs), AMany(f)) => areRefsSubsetOrEqual(x, f, st1, st2) && areRefsSubsetOrEqual(xs, ref2, st1, st2)
    case (AMany(e), AMany(f)) => areRefsSubsetOrEqual(e, f, st1, st2)
    case (AMany(e), ACons(y, ys)) => false

    //AInt
    case (i: AInt, j: AInt) => 
      j.lb <= i.lb && i.ub <= j.ub
  }

  def areStatesEqual(st1: AState, st2: AState): Boolean = {
    require(st1.vars.keySet == st2.vars.keySet)
    val keys = st1.vars.keySet

    keys forall { name =>
      areRefsEqual(st1.vars(name), st2.vars(name), st1, st2)
    }
  }

  def areStatesSubsetOrEqual(st1: AState, st2: AState): Boolean = {
    require(st1.vars.keySet == st2.vars.keySet)
    val keys = st1.vars.keySet

    keys forall { name =>
      areRefsSubsetOrEqual(st1.vars(name), st2.vars(name), st1, st2)
    }
  }

  def areListsEqual(set1: List[AState], set2: List[AState]): Boolean = {
    val result = set1.forall { st1 => set2.exists(st2 => areStatesEqual(st1, st2))}
    result && set2.forall { st2 => set1.exists(st1 => areStatesEqual(st1, st2))}
  }

  //Are sets subsets or equal
  def areListsSubsetOrEqual(set1: List[AState], set2: List[AState]): Boolean = {
    set1.forall { st1 => set2.exists(st2 => areStatesSubsetOrEqual(st1, st2))}
  }

  def isSubsetOf(states1: List[AState], states2: List[AState]): Boolean = {
    areListsSubsetOrEqual(states1.toList, states2.toList)
  } 

  def collectReferences(refs: List[ARef], st: AState): List[ARef] = {
    refs ++ (refs flatMap { r => collectReferences(st.refs(r).refs, st) })
  }

  // clean states of unused references
  def garbageCollector(st: AState): AState = {
    val roots = st.vars.values.toList
    val keep = collectReferences(roots, st)
    val drop = st.refs.keySet -- keep
    st copy (refs = st.refs -- drop) 
  }

  def garbageCollector(states: List[AState]): List[AState] = {
    states map garbageCollector
  }
}

object Abstract extends Stage {
  def exec(prefix: List[Cmd], cmds: List[Cmd], last: Cmd, state: cuvee.State) = {
    cmds.flatMap {
      case DefineProc(name, params, in, out, spec, body) =>
        val proc = Proc(name, params, in, out, spec)
        val a = new Abstract(state)
        var st_a: AState = AState.empty
        for (x <- in ++ out) { st_a = a.init(x, x.typ, st_a) }

        var s_a: List[AState] = List(st_a)
        val res_a = a.garbageCollector(a.exec(body, s_a))
        
        val annotator = new Annotator(a)
        val (annotatedBody, annotatedStates) = annotator.annotate(body, s_a)

        List(DefineProc(name, params, in, out, spec, annotatedBody))

      case cmd =>
        List(cmd)
    }
  }
}