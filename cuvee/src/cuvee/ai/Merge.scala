package cuvee.ai

object Merge{
  // Gets all the references (elements) in a list
  def flatten(xs: ARef, st: AState): List[ARef] = st.refs(xs) match {
    case ANil => Nil
    case ACons(hd, tl) => hd :: flatten(tl, st)
    case AMany(elems) => List(elems)
  }

  def flatten(hd: ARef, tl: ARef, st: AState): List[ARef] = {
    hd :: flatten(tl, st)    
  }
}

class Merge(sta: AState, stb: AState) {
  import Merge._
  var map: Map[(ARef, ARef), ARef] = Map()
  var result: Map[ARef, AVal] = Map()

  //widen
  def widen(a: ARef, b: ARef): ARef = {
    if (map contains (a, b)) {
      val c = map((a, b))
      c
    } else {
      val v = widen(sta refs a, stb refs b) 
      val c = ARef.fresh()
      map = map + ((a, b) -> c)
      result = result + (c -> v)
      c
    }
  }

  def widen(a: AVal, b: AVal): AVal = (a, b) match {
    //ABool
    case (a: ABool, b: ABool) => a widen b

    //AInt
    case (a: AInt, b: AInt) => a widen b

    //AList
    case (ANil, ANil) => ANil
    case (ANil, ACons(y, ys)) => AMany(join(flatten(y, ys, stb), stb)) 
    case (ANil, AMany(f)) => AMany(join(List(f), stb)) 
    case (ACons(x, xs), ANil) => AMany(join(flatten(x, xs, sta), sta)) 
    case (ACons(x, xs), ACons(y, ys)) => ACons(widen(x, y), widen(xs, ys))
    case (ACons(x, xs), AMany(f)) => AMany(widen(join(flatten(x, xs, sta), sta), f))
    case (AMany(e), ANil) => AMany(join(List(e), sta)) 
    case (AMany(e), ACons(y, ys)) => AMany(widen(e, join(flatten(y, ys, stb), stb))) 
    case (AMany(e), AMany(f)) => AMany(widen(e, f))
  }

  //join
  def join(refs: List[ARef]): ARef = {
    refs.reduceLeft(join)  
  }

  def join(a: ARef, b: ARef): ARef = {
    if (map contains (a, b)) {
      val c = map((a, b))
      c
    }else {
      if(sta.refs contains a){
        if(stb.refs contains b){
          val v = join(sta refs a, stb refs b) 
          val c = ARef.fresh()
          map = map + ((a, b) -> c) 
          result = result + (c -> v)
          c
      }else{
        val v = join(sta refs a, result(b)) 
        val c = ARef.fresh()
        map = map + ((a, b) -> c)
        result = result + (c -> v)
        c
        }
    }else{
      if(stb.refs contains b){
        val v = join(result(a), stb refs b) 
        val c = ARef.fresh()
        map = map + ((a, b) -> c) 
        result = result + (c -> v)
        c
      }else{
        val v = join(result(a), result(b)) 
        val c = ARef.fresh()
        map = map + ((a, b) -> c) 
        result = result + (c -> v)
        c
        }
      }
    }
  }

  //used for references of flattened lists -> need same state
  def join(refs: List[ARef], state: AState): ARef = {
    if (refs.length == 1) {
      val c = ARef.fresh()
      map = map + ((refs.head, refs.head) -> c)
      result = result + (c -> state.refs(refs.head))
      c
    } else {
      var acc = ARef.fresh()
      map = map + ((refs.head, refs.head) -> acc)
      result = result + (acc -> state.refs(refs.head))

      for (ref <- refs.tail) {
        
        val newAcc = join(acc, ref, state) 
        map = map + ((acc, ref) -> newAcc)
        result = result + (newAcc -> result(newAcc))
        acc = newAcc
      }
      acc
    }
  }

  def join(a: ARef, b: ARef, state: AState): ARef = {
    if(state.refs contains(a)){
      val v = join(state refs a, state refs b)
      val c = ARef.fresh()
      map = map + ((a, b) -> c) 
      result = result + (c -> v)
      c
    }else{
      val v = join(result(a), stb refs b) 
      val c = ARef.fresh()
      map = map + ((a, b) -> c) 
      result = result + (c -> v)
      c
    }
  }

  def join(a: AVal, b: AVal): AVal = (a, b) match {
    //ABool
    case (a: ABool, b: ABool) => a join b
    
    //AInt
    case (a: AInt, b: AInt) => a join b
   
    //AList
    case (ANil, ANil) => ANil
    case (ANil, ACons(y, ys)) => AMany(join(flatten(y, ys, stb), stb)) 
    case (ANil, AMany(f)) => AMany(join(List(f), stb))
    case (ACons(x, xs), ANil) => AMany(join(flatten(x, xs, sta), sta)) 
    case (ACons(x, xs), ACons(y, ys)) => ACons(join(x, y), join(xs, ys))
    case (ACons(x, xs), AMany(f)) => AMany(join(join(flatten(x, xs, sta), sta), f)) 
    case (AMany(e), ANil) => AMany(join(List(e), sta))
    case (AMany(e), ACons(y, ys)) => AMany(join(e, join(flatten(y, ys, stb), stb)))
    case (AMany(e), AMany(f)) => AMany(join(e, f))
  }

  //narrow
  def narrow(a: ARef, b: ARef): ARef = {
    if (map contains (a, b)) {
      val c = map((a, b))
      c
    } else {
      val v = narrow(sta refs a, a, stb refs b) 
      val c = ARef.fresh()
      map = map + ((a, b) -> c)
      result = result + (c -> v)
      c
    }
  }

  def narrow(a: AVal, a_ref: ARef, b: AVal): AVal = (a, b) match {
    //ABool
    case (AFalse, AFalse) | (ATrue, ATrue)  => b
    case (AUnknown, _) => b
    case (b1: ABool, b2: ABool) => ??? //case should not occure -e.g. (AFalse, ATrue) | (ATrue, AFalse) | (_, AUnknown)

    //AInt
    case (a: AInt, b: AInt) => a narrow b

    //AList
    case (ANil, ANil) => b
    case (ANil, ACons(y, ys)) => ??? //case should not occure
    case (ANil, AMany(f)) => ??? //case should not occure (right value is more precise than left value)
    case (ACons(x, xs), ANil) => ??? //case should not occure
    case (ACons(x, xs), ACons(y, ys)) => ACons(narrow(x, y), narrow(xs, ys))
    case (ACons(x, xs), AMany(f)) => ??? //case should not occure (right value is more precise than left value)
    case (AMany(e), ANil) => b
    case (AMany(e), ACons(y, ys)) => ACons(narrow(e,y), narrow(a_ref, ys)) 
    case (AMany(e), AMany(f)) => AMany(narrow(e, f))
  }
}