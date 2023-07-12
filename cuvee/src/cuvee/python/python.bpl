data pyValue
  = pyNone
  | pyInt(pyGetInt: int)
  | pyBool(pyGetBool: bool)
  | pyArray(pyGetValues: [int]pyValue, pyGetLength: int)
  ;

const pyTrue:  pyValue { pyBool(true) }
const pyFalse: pyValue { pyBool(false) }
const pyDefaultArray: [int]pyValue;

function pyIsTrue(x: pyValue): bool;
axiom
    pyIsTrue(pyNone) 
      == false;
axiom forall b: bool ::
    pyIsTrue(pyBool(b)) 
      == b;
axiom forall i: int ::
    pyIsTrue(pyInt(i)) 
      == (i != 0);
axiom forall a: [int]pyValue, n: int ::
    pyIsTrue(pyArray(a, n)) 
      == (n != 0);

function toInt(b: bool): int {
  if b
  then 1
  else 0
}

function pyIte(x: pyValue, y: pyValue, z: pyValue): pyValue;
axiom forall x: pyValue, y: pyValue, z: pyValue ::
  pyIte(x, y, z) 
    == if   pyIsTrue(x)
       then y
       else z;


function pyAnd(x: pyValue, y: pyValue): pyValue {
    pyIte(x, y, x)
}

function pyOr(x: pyValue, y: pyValue): pyValue {
    pyIte(x, x, y)
}

function pyNot(x: pyValue): pyValue {
    pyIte(x, pyFalse, pyTrue)
}

function pyImplies(x: pyValue, y: pyValue): pyValue {
    pyIte(x, y, pyTrue)
}


function pyEquals(x: pyValue, y: pyValue): pyValue;
axiom
  pyEquals(pyNone, pyNone) 
    == pyTrue;
axiom forall i: int, j: int ::
  pyEquals(pyInt(i), pyInt(j)) 
    == pyBool(i == j);
axiom forall a: bool, b: bool ::
  pyEquals(pyBool(a), pyBool(b)) 
    == pyBool(a == b);
axiom forall a1: [int]pyValue, n1: int,
             a2: [int]pyValue, n2: int ::
  pyEquals(pyArray(a1, n1), pyArray(a2, n2))
    ==  pyBool(n1 == n2 && 
        forall k: int ::
          0 <= k && k < n1 ==> a1[k] == a2[k]);
axiom forall i: int ::
  pyEquals(pyNone, pyInt(i)) 
    == pyFalse;
axiom forall b: bool ::
  pyEquals(pyNone, pyBool(b)) 
    == pyFalse;
axiom forall a: [int]pyValue, n: int ::
  pyEquals(pyNone, pyArray(a, n))
    == pyFalse;
axiom forall i: int ::
  pyEquals(pyInt(i), pyNone) 
    == pyFalse;
axiom forall b: bool ::
  pyEquals(pyBool(b), pyNone) 
    == pyFalse;
axiom forall a: [int]pyValue, n: int ::
  pyEquals(pyArray(a, n), pyNone)
    == pyFalse;
axiom forall i: int, b: bool ::
  pyEquals(pyInt(i), pyBool(b)) 
    == pyBool(i == toInt(b));
axiom forall i: int, a: [int]pyValue, n: int ::
  pyEquals(pyInt(i), pyArray(a, n)) 
    == pyFalse;
axiom forall b: bool, a: [int]pyValue, n: int ::
  pyEquals(pyBool(b), pyArray(a, n)) 
    == pyFalse;
axiom forall b: bool, i: int ::
  pyEquals(pyBool(b), pyInt(i)) 
    == pyBool(i == toInt(b));
axiom forall a: [int]pyValue, n: int, i: int ::
  pyEquals(pyArray(a, n), pyInt(i)) 
    == pyFalse;
axiom forall a: [int]pyValue, n: int, b: bool ::
  pyEquals(pyArray(a, n), pyBool(b)) 
    == pyFalse;


function pyLessThan(x: pyValue, y: pyValue): pyValue;
function pyLessEquals(x: pyValue, y: pyValue): pyValue;

function pyGreaterThan(x: pyValue, y: pyValue): pyValue {
  pyLessThan(y, x)
}

function pyGreaterEquals(x: pyValue, y: pyValue): pyValue {
  pyLessEquals(y, x)
}

axiom forall i: int, j: int ::
  pyLessThan(pyInt(i), pyInt(j)) 
    == pyBool(i < j);
axiom forall a: bool, b: bool ::
  pyLessThan(pyBool(a), pyBool(b)) 
    == pyBool(toInt(a) < toInt(b));
axiom forall a1: [int]pyValue, n1: int,
             a2: [int]pyValue, n2: int ::
  pyLessThan(pyArray(a1, n1), pyArray(a2, n2))
    == pyBool(if n1 < n2
              then forall k: int ::
                0 <= k && k < n1 ==> pyGetBool(pyLessEquals(a1[k], a2[k]))
              else exists k: int ::
                0 <= k && k < n2 && pyGetBool(pyLessThan(a1[k], a2[k])) &&
                    forall j: int :: 0 <= j && j < k ==> pyGetBool(pyEquals(a1[k], a2[k]))
              );
axiom forall b: bool, i: int ::
  pyLessThan(pyBool(b), pyInt(i)) 
    == pyBool(toInt(b) < i);
axiom forall i: int, b: bool ::
  pyLessThan(pyInt(i), pyBool(b)) 
    == pyBool(i < toInt(b));

axiom forall i: int, j: int ::
  pyLessEquals(pyInt(i), pyInt(j)) 
    == pyBool(i <= j);
axiom forall a: bool, b: bool ::
  pyLessEquals(pyBool(a), pyBool(b)) 
    == pyBool(toInt(a) <= toInt(b));
axiom forall a1: [int]pyValue, n1: int,
             a2: [int]pyValue, n2: int ::
  pyLessEquals(pyArray(a1, n1), pyArray(a2, n2))
    == pyBool(if n1 <= n2
              then forall k: int ::
                0 <= k && k < n1 ==> pyGetBool(pyLessEquals(a1[k], a2[k]))
              else exists k: int ::
                0 <= k && k < n2 && pyGetBool(pyLessThan(a1[k], a2[k])) &&
                    forall j: int :: 0 <= j && j < k ==> pyGetBool(pyEquals(a1[k], a2[k]))
              );
axiom forall b: bool, i: int ::
  pyLessEquals(pyBool(b), pyInt(i)) 
    == pyBool(toInt(b) <= i);
axiom forall i: int, b: bool ::
  pyLessEquals(pyInt(i), pyBool(b)) 
    == pyBool(i <= toInt(b));


function pyIn(a: pyValue, e: pyValue): pyValue;
axiom forall a: [int]pyValue, n: int, e: pyValue ::
  pyIn(pyArray(a, n), e)
    == pyBool(exists k: int :: 0 <= k && k < n
                        && pyGetBool(pyEquals(a[k], e)));


function pySelect(x: pyValue, y: pyValue): pyValue;
axiom forall a: [int]pyValue, n: int, i: int ::
  0 <= i && i < n ==> 
    pySelect(pyArray(a, n), pyInt(i)) 
      == a[i];


function pyStore(x: pyValue, y: pyValue, z: pyValue): pyValue;
axiom forall a: [int]pyValue, n: int, i: int, z: pyValue ::
  0 <= i && i < n ==> 
    pyStore(pyArray(a, n), pyInt(i), z) 
      == pyArray(a[i := z], n);


function pyShift(a: [int]pyValue, o: int): [int]pyValue;
axiom forall a: [int]pyValue, 
             o: int, k: int ::
  pyShift(a, o)[k]
    == a[k + o];


function pyConcat(a1: [int]pyValue, n1: int,
                  a2: [int]pyValue): [int]pyValue;
axiom forall a1: [int]pyValue, n1: int,
             a2: [int]pyValue,
             k: int ::
  pyConcat(a1, n1, a2)[k]
    ==  if    k < n1
        then  a1[k]
        else  a2[k - n1];


function pyReplicate(a: [int]pyValue, n: int, k: int): [int]pyValue;
axiom forall a: [int]pyValue, n: int ::
  pyReplicate(a, n, 0)
    == a;
axiom forall a: [int]pyValue, n: int, k: int ::
  k > 0 ==> 
    pyReplicate(a, n, k) 
      == pyConcat(a, n, pyReplicate(a, n, k - 1));


function pySlice(a: pyValue, l: pyValue, m: pyValue): pyValue;
axiom forall a: [int]pyValue, n: int, l: int, m: int ::
  0 <= l && l <= m && m <= n ==> 
    pySlice(pyArray(a, n), pyInt(l), pyInt(m))
      == pyArray(pyShift(a, l), m - l);
axiom forall a: [int]pyValue, n: int, l: int ::
  0 <= l && l <= n ==> 
    pySlice(pyArray(a, n), pyInt(l), pyNone)
      == pyArray(pyShift(a, l), n - l);
axiom forall a: [int]pyValue, n: int, m: int ::
  0 <= m && m <= n ==> 
    pySlice(pyArray(a, n), pyNone, pyInt(m))
      == pyArray(a, n - m);
axiom forall a: [int]pyValue, n: int ::
  pySlice(pyArray(a, n), pyNone, pyNone)
    == pyArray(a, n);


function pyAdd(x: pyValue, y:pyValue): pyValue;
axiom forall i: int, j: int ::
  pyAdd(pyInt(i), pyInt(j))
    == pyInt(i + j);
axiom 
  pyAdd(pyBool(false), pyBool(false)) 
    == pyInt(0);
axiom 
  pyAdd(pyBool(true), pyBool(false)) 
    == pyInt(1);
axiom 
  pyAdd(pyBool(false), pyBool(true)) 
    == pyInt(1);
axiom 
  pyAdd(pyBool(true), pyBool(true)) 
    == pyInt(2);
axiom forall a1: [int]pyValue, n1: int,
             a2: [int]pyValue, n2: int ::
  pyAdd(pyArray(a1, n1), pyArray(a2, n2))
    == pyArray(pyConcat(a1, n1, a2), n1 + n2);
axiom forall i: int ::
  pyAdd(pyBool(false), pyInt(i)) 
    == pyInt(i);
axiom forall i: int ::
  pyAdd(pyBool(true), pyInt(i)) 
    == pyInt(i + 1);
axiom forall i: int ::
  pyAdd(pyInt(i), pyBool(false)) 
    == pyInt(i);
axiom forall i: int ::
  pyAdd(pyInt(i), pyBool(true)) 
    == pyInt(i + 1);

function pyNegate(x: pyValue): pyValue;
axiom forall i: int::
  pyNegate(pyInt(i)) 
    == pyInt(-i);
axiom
  pyNegate(pyBool(true)) 
    == pyInt(-1);
axiom
  pyNegate(pyBool(false)) 
    == pyInt(0);

function pySub(x: pyValue, y:pyValue): pyValue;
axiom forall i: int, j: int ::
  pySub(pyInt(i), pyInt(j))
    == pyInt(i - j);
axiom forall a: bool, b: bool ::
  pySub(pyBool(a), pyBool(b))
    == pyInt(toInt(a) - toInt(b));
axiom forall b: bool, i: int ::
  pySub(pyBool(b), pyInt(i))
    == pyInt(toInt(b) - i);
axiom forall i: int, b: bool ::
  pySub(pyInt(i), pyBool(b))
    == pyInt(i - toInt(b));

function pyTimes(x: pyValue, y:pyValue): pyValue;
axiom forall i: int, j: int ::
  pyTimes(pyInt(i), pyInt(j))
    == pyInt(i * j);
axiom forall a: bool, b: bool ::
  pyTimes(pyBool(a), pyBool(b))
    == pyInt(toInt(a) * toInt(b));
axiom forall b: bool, i: int ::
  pyTimes(pyBool(b), pyInt(i))
    == pyInt(toInt(b) * i);
axiom forall i: int, b: bool ::
  pyTimes(pyInt(i), pyBool(b))
    == pyInt(i * toInt(b));
axiom forall a: [int]pyValue, n: int ::
  pyTimes(pyArray(a, n), pyBool(false))
    == pyArray(a, 0);
axiom forall a: [int]pyValue, n: int ::
  pyTimes(pyArray(a, n), pyBool(true))
    == pyArray(a, n);
axiom forall a: [int]pyValue, n: int ::
  pyTimes(pyBool(false), pyArray(a, n))
    == pyArray(a, 0);
axiom forall a: [int]pyValue, n: int ::
  pyTimes(pyBool(true), pyArray(a, n))
    == pyArray(a, 0);
axiom forall a: [int]pyValue, n: int, i: int ::
  i >= 0 ==>
    pyTimes(pyArray(a, n), pyInt(i))
      == pyArray(pyReplicate(a, n, i), n * i);
axiom forall a: [int]pyValue, n: int, i: int ::
  i >= 0 ==>
    pyTimes(pyInt(i), pyArray(a, n))
      == pyArray(pyReplicate(a, n, i), n * i);

function pyFloorDiv(x: pyValue, y:pyValue): pyValue;
axiom forall i: int, j: int ::
  pyFloorDiv(pyInt(i), pyInt(j))
    == pyInt(i / j);
axiom forall a: bool, b: bool ::
  pyFloorDiv(pyBool(a), pyBool(b))
    == pyInt(toInt(a) / toInt(b));
axiom forall i: int, b: bool ::
  pyFloorDiv(pyInt(i), pyBool(b))
    == pyInt(i / toInt(b));
axiom forall b: bool, i: int ::
  pyFloorDiv(pyBool(b), pyInt(i))
    == pyInt(toInt(b) / i);

// TODO: only support if SMT-LIB has a pow operator (perhaps "exp"), and if so, check Fun.exp, Exp in Expr.scala
//function pyPow(x: pyValue, y:pyValue): pyValue;
//axiom forall i: int, j: int ::
//  pyPow(pyInt(i), pyInt(j))
//    == pyInt( ??? );
//axiom forall a: bool, b: bool ::
//  pyPow(pyBool(a), pyBool(b))
//    == pyInt(toInt(a) ??? toInt(b));
//axiom forall b: bool, i: int ::
//  pyPow(pyBool(b), pyInt(i))
//    == pyInt(toInt(b) ??? i);
//axiom forall i: int, b: bool ::
//  pyPow(pyInt(i), pyBool(b))
//    == pyInt(i ??? toInt(b));

function pyMod(x: pyValue, y:pyValue): pyValue;
axiom forall i: int, j: int ::
  pyMod(pyInt(i), pyInt(j))
    == pyInt(i % j);
axiom forall a: bool, b: bool ::
  pyMod(pyBool(a), pyBool(b))
    == pyInt(toInt(a) % toInt(b));
axiom forall b: bool, i: int ::
  pyMod(pyBool(b), pyInt(i))
    == pyInt(toInt(b) % i);
axiom forall i: int, b: bool ::
  pyMod(pyInt(i), pyBool(b))
    == pyInt(i % toInt(b));
