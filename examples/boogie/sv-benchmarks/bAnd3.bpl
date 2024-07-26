data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure __VERIFIER_nondet_int() returns (c#result: int);
  modifies c#heap;

procedure bAnd(x: [int]int)
  returns (c#result: int)
  modifies c#heap;
{
  var i: int;
  var res: int;
  res := x[0];
  i := 1;
  while(i < 10000) {
    res := c#bitand(res, x[i]);
    var x₉₄₃: int := i;
    i := i + 1;
  }
  c#result := res;
  return;
}

procedure main()
  returns (c#result: int)
  modifies c#heap;
{
  var x: [int]int;
  var temp: int;
  var ret: int;
  var ret2: int;
  var ret5: int;
  var i: int;
  i := 0;
  while(i < 10000) {
    var __VERIFIER_nondet_int₉₄₄: int;
    __VERIFIER_nondet_int₉₄₄ := call __VERIFIER_nondet_int();
    x := x[i := __VERIFIER_nondet_int₉₄₄];
    var x₉₄₅: int := i;
    i := i + 1;
  }
  var bAnd₉₄₆: int;
  bAnd₉₄₆ := call bAnd(x);
  ret := bAnd₉₄₆;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var bAnd₉₄₇: int;
  bAnd₉₄₇ := call bAnd(x);
  ret2 := bAnd₉₄₇;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 10000 - 1) {
    x := x[i := x[i + 1]];
    var x₉₄₈: int := i;
    i := i + 1;
  }
  x := x[10000 - 1 := temp];
  var bAnd₉₄₉: int;
  bAnd₉₄₉ := call bAnd(x);
  ret5 := bAnd₉₄₉;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

