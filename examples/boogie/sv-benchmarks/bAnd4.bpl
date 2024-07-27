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
  while(i < 100000) {
    res := c#bitand(res, x[i]);
    var x₈₃₁: int := i;
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
  while(i < 100000) {
    var __VERIFIER_nondet_int₈₃₂: int;
    __VERIFIER_nondet_int₈₃₂ := call __VERIFIER_nondet_int();
    x := x[i := __VERIFIER_nondet_int₈₃₂];
    var x₈₃₃: int := i;
    i := i + 1;
  }
  var bAnd₈₃₄: int;
  bAnd₈₃₄ := call bAnd(x);
  ret := bAnd₈₃₄;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var bAnd₈₃₅: int;
  bAnd₈₃₅ := call bAnd(x);
  ret2 := bAnd₈₃₅;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 100000 - 1) {
    x := x[i := x[i + 1]];
    var x₈₃₆: int := i;
    i := i + 1;
  }
  x := x[100000 - 1 := temp];
  var bAnd₈₃₇: int;
  bAnd₈₃₇ := call bAnd(x);
  ret5 := bAnd₈₃₇;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

