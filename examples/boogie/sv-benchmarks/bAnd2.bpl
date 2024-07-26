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
  while(i < 1000) {
    res := c#bitand(res, x[i]);
    var x₈₆₉: int := i;
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
  while(i < 1000) {
    var __VERIFIER_nondet_int₈₇₀: int;
    __VERIFIER_nondet_int₈₇₀ := call __VERIFIER_nondet_int();
    x := x[i := __VERIFIER_nondet_int₈₇₀];
    var x₈₇₁: int := i;
    i := i + 1;
  }
  var bAnd₈₇₂: int;
  bAnd₈₇₂ := call bAnd(x);
  ret := bAnd₈₇₂;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var bAnd₈₇₃: int;
  bAnd₈₇₃ := call bAnd(x);
  ret2 := bAnd₈₇₃;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 1000 - 1) {
    x := x[i := x[i + 1]];
    var x₈₇₄: int := i;
    i := i + 1;
  }
  x := x[1000 - 1 := temp];
  var bAnd₈₇₅: int;
  bAnd₈₇₅ := call bAnd(x);
  ret5 := bAnd₈₇₅;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

