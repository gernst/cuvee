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
  while(i < 100) {
    res := c#bitand(res, x[i]);
    var x₈₁₇: int := i;
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
  while(i < 100) {
    var __VERIFIER_nondet_int₈₁₈: int;
    __VERIFIER_nondet_int₈₁₈ := call __VERIFIER_nondet_int();
    x := x[i := __VERIFIER_nondet_int₈₁₈];
    var x₈₁₉: int := i;
    i := i + 1;
  }
  var bAnd₈₂₀: int;
  bAnd₈₂₀ := call bAnd(x);
  ret := bAnd₈₂₀;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var bAnd₈₂₁: int;
  bAnd₈₂₁ := call bAnd(x);
  ret2 := bAnd₈₂₁;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 100 - 1) {
    x := x[i := x[i + 1]];
    var x₈₂₂: int := i;
    i := i + 1;
  }
  x := x[100 - 1 := temp];
  var bAnd₈₂₃: int;
  bAnd₈₂₃ := call bAnd(x);
  ret5 := bAnd₈₂₃;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

