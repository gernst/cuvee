data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure __VERIFIER_nondet_int() returns (c#result: int);
  modifies c#heap;

procedure sum(x: [int]int)
  returns (c#result: int)
  modifies c#heap;
{
  var i: int;
  var ret: int;
  ret := 0;
  i := 0;
  while(i < 20) {
    ret := ret + x[i];
    var x₅₂₀: int := i;
    i := i + 1;
  }
  c#result := ret;
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
  while(i < 20) {
    var __VERIFIER_nondet_int₅₂₁: int;
    __VERIFIER_nondet_int₅₂₁ := call __VERIFIER_nondet_int();
    x := x[i := __VERIFIER_nondet_int₅₂₁];
    var x₅₂₂: int := i;
    i := i + 1;
  }
  var sum₅₂₃: int;
  sum₅₂₃ := call sum(x);
  ret := sum₅₂₃;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var sum₅₂₄: int;
  sum₅₂₄ := call sum(x);
  ret2 := sum₅₂₄;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 20 - 1) {
    x := x[i := x[i + 1]];
    var x₅₂₅: int := i;
    i := i + 1;
  }
  x := x[20 - 1 := temp];
  var sum₅₂₆: int;
  sum₅₂₆ := call sum(x);
  ret5 := sum₅₂₆;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

