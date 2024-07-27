data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure __VERIFIER_nondet_int() returns (c#result: int);
  modifies c#heap;

procedure avg(x: [int]int)
  returns (c#result: int)
  modifies c#heap;
{
  var i: int;
  var ret: int;
  ret := 0;
  i := 0;
  while(i < 20) {
    ret := ret + x[i];
    var x₄₄₀: int := i;
    i := i + 1;
  }
  c#result := ret / 20;
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
    var __VERIFIER_nondet_int₄₄₁: int;
    __VERIFIER_nondet_int₄₄₁ := call __VERIFIER_nondet_int();
    x := x[i := __VERIFIER_nondet_int₄₄₁];
    var x₄₄₂: int := i;
    i := i + 1;
  }
  var avg₄₄₃: int;
  avg₄₄₃ := call avg(x);
  ret := avg₄₄₃;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var avg₄₄₄: int;
  avg₄₄₄ := call avg(x);
  ret2 := avg₄₄₄;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 20 - 1) {
    x := x[i := x[i + 1]];
    var x₄₄₅: int := i;
    i := i + 1;
  }
  x := x[20 - 1 := temp];
  var avg₄₄₆: int;
  avg₄₄₆ := call avg(x);
  ret5 := avg₄₄₆;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

