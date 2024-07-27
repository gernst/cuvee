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
  while(i < 60) {
    ret := ret + x[i];
    var x₄₀₀: int := i;
    i := i + 1;
  }
  c#result := ret / 60;
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
  while(i < 60) {
    var __VERIFIER_nondet_int₄₀₁: int;
    __VERIFIER_nondet_int₄₀₁ := call __VERIFIER_nondet_int();
    x := x[i := __VERIFIER_nondet_int₄₀₁];
    var x₄₀₂: int := i;
    i := i + 1;
  }
  var avg₄₀₃: int;
  avg₄₀₃ := call avg(x);
  ret := avg₄₀₃;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var avg₄₀₄: int;
  avg₄₀₄ := call avg(x);
  ret2 := avg₄₀₄;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 60 - 1) {
    x := x[i := x[i + 1]];
    var x₄₀₅: int := i;
    i := i + 1;
  }
  x := x[60 - 1 := temp];
  var avg₄₀₆: int;
  avg₄₀₆ := call avg(x);
  ret5 := avg₄₀₆;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

