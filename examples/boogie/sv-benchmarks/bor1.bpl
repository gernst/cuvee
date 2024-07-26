data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure __VERIFIER_nondet_int() returns (c#result: int);
  modifies c#heap;

procedure bor(x: [int]int)
  returns (c#result: int)
  modifies c#heap;
{
  var i: int;
  var res: int;
  res := x[0];
  i := 1;
  while(i < 100) {
    res := c#bitor(res, x[i]);
    var x₁₀₁₉: int := i;
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
    var __VERIFIER_nondet_int₁₀₂₀: int;
    __VERIFIER_nondet_int₁₀₂₀ := call __VERIFIER_nondet_int();
    x := x[i := __VERIFIER_nondet_int₁₀₂₀];
    var x₁₀₂₁: int := i;
    i := i + 1;
  }
  var bor₁₀₂₂: int;
  bor₁₀₂₂ := call bor(x);
  ret := bor₁₀₂₂;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var bor₁₀₂₃: int;
  bor₁₀₂₃ := call bor(x);
  ret2 := bor₁₀₂₃;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 100 - 1) {
    x := x[i := x[i + 1]];
    var x₁₀₂₄: int := i;
    i := i + 1;
  }
  x := x[100 - 1 := temp];
  var bor₁₀₂₅: int;
  bor₁₀₂₅ := call bor(x);
  ret5 := bor₁₀₂₅;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

