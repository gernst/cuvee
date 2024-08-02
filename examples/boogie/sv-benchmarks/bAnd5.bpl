data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var N: int;

procedure bAnd(x: [int]int)
  returns (c#result: int)
  modifies N;
{
  var i: int;
  var res: int;
  res := x[0];
  i := 1;
  while(i < N) {
    res := c#bitand(res, x[i]);
    i := i + 1;
  }
  c#result := res;
  return;
}

procedure main()
  returns (c#result: int)
  modifies N;
{
  var __VERIFIER_nondet_int₁₀₂₇: int;
  N := __VERIFIER_nondet_int₁₀₂₇;
  if(1 < N) {
    var x: [int]int;
    var temp: int;
    var ret: int;
    var ret2: int;
    var ret5: int;
    var i: int;
    i := 0;
    while(i < N) {
      var __VERIFIER_nondet_int₁₀₂₈: int;
      x := x[i := __VERIFIER_nondet_int₁₀₂₈];
      i := i + 1;
    }
    var bAnd₁₀₃₀: int;
    bAnd₁₀₃₀ := call bAnd(x);
    ret := bAnd₁₀₃₀;
    temp := x[0];
    x := x[0 := x[1]];
    x := x[1 := temp];
    var bAnd₁₀₃₁: int;
    bAnd₁₀₃₁ := call bAnd(x);
    ret2 := bAnd₁₀₃₁;
    temp := x[0];
    var i: int;
    i := 0;
    while(i < N - 1) {
      x := x[i := x[i + 1]];
      i := i + 1;
    }
    x := x[N - 1 := temp];
    var bAnd₁₀₃₃: int;
    bAnd₁₀₃₃ := call bAnd(x);
    ret5 := bAnd₁₀₃₃;
    if(ret != ret2 || ret != ret5) {
      assert false;
    }
  }
  c#result := 1;
  return;
}

