data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure __VERIFIER_nondet_int() returns (c#result: int);
  modifies c#heap;

var N: int;

procedure bor(x: [int]int)
  returns (c#result: int)
  modifies c#heap, N;
{
  var i: int;
  var res: int;
  res := x[0];
  i := 1;
  while(i < N) {
    res := c#bitor(res, x[i]);
    var x₉₉₅: int := i;
    i := i + 1;
  }
  c#result := res;
  return;
}

procedure main()
  returns (c#result: int)
  modifies c#heap, N;
{
  var __VERIFIER_nondet_int₉₉₆: int;
  __VERIFIER_nondet_int₉₉₆ := call __VERIFIER_nondet_int();
  N := __VERIFIER_nondet_int₉₉₆;
  if(1 < N) {
    var x: [int]int;
    var temp: int;
    var ret: int;
    var ret2: int;
    var ret5: int;
    var i: int;
    i := 0;
    while(i < N) {
      var __VERIFIER_nondet_int₉₉₇: int;
      __VERIFIER_nondet_int₉₉₇ := call __VERIFIER_nondet_int();
      x := x[i := __VERIFIER_nondet_int₉₉₇];
      var x₉₉₈: int := i;
      i := i + 1;
    }
    var bor₉₉₉: int;
    bor₉₉₉ := call bor(x);
    ret := bor₉₉₉;
    temp := x[0];
    x := x[0 := x[1]];
    x := x[1 := temp];
    var bor₁₀₀₀: int;
    bor₁₀₀₀ := call bor(x);
    ret2 := bor₁₀₀₀;
    temp := x[0];
    var i: int;
    i := 0;
    while(i < N - 1) {
      x := x[i := x[i + 1]];
      var x₁₀₀₁: int := i;
      i := i + 1;
    }
    x := x[N - 1 := temp];
    var bor₁₀₀₂: int;
    bor₁₀₀₂ := call bor(x);
    ret5 := bor₁₀₀₂;
    if(ret != ret2 || ret != ret5) {
      assert false;
    }
  }
  c#result := 1;
  return;
}

