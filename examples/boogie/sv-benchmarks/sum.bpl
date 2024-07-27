data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure __VERIFIER_nondet_int() returns (c#result: int);
  modifies c#heap;

var N: int;

procedure sum(x: [int]int)
  returns (c#result: int)
  modifies c#heap, N;
{
  var i: int;
  var ret: int;
  ret := 0;
  i := 0;
  while(i < N) {
    ret := ret + x[i];
    var x₆₆₈: int := i;
    i := i + 1;
  }
  c#result := ret;
  return;
}

procedure main()
  returns (c#result: int)
  modifies c#heap, N;
{
  var __VERIFIER_nondet_int₆₆₉: int;
  __VERIFIER_nondet_int₆₆₉ := call __VERIFIER_nondet_int();
  N := __VERIFIER_nondet_int₆₆₉;
  if(1 < N) {
    var x: [int]int;
    var temp: int;
    var ret: int;
    var ret2: int;
    var ret5: int;
    var sum₆₇₀: int;
    sum₆₇₀ := call sum(x);
    ret := sum₆₇₀;
    temp := x[0];
    x := x[0 := x[1]];
    x := x[1 := temp];
    var sum₆₇₁: int;
    sum₆₇₁ := call sum(x);
    ret2 := sum₆₇₁;
    temp := x[0];
    var i: int;
    i := 0;
    while(i < N - 1) {
      x := x[i := x[i + 1]];
      var x₆₇₂: int := i;
      i := i + 1;
    }
    x := x[N - 1 := temp];
    var sum₆₇₃: int;
    sum₆₇₃ := call sum(x);
    ret5 := sum₆₇₃;
    if(ret != ret2 || ret != ret5) {
      assert false;
    }
  }
  c#result := 1;
  return;
}

