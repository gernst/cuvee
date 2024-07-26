data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure __VERIFIER_nondet_int() returns (c#result: int);
  modifies c#heap;

procedure sep(x: [int]int)
  returns (c#result: int)
  modifies c#heap;
{
  var ret: int;
  ret := 0;
  var i: int;
  i := 0;
  while(i < 60) {
    if(x[i] % 2 == 0) {
      var x₄₆₈: int := ret;
      ret := ret + 1;
    } else {
      var x₄₆₉: int := ret;
      ret := ret - 1;
    }
    var x₄₇₀: int := i;
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
  while(i < 60) {
    var __VERIFIER_nondet_int₄₇₁: int;
    __VERIFIER_nondet_int₄₇₁ := call __VERIFIER_nondet_int();
    x := x[i := __VERIFIER_nondet_int₄₇₁];
    var x₄₇₂: int := i;
    i := i + 1;
  }
  var sep₄₇₃: int;
  sep₄₇₃ := call sep(x);
  ret := sep₄₇₃;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var sep₄₇₄: int;
  sep₄₇₄ := call sep(x);
  ret2 := sep₄₇₄;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 60 - 1) {
    x := x[i := x[i + 1]];
    var x₄₇₅: int := i;
    i := i + 1;
  }
  x := x[60 - 1 := temp];
  var sep₄₇₆: int;
  sep₄₇₆ := call sep(x);
  ret5 := sep₄₇₆;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

