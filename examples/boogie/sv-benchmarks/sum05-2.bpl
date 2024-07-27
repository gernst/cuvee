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
  while(i < 5) {
    ret := ret + x[i];
    var x₆₄₆: int := i;
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
  while(i < 5) {
    var __VERIFIER_nondet_int₆₄₇: int;
    __VERIFIER_nondet_int₆₄₇ := call __VERIFIER_nondet_int();
    x := x[i := __VERIFIER_nondet_int₆₄₇];
    var x₆₄₈: int := i;
    i := i + 1;
  }
  var sum₆₄₉: int;
  sum₆₄₉ := call sum(x);
  ret := sum₆₄₉;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var sum₆₅₀: int;
  sum₆₅₀ := call sum(x);
  ret2 := sum₆₅₀;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 5 - 1) {
    x := x[i := x[i + 1]];
    var x₆₅₁: int := i;
    i := i + 1;
  }
  x := x[5 - 1 := temp];
  var sum₆₅₂: int;
  sum₆₅₂ := call sum(x);
  ret5 := sum₆₅₂;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

