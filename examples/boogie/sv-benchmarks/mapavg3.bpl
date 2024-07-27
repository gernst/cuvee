data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure __VERIFIER_nondet_int() returns (c#result: int);
  modifies c#heap;

procedure mapavg(x: [int]int)
  returns (c#result: int)
  modifies c#heap;
{
  var i: int;
  var ret: int;
  ret := 0;
  i := 0;
  while(i < 10000) {
    ret := ret + i + x[i];
    var x₉₅₇: int := i;
    i := i + 1;
  }
  c#result := ret / 10000;
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
  while(i < 10000) {
    var __VERIFIER_nondet_int₉₅₈: int;
    __VERIFIER_nondet_int₉₅₈ := call __VERIFIER_nondet_int();
    x := x[i := __VERIFIER_nondet_int₉₅₈];
    var x₉₅₉: int := i;
    i := i + 1;
  }
  var mapavg₉₆₀: int;
  mapavg₉₆₀ := call mapavg(x);
  ret := mapavg₉₆₀;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var mapavg₉₆₁: int;
  mapavg₉₆₁ := call mapavg(x);
  ret2 := mapavg₉₆₁;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 10000 - 1) {
    x := x[i := x[i + 1]];
    var x₉₆₂: int := i;
    i := i + 1;
  }
  x := x[10000 - 1 := temp];
  var mapavg₉₆₃: int;
  mapavg₉₆₃ := call mapavg(x);
  ret5 := mapavg₉₆₃;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

