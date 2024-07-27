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
  while(i < 100) {
    ret := ret + i + x[i];
    var x₉₇₇: int := i;
    i := i + 1;
  }
  c#result := ret / 100;
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
    var __VERIFIER_nondet_int₉₇₈: int;
    __VERIFIER_nondet_int₉₇₈ := call __VERIFIER_nondet_int();
    x := x[i := __VERIFIER_nondet_int₉₇₈];
    var x₉₇₉: int := i;
    i := i + 1;
  }
  var mapavg₉₈₀: int;
  mapavg₉₈₀ := call mapavg(x);
  ret := mapavg₉₈₀;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var mapavg₉₈₁: int;
  mapavg₉₈₁ := call mapavg(x);
  ret2 := mapavg₉₈₁;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 100 - 1) {
    x := x[i := x[i + 1]];
    var x₉₈₂: int := i;
    i := i + 1;
  }
  x := x[100 - 1 := temp];
  var mapavg₉₈₃: int;
  mapavg₉₈₃ := call mapavg(x);
  ret5 := mapavg₉₈₃;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

