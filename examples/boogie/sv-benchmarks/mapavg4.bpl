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
  while(i < 100000) {
    ret := ret + i + x[i];
    var x₈₉₀: int := i;
    i := i + 1;
  }
  c#result := ret / 100000;
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
  while(i < 100000) {
    var __VERIFIER_nondet_int₈₉₁: int;
    __VERIFIER_nondet_int₈₉₁ := call __VERIFIER_nondet_int();
    x := x[i := __VERIFIER_nondet_int₈₉₁];
    var x₈₉₂: int := i;
    i := i + 1;
  }
  var mapavg₈₉₃: int;
  mapavg₈₉₃ := call mapavg(x);
  ret := mapavg₈₉₃;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var mapavg₈₉₄: int;
  mapavg₈₉₄ := call mapavg(x);
  ret2 := mapavg₈₉₄;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 100000 - 1) {
    x := x[i := x[i + 1]];
    var x₈₉₅: int := i;
    i := i + 1;
  }
  x := x[100000 - 1 := temp];
  var mapavg₈₉₆: int;
  mapavg₈₉₆ := call mapavg(x);
  ret5 := mapavg₈₉₆;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

