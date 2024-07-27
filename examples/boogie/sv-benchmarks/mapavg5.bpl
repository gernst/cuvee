data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure __VERIFIER_nondet_int() returns (c#result: int);
  modifies c#heap;

var N: int;

procedure mapavg(x: [int]int)
  returns (c#result: int)
  modifies c#heap, N;
{
  var i: int;
  var ret: int;
  ret := 0;
  i := 0;
  while(i < N) {
    ret := ret + i + x[i];
    var x₈₃₈: int := i;
    i := i + 1;
  }
  c#result := ret / N;
  return;
}

procedure main()
  returns (c#result: int)
  modifies c#heap, N;
{
  var __VERIFIER_nondet_int₈₃₉: int;
  __VERIFIER_nondet_int₈₃₉ := call __VERIFIER_nondet_int();
  N := __VERIFIER_nondet_int₈₃₉;
  if(1 < N) {
    var x: [int]int;
    var temp: int;
    var ret: int;
    var ret2: int;
    var ret5: int;
    var i: int;
    i := 0;
    while(i < N) {
      var __VERIFIER_nondet_int₈₄₀: int;
      __VERIFIER_nondet_int₈₄₀ := call __VERIFIER_nondet_int();
      x := x[i := __VERIFIER_nondet_int₈₄₀];
      var x₈₄₁: int := i;
      i := i + 1;
    }
    var mapavg₈₄₂: int;
    mapavg₈₄₂ := call mapavg(x);
    ret := mapavg₈₄₂;
    temp := x[0];
    x := x[0 := x[1]];
    x := x[1 := temp];
    var mapavg₈₄₃: int;
    mapavg₈₄₃ := call mapavg(x);
    ret2 := mapavg₈₄₃;
    temp := x[0];
    var i: int;
    i := 0;
    while(i < N - 1) {
      x := x[i := x[i + 1]];
      var x₈₄₄: int := i;
      i := i + 1;
    }
    x := x[N - 1 := temp];
    var mapavg₈₄₅: int;
    mapavg₈₄₅ := call mapavg(x);
    ret5 := mapavg₈₄₅;
    if(ret != ret2 || ret != ret5) {
      assert false;
    }
  }
  c#result := 1;
  return;
}

