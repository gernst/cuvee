data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure mapavg(x: [int]int)
  returns (c#result: int)
{
  var i: int;
  var ret: int;
  ret := 0;
  i := 0;
  while(i < 1000) {
    ret := ret + i + x[i];
    i := i + 1;
  }
  c#result := ret / 1000;
  return;
}

procedure main()
  returns (c#result: int)
{
  var x: [int]int;
  var temp: int;
  var ret: int;
  var ret2: int;
  var ret5: int;
  var i: int;
  i := 0;
  while(i < 1000) {
    var __VERIFIER_nondet_int₉₃₇: int;
    x := x[i := __VERIFIER_nondet_int₉₃₇];
    i := i + 1;
  }
  var mapavg₉₃₉: int;
  mapavg₉₃₉ := call mapavg(x);
  ret := mapavg₉₃₉;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var mapavg₉₄₀: int;
  mapavg₉₄₀ := call mapavg(x);
  ret2 := mapavg₉₄₀;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 1000 - 1) {
    x := x[i := x[i + 1]];
    i := i + 1;
  }
  x := x[1000 - 1 := temp];
  var mapavg₉₄₂: int;
  mapavg₉₄₂ := call mapavg(x);
  ret5 := mapavg₉₄₂;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

