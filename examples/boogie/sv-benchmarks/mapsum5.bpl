data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var N: int;

procedure mapsum(x: [int]int)
  returns (c#result: int)
  modifies N;
{
  var i: int;
  var ret: int;
  ret := 0;
  i := 0;
  while(i < N) {
    ret := ret + i + x[i];
    i := i + 1;
  }
  c#result := ret;
  return;
}

procedure main()
  returns (c#result: int)
  modifies N;
{
  var __VERIFIER_nondet_int₉₂₉: int;
  N := __VERIFIER_nondet_int₉₂₉;
  if(1 < N) {
    var x: [int]int;
    var temp: int;
    var ret: int;
    var ret2: int;
    var ret5: int;
    var i: int;
    i := 0;
    while(i < N) {
      var __VERIFIER_nondet_int₉₃₀: int;
      x := x[i := __VERIFIER_nondet_int₉₃₀];
      i := i + 1;
    }
    var mapsum₉₃₂: int;
    mapsum₉₃₂ := call mapsum(x);
    ret := mapsum₉₃₂;
    temp := x[0];
    x := x[0 := x[1]];
    x := x[1 := temp];
    var mapsum₉₃₃: int;
    mapsum₉₃₃ := call mapsum(x);
    ret2 := mapsum₉₃₃;
    temp := x[0];
    var i: int;
    i := 0;
    while(i < N - 1) {
      x := x[i := x[i + 1]];
      i := i + 1;
    }
    x := x[N - 1 := temp];
    var mapsum₉₃₅: int;
    mapsum₉₃₅ := call mapsum(x);
    ret5 := mapsum₉₃₅;
    if(ret != ret2 || ret != ret5) {
      assert false;
    }
  }
  c#result := 1;
  return;
}

