data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var N: int;

procedure sep(x: [int]int)
  returns (c#result: int)
  modifies N;
{
  var ret: int;
  ret := 0;
  var i: int;
  i := 0;
  while(i < N) {
    if(x[i] % 2 == 0) {
      ret := ret + 1;
    } else {
      ret := ret - 1;
    }
    i := i + 1;
  }
  c#result := ret;
  return;
}

procedure main()
  returns (c#result: int)
  modifies N;
{
  var __VERIFIER_nondet_int₅₉₁: int;
  N := __VERIFIER_nondet_int₅₉₁;
  if(1 < N) {
    var x: [int]int;
    var temp: int;
    var ret: int;
    var ret2: int;
    var ret5: int;
    var sep₅₉₂: int;
    sep₅₉₂ := call sep(x);
    ret := sep₅₉₂;
    temp := x[0];
    x := x[0 := x[1]];
    x := x[1 := temp];
    var sep₅₉₃: int;
    sep₅₉₃ := call sep(x);
    ret2 := sep₅₉₃;
    temp := x[0];
    var i: int;
    i := 0;
    while(i < N - 1) {
      x := x[i := x[i + 1]];
      i := i + 1;
    }
    x := x[N - 1 := temp];
    var sep₅₉₅: int;
    sep₅₉₅ := call sep(x);
    ret5 := sep₅₉₅;
    if(ret != ret2 || ret != ret5) {
      assert false;
    }
  }
  c#result := 1;
  return;
}

