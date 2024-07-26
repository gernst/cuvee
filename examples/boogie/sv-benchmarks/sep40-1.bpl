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
  while(i < 40) {
    if(x[i] % 2 == 0) {
      var x₄₉₂: int := ret;
      ret := ret + 1;
    } else {
      var x₄₉₃: int := ret;
      ret := ret - 1;
    }
    var x₄₉₄: int := i;
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
  while(i < 40) {
    var __VERIFIER_nondet_int₄₉₅: int;
    __VERIFIER_nondet_int₄₉₅ := call __VERIFIER_nondet_int();
    x := x[i := __VERIFIER_nondet_int₄₉₅];
    var x₄₉₆: int := i;
    i := i + 1;
  }
  var sep₄₉₇: int;
  sep₄₉₇ := call sep(x);
  ret := sep₄₉₇;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var sep₄₉₈: int;
  sep₄₉₈ := call sep(x);
  ret2 := sep₄₉₈;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 40 - 1) {
    x := x[i := x[i + 1]];
    var x₄₉₉: int := i;
    i := i + 1;
  }
  x := x[40 - 1 := temp];
  var sep₅₀₀: int;
  sep₅₀₀ := call sep(x);
  ret5 := sep₅₀₀;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

