data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure __VERIFIER_nondet_int() returns (c#result: int);
  modifies c#heap;

procedure init_nondet(x: [int]int)
  returns (c#result: c#void)
  modifies c#heap;
{
  var i: int;
  i := 0;
  while(i < 10) {
    var __VERIFIER_nondet_int₄₃₂: int;
    __VERIFIER_nondet_int₄₃₂ := call __VERIFIER_nondet_int();
    x := x[i := __VERIFIER_nondet_int₄₃₂];
    var x₄₃₃: int := i;
    i := i + 1;
  }
}

procedure rangesum(x: [int]int)
  returns (c#result: int)
  modifies c#heap;
{
  var i: int;
  var ret: int;
  ret := 0;
  var cnt: int;
  cnt := 0;
  i := 0;
  while(i < 10) {
    if(10 / 2 < i) {
      ret := ret + x[i];
      cnt := cnt + 1;
    }
    var x₄₃₄: int := i;
    i := i + 1;
  }
  if(cnt != 0) {
    c#result := ret / cnt;
    return;
  } else {
    c#result := 0;
    return;
  }
}

procedure main()
  returns (c#result: int)
  modifies c#heap;
{
  var x: [int]int;
  var init_nondet₄₃₅: c#void;
  init_nondet₄₃₅ := call init_nondet(x);
  var temp: int;
  var ret: int;
  var ret2: int;
  var ret5: int;
  var rangesum₄₃₆: int;
  rangesum₄₃₆ := call rangesum(x);
  ret := rangesum₄₃₆;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var rangesum₄₃₇: int;
  rangesum₄₃₇ := call rangesum(x);
  ret2 := rangesum₄₃₇;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 10 - 1) {
    x := x[i := x[i + 1]];
    var x₄₃₈: int := i;
    i := i + 1;
  }
  x := x[10 - 1 := temp];
  var rangesum₄₃₉: int;
  rangesum₄₃₉ := call rangesum(x);
  ret5 := rangesum₄₃₉;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

