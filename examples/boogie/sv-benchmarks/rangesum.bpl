data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure __VERIFIER_nondet_int() returns (c#result: int);
  modifies c#heap;

var N: int;

procedure init_nondet(x: [int]int)
  returns (c#result: c#void)
  modifies c#heap, N;
{
  var i: int;
  i := 0;
  while(i < N) {
    var __VERIFIER_nondet_int₅₆₆: int;
    __VERIFIER_nondet_int₅₆₆ := call __VERIFIER_nondet_int();
    x := x[i := __VERIFIER_nondet_int₅₆₆];
    var x₅₆₇: int := i;
    i := i + 1;
  }
}

procedure rangesum(x: [int]int)
  returns (c#result: int)
  modifies c#heap, N;
{
  var i: int;
  var ret: int;
  ret := 0;
  var cnt: int;
  cnt := 0;
  i := 0;
  while(i < N) {
    if(N / 2 < i) {
      ret := ret + x[i];
      cnt := cnt + 1;
    }
    var x₅₆₈: int := i;
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
  modifies c#heap, N;
{
  var __VERIFIER_nondet_int₅₆₉: int;
  __VERIFIER_nondet_int₅₆₉ := call __VERIFIER_nondet_int();
  N := __VERIFIER_nondet_int₅₆₉;
  if(1 < N) {
    var x: [int]int;
    var init_nondet₅₇₀: c#void;
    init_nondet₅₇₀ := call init_nondet(x);
    var temp: int;
    var ret: int;
    var ret2: int;
    var ret5: int;
    var rangesum₅₇₁: int;
    rangesum₅₇₁ := call rangesum(x);
    ret := rangesum₅₇₁;
    temp := x[0];
    x := x[0 := x[1]];
    x := x[1 := temp];
    var rangesum₅₇₂: int;
    rangesum₅₇₂ := call rangesum(x);
    ret2 := rangesum₅₇₂;
    temp := x[0];
    var i: int;
    i := 0;
    while(i < N - 1) {
      x := x[i := x[i + 1]];
      var x₅₇₃: int := i;
      i := i + 1;
    }
    x := x[N - 1 := temp];
    var rangesum₅₇₄: int;
    rangesum₅₇₄ := call rangesum(x);
    ret5 := rangesum₅₇₄;
    if(ret != ret2 || ret != ret5) {
      assert false;
    }
  }
  c#result := 1;
  return;
}

