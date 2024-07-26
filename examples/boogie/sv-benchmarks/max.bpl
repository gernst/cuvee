data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure __VERIFIER_nondet_int() returns (c#result: int);
  modifies c#heap;

var N: int;

procedure max(x: [int]int)
  returns (c#result: int)
  modifies c#heap, N;
{
  var i: int;
  var ret: int;
  ret := 0;
  i := 0;
  while(i < N) {
    var x₄₈₅: int;
    if(ret < x[i]) {
      x₄₈₅ := x[i];
    } else {
      x₄₈₅ := ret;
    }
    ret := x₄₈₅;
    var x₄₈₆: int := i;
    i := i + 1;
  }
  c#result := ret;
  return;
}

procedure main()
  returns (c#result: int)
  modifies c#heap, N;
{
  var __VERIFIER_nondet_int₄₈₇: int;
  __VERIFIER_nondet_int₄₈₇ := call __VERIFIER_nondet_int();
  N := __VERIFIER_nondet_int₄₈₇;
  if(1 < N) {
    var x: [int]int;
    var temp: int;
    var ret: int;
    var ret2: int;
    var ret5: int;
    var max₄₈₈: int;
    max₄₈₈ := call max(x);
    ret := max₄₈₈;
    temp := x[0];
    x := x[0 := x[1]];
    x := x[1 := temp];
    var max₄₈₉: int;
    max₄₈₉ := call max(x);
    ret2 := max₄₈₉;
    temp := x[0];
    var i: int;
    i := 0;
    while(i < N - 1) {
      x := x[i := x[i + 1]];
      var x₄₉₀: int := i;
      i := i + 1;
    }
    x := x[N - 1 := temp];
    var max₄₉₁: int;
    max₄₉₁ := call max(x);
    ret5 := max₄₉₁;
    if(ret != ret2 || ret != ret5) {
      assert false;
    }
  }
  c#result := 1;
  return;
}

