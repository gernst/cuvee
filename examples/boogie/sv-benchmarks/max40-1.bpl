data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure __VERIFIER_nondet_int() returns (c#result: int);
  modifies c#heap;

procedure max(x: [int]int)
  returns (c#result: int)
  modifies c#heap;
{
  var i: int;
  var ret: int;
  ret := 0;
  i := 0;
  while(i < 40) {
    var x₇₁₈: int;
    if(ret < x[i]) {
      x₇₁₈ := x[i];
    } else {
      x₇₁₈ := ret;
    }
    ret := x₇₁₈;
    var x₇₁₉: int := i;
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
    var __VERIFIER_nondet_int₇₂₀: int;
    __VERIFIER_nondet_int₇₂₀ := call __VERIFIER_nondet_int();
    x := x[i := __VERIFIER_nondet_int₇₂₀];
    var x₇₂₁: int := i;
    i := i + 1;
  }
  var max₇₂₂: int;
  max₇₂₂ := call max(x);
  ret := max₇₂₂;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var max₇₂₃: int;
  max₇₂₃ := call max(x);
  ret2 := max₇₂₃;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 40 - 1) {
    x := x[i := x[i + 1]];
    var x₇₂₄: int := i;
    i := i + 1;
  }
  x := x[40 - 1 := temp];
  var max₇₂₅: int;
  max₇₂₅ := call max(x);
  ret5 := max₇₂₅;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

