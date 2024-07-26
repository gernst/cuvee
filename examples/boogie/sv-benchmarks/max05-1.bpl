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
  while(i < 5) {
    var x₇₁₀: int;
    if(ret < x[i]) {
      x₇₁₀ := x[i];
    } else {
      x₇₁₀ := ret;
    }
    ret := x₇₁₀;
    var x₇₁₁: int := i;
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
  while(i < 5) {
    var __VERIFIER_nondet_int₇₁₂: int;
    __VERIFIER_nondet_int₇₁₂ := call __VERIFIER_nondet_int();
    x := x[i := __VERIFIER_nondet_int₇₁₂];
    var x₇₁₃: int := i;
    i := i + 1;
  }
  var max₇₁₄: int;
  max₇₁₄ := call max(x);
  ret := max₇₁₄;
  temp := x[0];
  x := x[0 := x[1]];
  x := x[1 := temp];
  var max₇₁₅: int;
  max₇₁₅ := call max(x);
  ret2 := max₇₁₅;
  temp := x[0];
  var i: int;
  i := 0;
  while(i < 5 - 1) {
    x := x[i := x[i + 1]];
    var x₇₁₆: int := i;
    i := i + 1;
  }
  x := x[5 - 1 := temp];
  var max₇₁₇: int;
  max₇₁₇ := call max(x);
  ret5 := max₇₁₇;
  if(ret != ret2 || ret != ret5) {
    assert false;
  }
  c#result := 1;
  return;
}

