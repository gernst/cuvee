data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure __VERIFIER_nondet_int() returns (c#result: int);
  modifies c#heap;

procedure main()
  returns (c#result: int)
  modifies c#heap;
{
  var a1: [int]int;
  var a2: [int]int;
  var a: int;
  a := 0;
  while(a < 100000) {
    var __VERIFIER_nondet_int₁₄₀: int;
    __VERIFIER_nondet_int₁₄₀ := call __VERIFIER_nondet_int();
    a1 := a1[a := __VERIFIER_nondet_int₁₄₀];
    var __VERIFIER_nondet_int₁₄₁: int;
    __VERIFIER_nondet_int₁₄₁ := call __VERIFIER_nondet_int();
    a2 := a2[a := __VERIFIER_nondet_int₁₄₁];
    var x₁₄₂: int := a;
    a := a + 1;
  }
  var i: int;
  i := 0;
  while(i < 100000) {
    a1 := a1[i := a1[i]];
    var x₁₄₃: int := i;
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000) {
    assert a1[x] == a2[x];
    var x₁₄₄: int := x;
    x := x + 1;
  }
  c#result := 0;
  return;
}

