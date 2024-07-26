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
  var aa: [int]int;
  var a: int;
  a := 0;
  var i: int;
  i := 0;
  while(i < 100000) {
    var __VERIFIER_nondet_int₁₇₂: int;
    __VERIFIER_nondet_int₁₇₂ := call __VERIFIER_nondet_int();
    aa := aa[i := __VERIFIER_nondet_int₁₇₂];
    var x₁₇₃: int := i;
    i := i + 1;
  }
  while(0 <= aa[a]) {
    var x₁₇₄: int := a;
    a := a + 1;
  }
  var x: int;
  x := 0;
  while(x < a) {
    assert 0 <= aa[x];
    var x₁₇₅: int := x;
    x := x + 1;
  }
  c#result := 0;
  return;
}

