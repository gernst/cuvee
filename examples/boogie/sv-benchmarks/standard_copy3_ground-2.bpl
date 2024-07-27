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
  var a3: [int]int;
  var a4: [int]int;
  var a: int;
  a := 0;
  while(a < 100000) {
    var __VERIFIER_nondet_int₆₁: int;
    __VERIFIER_nondet_int₆₁ := call __VERIFIER_nondet_int();
    a1 := a1[a := __VERIFIER_nondet_int₆₁];
    var __VERIFIER_nondet_int₆₂: int;
    __VERIFIER_nondet_int₆₂ := call __VERIFIER_nondet_int();
    a3 := a3[a := __VERIFIER_nondet_int₆₂];
    var x₆₃: int := a;
    a := a + 1;
  }
  var i: int;
  i := 0;
  while(i < 100000) {
    a2 := a2[i := a1[i]];
    var x₆₄: int := i;
    i := i + 1;
  }
  i := 0;
  while(i < 100000) {
    a4 := a4[i := a2[i]];
    var x₆₅: int := i;
    i := i + 1;
  }
  i := 0;
  while(i < 100000) {
    a4 := a4[i := a3[i]];
    var x₆₆: int := i;
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000) {
    assert a1[x] == a4[x];
    var x₆₇: int := x;
    x := x + 1;
  }
  c#result := 0;
  return;
}

