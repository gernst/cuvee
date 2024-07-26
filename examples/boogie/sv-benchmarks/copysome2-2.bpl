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
  var i: int;
  var z: int;
  z := 150000;
  i := 0;
  while(i < 200000) {
    var __VERIFIER_nondet_int₇₈₁: int;
    __VERIFIER_nondet_int₇₈₁ := call __VERIFIER_nondet_int();
    a1 := a1[i := __VERIFIER_nondet_int₇₈₁];
    var __VERIFIER_nondet_int₇₈₂: int;
    __VERIFIER_nondet_int₇₈₂ := call __VERIFIER_nondet_int();
    a2 := a2[i := __VERIFIER_nondet_int₇₈₂];
    var __VERIFIER_nondet_int₇₈₃: int;
    __VERIFIER_nondet_int₇₈₃ := call __VERIFIER_nondet_int();
    a3 := a3[i := __VERIFIER_nondet_int₇₈₃];
    var x₇₈₄: int := i;
    i := i + 1;
  }
  i := 0;
  while(i < 200000) {
    if(i != z) {
      a2 := a2[i := a1[i]];
    }
    var x₇₈₅: int := i;
    i := i + 1;
  }
  i := 0;
  while(i < 200000) {
    if(i != z) {
      a3 := a3[i := a2[i]];
    } else {
      a3 := a3[i := a1[i]];
    }
    var x₇₈₆: int := i;
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 200000) {
    assert a2[x] == a3[x];
    var x₇₈₇: int := x;
    x := x + 1;
  }
  c#result := 0;
  return;
}

