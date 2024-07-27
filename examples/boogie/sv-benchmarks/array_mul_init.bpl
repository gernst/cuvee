data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure __VERIFIER_nondet_short() returns (c#result: int);
  modifies c#heap;

procedure main()
  returns (c#result: int)
  modifies c#heap;
{
  var a: [int]int;
  var b: [int]int;
  var k: int;
  var i: int;
  i := 0;
  while(i < 100000) {
    a := a[i := i];
    b := b[i := i];
    var x₃₇₂: int := i;
    i := i + 1;
  }
  i := 0;
  while(i < 100000) {
    var __VERIFIER_nondet_short₃₇₃: int;
    __VERIFIER_nondet_short₃₇₃ := call __VERIFIER_nondet_short();
    if(__VERIFIER_nondet_short₃₇₃ != 0) {
      var __VERIFIER_nondet_short₃₇₄: int;
      __VERIFIER_nondet_short₃₇₄ := call __VERIFIER_nondet_short();
      k := __VERIFIER_nondet_short₃₇₄;
      a := a[i := k];
      b := b[i := k * k];
    }
    var x₃₇₅: int := i;
    i := i + 1;
  }
  i := 0;
  while(i < 100000) {
    assert a[i] == b[i] || b[i] == a[i] * a[i];
    var x₃₇₆: int := i;
    i := i + 1;
  }
}

