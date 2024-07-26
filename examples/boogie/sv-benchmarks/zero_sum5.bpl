data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure __VERIFIER_nondet_short() returns (c#result: int);
  modifies c#heap;

var SIZE: int;

procedure main()
  returns (c#result: int)
  modifies c#heap, SIZE;
{
  var __VERIFIER_nondet_short₉₁₅: int;
  __VERIFIER_nondet_short₉₁₅ := call __VERIFIER_nondet_short();
  SIZE := __VERIFIER_nondet_short₉₁₅;
  if(1 < SIZE) {
    var i: int;
    var a: [int]int;
    var sum: int;
    sum := 0;
    {
      var i: int;
      i := 0;
      while(i < SIZE) {
        var __VERIFIER_nondet_short₉₁₆: int;
        __VERIFIER_nondet_short₉₁₆ := call __VERIFIER_nondet_short();
        a := a[i := __VERIFIER_nondet_short₉₁₆];
        var x₉₁₇: int := i;
        i := i + 1;
      }
    }
    i := 0;
    while(i < SIZE) {
      sum := sum + a[i];
      var x₉₁₈: int := i;
      i := i + 1;
    }
    i := 0;
    while(i < SIZE) {
      sum := sum - a[i];
      var x₉₁₉: int := i;
      i := i + 1;
    }
    i := 0;
    while(i < SIZE) {
      sum := sum + a[i];
      var x₉₂₀: int := i;
      i := i + 1;
    }
    i := 0;
    while(i < SIZE) {
      sum := sum - a[i];
      var x₉₂₁: int := i;
      i := i + 1;
    }
    i := 0;
    while(i < SIZE) {
      sum := sum + a[i];
      var x₉₂₂: int := i;
      i := i + 1;
    }
    i := 0;
    while(i < SIZE) {
      sum := sum - a[i];
      var x₉₂₃: int := i;
      i := i + 1;
    }
    i := 0;
    while(i < SIZE) {
      sum := sum + a[i];
      var x₉₂₄: int := i;
      i := i + 1;
    }
    i := 0;
    while(i < SIZE) {
      sum := sum - a[i];
      var x₉₂₅: int := i;
      i := i + 1;
    }
    i := 0;
    while(i < SIZE) {
      sum := sum + a[i];
      var x₉₂₆: int := i;
      i := i + 1;
    }
    i := 0;
    while(i < SIZE) {
      sum := sum - a[i];
      var x₉₂₇: int := i;
      i := i + 1;
    }
    assert sum == 0;
  }
  c#result := 1;
  return;
}

