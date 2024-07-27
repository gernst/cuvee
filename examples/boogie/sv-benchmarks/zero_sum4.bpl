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
  var __VERIFIER_nondet_short₉₀₄: int;
  __VERIFIER_nondet_short₉₀₄ := call __VERIFIER_nondet_short();
  SIZE := __VERIFIER_nondet_short₉₀₄;
  if(1 < SIZE) {
    var i: int;
    var a: [int]int;
    var sum: int;
    sum := 0;
    {
      var i: int;
      i := 0;
      while(i < SIZE) {
        var __VERIFIER_nondet_short₉₀₅: int;
        __VERIFIER_nondet_short₉₀₅ := call __VERIFIER_nondet_short();
        a := a[i := __VERIFIER_nondet_short₉₀₅];
        var x₉₀₆: int := i;
        i := i + 1;
      }
    }
    i := 0;
    while(i < SIZE) {
      sum := sum + a[i];
      var x₉₀₇: int := i;
      i := i + 1;
    }
    i := 0;
    while(i < SIZE) {
      sum := sum - a[i];
      var x₉₀₈: int := i;
      i := i + 1;
    }
    i := 0;
    while(i < SIZE) {
      sum := sum + a[i];
      var x₉₀₉: int := i;
      i := i + 1;
    }
    i := 0;
    while(i < SIZE) {
      sum := sum - a[i];
      var x₉₁₀: int := i;
      i := i + 1;
    }
    i := 0;
    while(i < SIZE) {
      sum := sum + a[i];
      var x₉₁₁: int := i;
      i := i + 1;
    }
    i := 0;
    while(i < SIZE) {
      sum := sum - a[i];
      var x₉₁₂: int := i;
      i := i + 1;
    }
    i := 0;
    while(i < SIZE) {
      sum := sum + a[i];
      var x₉₁₃: int := i;
      i := i + 1;
    }
    i := 0;
    while(i < SIZE) {
      sum := sum - a[i];
      var x₉₁₄: int := i;
      i := i + 1;
    }
    assert sum == 0;
  }
  c#result := 1;
  return;
}

