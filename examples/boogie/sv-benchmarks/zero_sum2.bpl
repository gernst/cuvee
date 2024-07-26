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
  var __VERIFIER_nondet_short₉₅₀: int;
  __VERIFIER_nondet_short₉₅₀ := call __VERIFIER_nondet_short();
  SIZE := __VERIFIER_nondet_short₉₅₀;
  if(1 < SIZE) {
    var i: int;
    var a: [int]int;
    var sum: int;
    sum := 0;
    {
      var i: int;
      i := 0;
      while(i < SIZE) {
        var __VERIFIER_nondet_short₉₅₁: int;
        __VERIFIER_nondet_short₉₅₁ := call __VERIFIER_nondet_short();
        a := a[i := __VERIFIER_nondet_short₉₅₁];
        var x₉₅₂: int := i;
        i := i + 1;
      }
    }
    i := 0;
    while(i < SIZE) {
      sum := sum + a[i];
      var x₉₅₃: int := i;
      i := i + 1;
    }
    i := 0;
    while(i < SIZE) {
      sum := sum - a[i];
      var x₉₅₄: int := i;
      i := i + 1;
    }
    i := 0;
    while(i < SIZE) {
      sum := sum + a[i];
      var x₉₅₅: int := i;
      i := i + 1;
    }
    i := 0;
    while(i < SIZE) {
      sum := sum - a[i];
      var x₉₅₆: int := i;
      i := i + 1;
    }
    assert sum == 0;
  }
  c#result := 1;
  return;
}

