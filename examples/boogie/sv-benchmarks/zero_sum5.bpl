data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var SIZE: int;

procedure main()
  returns (c#result: int)
  modifies SIZE;
{
  havoc SIZE;
  if(1 < SIZE) {
    var i: int;
    var a: [int]int;
    var sum: int := 0;
    {
      var i: int := 0;
      while(i < SIZE) {
        var __VERIFIER_nondet_short₁: int;
        a := a[i := __VERIFIER_nondet_short₁];
        i := i + 1;
      }
    }
    i := 0;
    while(i < SIZE) {
      sum := sum + a[i];
      i := i + 1;
    }
    i := 0;
    while(i < SIZE) {
      sum := sum - a[i];
      i := i + 1;
    }
    i := 0;
    while(i < SIZE) {
      sum := sum + a[i];
      i := i + 1;
    }
    i := 0;
    while(i < SIZE) {
      sum := sum - a[i];
      i := i + 1;
    }
    i := 0;
    while(i < SIZE) {
      sum := sum + a[i];
      i := i + 1;
    }
    i := 0;
    while(i < SIZE) {
      sum := sum - a[i];
      i := i + 1;
    }
    i := 0;
    while(i < SIZE) {
      sum := sum + a[i];
      i := i + 1;
    }
    i := 0;
    while(i < SIZE) {
      sum := sum - a[i];
      i := i + 1;
    }
    i := 0;
    while(i < SIZE) {
      sum := sum + a[i];
      i := i + 1;
    }
    i := 0;
    while(i < SIZE) {
      sum := sum - a[i];
      i := i + 1;
    }
    assert sum == 0;
  }
  c#result := 1;
  return;
}

