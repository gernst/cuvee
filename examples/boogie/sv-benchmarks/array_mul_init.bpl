data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var a: [int]int;
  var b: [int]int;
  var k: int;
  var i: int;
  i := 0;
  while(i < 100000) {
    a := a[i := i];
    b := b[i := i];
    i := i + 1;
  }
  i := 0;
  while(i < 100000) {
    var __VERIFIER_nondet_short₂: int;
    if(__VERIFIER_nondet_short₂ != 0) {
      havoc k;
      a := a[i := k];
      b := b[i := k * k];
    }
    i := i + 1;
  }
  i := 0;
  while(i < 100000) {
    assert a[i] == b[i] || b[i] == a[i] * a[i];
    i := i + 1;
  }
}

