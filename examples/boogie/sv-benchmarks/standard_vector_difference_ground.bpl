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
  var a: [int]int;
  var b: [int]int;
  var c: [int]int;
  var i: int;
  i := 0;
  i := 0;
  while(i < 100000) {
    var __VERIFIER_nondet_int₁₆₇: int;
    __VERIFIER_nondet_int₁₆₇ := call __VERIFIER_nondet_int();
    a := a[i := __VERIFIER_nondet_int₁₆₇];
    var __VERIFIER_nondet_int₁₆₈: int;
    __VERIFIER_nondet_int₁₆₈ := call __VERIFIER_nondet_int();
    b := b[i := __VERIFIER_nondet_int₁₆₈];
    var x₁₆₉: int := i;
    i := i + 1;
  }
  i := 0;
  while(i < 100000) {
    c := c[i := a[i] - b[i]];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000) {
    assert c[x] == a[x] - b[x];
    var x₁₇₀: int := x;
    x := x + 1;
  }
  c#result := 0;
  return;
}

