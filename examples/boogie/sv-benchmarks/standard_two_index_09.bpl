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
  var i: int;
  i := 0;
  var j: int;
  j := 0;
  while(i < 100000) {
    var __VERIFIER_nondet_int₁₂₆: int;
    __VERIFIER_nondet_int₁₂₆ := call __VERIFIER_nondet_int();
    b := b[i := __VERIFIER_nondet_int₁₂₆];
    i := i + 1;
  }
  i := 1;
  while(i < 100000) {
    a := a[j := b[i]];
    i := i + 9;
    j := j + 1;
  }
  i := 1;
  j := 0;
  while(i < 100000) {
    assert a[j] == b[9 * j + 1];
    i := i + 9;
    j := j + 1;
  }
  c#result := 0;
  return;
}

