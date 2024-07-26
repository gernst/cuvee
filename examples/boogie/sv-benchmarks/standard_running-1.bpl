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
  i := 0;
  while(i < 100000) {
    var __VERIFIER_nondet_int₁₃₅: int;
    __VERIFIER_nondet_int₁₃₅ := call __VERIFIER_nondet_int();
    a := a[i := __VERIFIER_nondet_int₁₃₅];
    var x₁₃₆: int := i;
    i := i + 1;
  }
  i := 0;
  while(i < 100000) {
    if(0 <= a[i]) {
      b := b[i := 1];
    } else {
      b := b[i := 0];
    }
    i := i + 1;
  }
  var f: int;
  f := 1;
  i := 0;
  while(i < 100000) {
    if(0 <= a[i] && !(b[i] != 0)) {
      f := 0;
    }
    if(a[i] < 0 && !(b[i] != 0)) {
      f := 0;
    }
    i := i + 1;
  }
  assert f != 0;
  c#result := 0;
  return;
}

