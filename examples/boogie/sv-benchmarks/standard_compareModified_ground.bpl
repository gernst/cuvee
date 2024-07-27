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
  var c: [int]int;
  var rv: int;
  rv := 1;
  var j: int;
  j := 0;
  while(j < 100000) {
    var __VERIFIER_nondet_int₂₆₄: int;
    __VERIFIER_nondet_int₂₆₄ := call __VERIFIER_nondet_int();
    a := a[j := __VERIFIER_nondet_int₂₆₄];
    var __VERIFIER_nondet_int₂₆₅: int;
    __VERIFIER_nondet_int₂₆₅ := call __VERIFIER_nondet_int();
    b := b[j := __VERIFIER_nondet_int₂₆₅];
    var x₂₆₆: int := j;
    j := j + 1;
  }
  while(i < 100000) {
    if(a[i] != b[i]) {
      rv := 0;
    }
    c := c[i := a[i]];
    i := i + 1;
  }
  var x: int;
  if(rv != 0) {
    x := 0;
    while(x < 100000) {
      assert a[x] == b[x];
      var x₂₆₇: int := x;
      x := x + 1;
    }
  }
  x := 0;
  while(x < 100000) {
    assert a[x] == c[x];
    var x₂₆₈: int := x;
    x := x + 1;
  }
  c#result := 0;
  return;
}

