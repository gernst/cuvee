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
  var aa: [int]int;
  var a: int;
  a := 0;
  var b: int;
  b := 0;
  var c: int;
  c := 0;
  var bb: [int]int;
  var cc: [int]int;
  while(a < 100000) {
    var __VERIFIER_nondet_int₁₆₄: int;
    __VERIFIER_nondet_int₁₆₄ := call __VERIFIER_nondet_int();
    aa := aa[a := __VERIFIER_nondet_int₁₆₄];
    if(0 <= aa[a]) {
      bb := bb[b := aa[a]];
      b := b + 1;
    }
    a := a + 1;
  }
  a := 0;
  while(a < 100000) {
    if(0 <= aa[a]) {
      cc := cc[c := aa[a]];
      c := c + 1;
    }
    a := a + 1;
  }
  var x: int;
  x := 0;
  while(x < b) {
    assert 0 <= bb[x];
    var x₁₆₅: int := x;
    x := x + 1;
  }
  x := 0;
  while(x < c) {
    assert cc[x] < 0;
    var x₁₆₆: int := x;
    x := x + 1;
  }
  c#result := 0;
  return;
}

