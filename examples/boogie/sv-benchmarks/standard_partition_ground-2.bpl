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
  var i: int;
  i := 0;
  while(i < 100000) {
    var __VERIFIER_nondet_int₂₄₇: int;
    __VERIFIER_nondet_int₂₄₇ := call __VERIFIER_nondet_int();
    aa := aa[i := __VERIFIER_nondet_int₂₄₇];
    var x₂₄₈: int := i;
    i := i + 1;
  }
  while(a < 100000) {
    if(0 <= aa[a]) {
      bb := bb[b := aa[a]];
      b := b + 1;
    }
    a := a + 1;
  }
  a := 0;
  while(a < 100000) {
    if(aa[a] < 0) {
      cc := cc[c := aa[a]];
      c := c + 1;
    }
    a := a + 1;
  }
  var x: int;
  x := 0;
  while(x < b) {
    assert 0 <= bb[x];
    var x₂₄₉: int := x;
    x := x + 1;
  }
  c#result := 0;
  return;
}

