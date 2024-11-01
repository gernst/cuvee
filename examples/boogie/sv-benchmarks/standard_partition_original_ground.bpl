data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var aa: [int]int;
  var a: int := 0;
  var b: int := 0;
  var c: int := 0;
  var bb: [int]int;
  var cc: [int]int;
  var i: int := 0;
  while(i < 100000) {
    var nondet_int₁: int;
    aa[i] := nondet_int₁;
    i := i + 1;
  }
  while(a < 100000) {
    if(0 <= aa[a]) {
      bb[b] := aa[a];
      b := b + 1;
    } else {
      cc[c] := aa[a];
      c := c + 1;
    }
    a := a + 1;
  }
  var x: int;
  x := 0;
  while(x < b) {
    assert 0 <= bb[x];
    x := x + 1;
  }
  x := 0;
  while(x < c) {
    assert cc[x] < 0;
    x := x + 1;
  }
  c#result := 0;
  return;
}

