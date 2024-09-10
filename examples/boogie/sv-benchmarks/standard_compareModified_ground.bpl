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
  var a: [int]int;
  var b: [int]int;
  var i: int := 0;
  var c: [int]int;
  var rv: int := 1;
  var j: int := 0;
  while(j < 100000) {
    var nondet_int₁: int;
    assume -2147483648 <= nondet_int₁ && nondet_int₁ < 2147483648;
    a[j] := nondet_int₁;
    var nondet_int₂: int;
    assume -2147483648 <= nondet_int₂ && nondet_int₂ < 2147483648;
    b[j] := nondet_int₂;
    j := j + 1;
  }
  while(i < 100000) {
    if(a[i] != b[i]) {
      rv := 0;
    }
    c[i] := a[i];
    i := i + 1;
  }
  var x: int;
  if(rv != 0) {
    x := 0;
    while(x < 100000) {
      assert a[x] == b[x];
      x := x + 1;
    }
  }
  x := 0;
  while(x < 100000) {
    assert a[x] == c[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

