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
  var max: int := 0;
  var j: int := 0;
  while(j < 100000) {
    var nondet_int₁: int;
    assume -2147483648 <= nondet_int₁ && nondet_int₁ < 2147483648;
    a[j] := nondet_int₁;
    j := j + 1;
  }
  var i: int := 0;
  while(i < 100000) {
    if(max < a[i]) {
      max := a[i];
    }
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000) {
    assert a[x] <= max;
    x := x + 1;
  }
  c#result := 0;
  return;
}

