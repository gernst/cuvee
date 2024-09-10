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
  var marker: int;
  var pos: int;
  var i: int := 0;
  while(i < 100000) {
    var nondet_int₁: int;
    a[i] := nondet_int₁;
    i := i + 1;
  }
  if(0 <= pos && pos < 100000) {
    a[pos] := marker;
    var i: int := 0;
    while(a[i] != marker) {
      i := i + 1;
    }
    assert i <= pos;
  }
  c#result := 0;
  return;
}

