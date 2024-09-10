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
  var a1: [int]int;
  var a2: [int]int;
  var i: int;
  var z: int;
  z := 150000;
  i := 0;
  while(i < 200000) {
    var nondet_int₁: int;
    a1[i] := nondet_int₁;
    var nondet_int₂: int;
    a2[i] := nondet_int₂;
    i := i + 1;
  }
  i := 0;
  while(i < 200000) {
    if(i != z) {
      a2[i] := a1[i];
    }
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 200000) {
    if(x != z) {
      assert a1[x] == a2[x];
    }
    x := x + 1;
  }
  c#result := 0;
  return;
}

