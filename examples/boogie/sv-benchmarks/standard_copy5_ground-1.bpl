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
  var a3: [int]int;
  var a4: [int]int;
  var a5: [int]int;
  var a6: [int]int;
  var a: int;
  a := 0;
  while(a < 100000) {
    var nondet_int₁: int;
    assume -2147483648 <= nondet_int₁ && nondet_int₁ < 2147483648;
    a1[a] := nondet_int₁;
    a := a + 1;
  }
  var i: int;
  i := 0;
  while(i < 100000) {
    a2[i] := a1[i];
    i := i + 1;
  }
  i := 0;
  while(i < 100000) {
    a3[i] := a2[i];
    i := i + 1;
  }
  i := 0;
  while(i < 100000) {
    a4[i] := a3[i];
    i := i + 1;
  }
  i := 0;
  while(i < 100000) {
    a5[i] := a4[i];
    i := i + 1;
  }
  i := 0;
  while(i < 100000) {
    a6[i] := a5[i];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000) {
    assert a1[x] == a6[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

