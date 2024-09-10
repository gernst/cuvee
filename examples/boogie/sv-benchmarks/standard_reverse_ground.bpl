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
  var i: int;
  i := 0;
  while(i < 100000) {
    var nondet_int₁: int;
    assume -2147483648 <= nondet_int₁ && nondet_int₁ < 2147483648;
    a := a[i := nondet_int₁];
    i := i + 1;
  }
  i := 0;
  while(i < 100000) {
    b := b[i := a[100000 - i - 1]];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000) {
    assert a[x] == b[100000 - x - 1];
    x := x + 1;
  }
  c#result := 0;
  return;
}

