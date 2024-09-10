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
  var array: [int]int;
  var i: int;
  i := 0;
  while(i < 100000) {
    var nondet_int₁: int;
    assume -2147483648 <= nondet_int₁ && nondet_int₁ < 2147483648;
    array := array[i := nondet_int₁];
    i := i + 1;
  }
  var largest: int := array[0];
  i := 1;
  while(i < 100000) {
    if(largest < array[i]) {
      largest := array[i];
    }
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000) {
    assert array[x] <= largest;
    x := x + 1;
  }
  c#result := 0;
  return;
}

