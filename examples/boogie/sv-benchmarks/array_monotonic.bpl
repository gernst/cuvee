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
  var i: int;
  var a: [int]int;
  var b: [int]int;
  i := 0;
  while(i < 100000) {
    var nondet_int₁: int;
    assume -2147483648 <= nondet_int₁ && nondet_int₁ < 2147483648;
    a[i] := nondet_int₁;
    if(a[i] == 10) {
      b[i] := 20;
    }
    i := i + 2;
  }
  i := 0;
  while(i < 100000) {
    if(a[i] == 10) {
      assert b[i] == 20;
    }
    i := i + 2;
  }
}

