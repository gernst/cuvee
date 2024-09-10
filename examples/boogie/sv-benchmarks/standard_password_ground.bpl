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
  var password: [int]int;
  var guess: [int]int;
  var i: int;
  var result: int := 1;
  i := 0;
  while(i < 100000) {
    var nondet_int₁: int;
    assume -2147483648 <= nondet_int₁ && nondet_int₁ < 2147483648;
    password := password[i := nondet_int₁];
    var nondet_int₂: int;
    assume -2147483648 <= nondet_int₂ && nondet_int₂ < 2147483648;
    guess := guess[i := nondet_int₂];
    i := i + 1;
  }
  i := 0;
  while(i < 100000) {
    if(password[i] != guess[i]) {
      result := 0;
    }
    i := i + 1;
  }
  if(result != 0) {
    var x: int;
    x := 0;
    while(x < 100000) {
      assert password[x] == guess[x];
      x := x + 1;
    }
  }
  c#result := 0;
  return;
}

