data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var password: [int]int;
  var guess: [int]int;
  var i: int;
  var result: int;
  result := 1;
  i := 0;
  while(i < 100000) {
    var __VERIFIER_nondet_int₂₀₆: int;
    password := password[i := __VERIFIER_nondet_int₂₀₆];
    var __VERIFIER_nondet_int₂₀₇: int;
    guess := guess[i := __VERIFIER_nondet_int₂₀₇];
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

