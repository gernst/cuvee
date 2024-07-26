data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure __VERIFIER_nondet_int() returns (c#result: int);
  modifies c#heap;

procedure main()
  returns (c#result: int)
  modifies c#heap;
{
  var password: [int]int;
  var guess: [int]int;
  var i: int;
  var result: int;
  result := 1;
  i := 0;
  while(i < 100000) {
    var __VERIFIER_nondet_int₂₀₆: int;
    __VERIFIER_nondet_int₂₀₆ := call __VERIFIER_nondet_int();
    password := password[i := __VERIFIER_nondet_int₂₀₆];
    var __VERIFIER_nondet_int₂₀₇: int;
    __VERIFIER_nondet_int₂₀₇ := call __VERIFIER_nondet_int();
    guess := guess[i := __VERIFIER_nondet_int₂₀₇];
    var x₂₀₈: int := i;
    i := i + 1;
  }
  i := 0;
  while(i < 100000) {
    if(password[i] != guess[i]) {
      result := 0;
    }
    var x₂₀₉: int := i;
    i := i + 1;
  }
  if(result != 0) {
    var x: int;
    x := 0;
    while(x < 100000) {
      assert password[x] == guess[x];
      var x₂₁₀: int := x;
      x := x + 1;
    }
  }
  c#result := 0;
  return;
}

