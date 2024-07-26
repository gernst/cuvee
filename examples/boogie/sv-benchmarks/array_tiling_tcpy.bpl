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
  var __VERIFIER_nondet_int₁₀₈₉: int;
  __VERIFIER_nondet_int₁₀₈₉ := call __VERIFIER_nondet_int();
  var S: int;
  S := __VERIFIER_nondet_int₁₀₈₉;
  assume 1 < S;
  assume S < 1073741823;
  var i: int;
  var a: [int]int;
  var acopy: [int]int;
  i := 0;
  while(i < S) {
    acopy := acopy[2 * S - i + 1 := a[2 * S - i + 1]];
    acopy := acopy[i := a[i]];
    var x₁₀₉₀: int := i;
    i := i + 1;
  }
  i := 0;
  while(i < 2 * S) {
    assert acopy[i] == a[i];
    var x₁₀₉₁: int := i;
    i := i + 1;
  }
  c#result := 0;
  return;
}

