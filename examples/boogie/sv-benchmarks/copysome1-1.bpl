data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

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
    var __VERIFIER_nondet_int₇₉₅: int;
    a1 := a1[i := __VERIFIER_nondet_int₇₉₅];
    var __VERIFIER_nondet_int₇₉₆: int;
    a2 := a2[i := __VERIFIER_nondet_int₇₉₆];
    i := i + 1;
  }
  i := 0;
  while(i < 200000) {
    if(i != z) {
      a2 := a2[i := a1[i]];
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

