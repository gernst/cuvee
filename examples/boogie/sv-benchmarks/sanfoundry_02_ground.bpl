data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var array: [int]int;
  var i: int;
  var largest1: int;
  var largest2: int;
  var temp: int;
  i := 0;
  while(i < 100000) {
    var __VERIFIER_nondet_int₁₅₀: int;
    array := array[i := __VERIFIER_nondet_int₁₅₀];
    i := i + 1;
  }
  largest1 := array[0];
  largest2 := array[1];
  if(largest1 < largest2) {
    temp := largest1;
    largest1 := largest2;
    largest2 := temp;
  }
  i := 2;
  while(i < 100000) {
    if(largest1 <= array[i]) {
      largest2 := largest1;
      largest1 := array[i];
    } else {
      if(largest2 < array[i]) {
        largest2 := array[i];
      }
    }
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000) {
    assert array[x] <= largest1;
    x := x + 1;
  }
  x := 0;
  while(x < 100000) {
    assert array[x] <= largest2 || array[x] == largest1;
    x := x + 1;
  }
  c#result := 0;
  return;
}

