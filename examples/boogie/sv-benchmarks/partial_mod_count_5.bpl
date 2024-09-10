data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var N: int;

procedure main()
  returns (c#result: int)
  modifies N;
{
  N := 1000000;
  var i: int;
  var j: int := 0;
  var a: [int]int;
  var R: int := 5;
  i := 0;
  while(i < N) {
    a := a[i := i + 1];
    if(N / 2 < i) {
      a := a[i := i % R];
    }
    i := i + 1;
  }
  i := 0;
  while(i < N) {
    if(a[i] == 0) {
      j := j + 1;
    }
    assert j < N / 10;
    i := i + 1;
  }
  c#result := 0;
  return;
}

