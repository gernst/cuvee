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
  var k: int := 0;
  var a: [int]int;
  var R: int;
  assume 0 < R;
  i := 0;
  while(i < N) {
    a[i] := i + 1;
    if(N / 2 < i && k < 1) {
      a[i] := i % R;
    }
    if(a[i] == 0) {
      k := k + 1;
    }
    i := i + 1;
  }
  i := 0;
  while(i < N) {
    if(a[i] == 0) {
      j := j + 1;
    }
    assert j < 2;
    i := i + 1;
  }
  c#result := 0;
  return;
}

