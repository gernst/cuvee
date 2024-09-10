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
  N := 1000;
  var i: int;
  var j: int := 0;
  var k: int := 0;
  var a: [int]int;
  var lim: int;
  assume -2147483648 <= lim && lim < 2147483648;
  var R: int := 5;
  assume 0 < lim && lim < N / R;
  i := 0;
  while(i < N) {
    a[i] := i + 1;
    if(N / 2 < i && k < lim) {
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
    assert j < N / 2 * R;
    i := i + 1;
  }
  c#result := 0;
  return;
}

