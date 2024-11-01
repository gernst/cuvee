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
  N := 100000;
  var i: int;
  var j: int := 0;
  var k: int := 0;
  var a: [int]int;
  i := 0;
  while(i < N) {
    var x: int;
    if(x != 0) {
      break;
    }
    a[i] := j;
    j := j + i;
    k := k - i;
    i := i + 1;
  }
  var l: int := 1;
  while(l < i) {
    assert k <= a[l];
    l := l + 1;
  }
  c#result := 0;
  return;
}

