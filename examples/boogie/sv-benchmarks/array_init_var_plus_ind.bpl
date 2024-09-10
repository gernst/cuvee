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
  var a: [int]int;
  i := 0;
  while(i < N) {
    var x: int;
    assume -2147483648 <= x && x < 2147483648;
    if(x != 0) {
      break;
    }
    a := a[i := j];
    j := j + i;
    i := i + 1;
  }
  var k: int := 1;
  while(k < i) {
    assert 0 <= a[k];
    k := k + 1;
  }
  c#result := 0;
  return;
}

