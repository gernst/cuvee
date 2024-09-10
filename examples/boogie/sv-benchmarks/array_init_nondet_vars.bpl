data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var i: int;
  var j: int;
  assume -2147483648 <= j && j < 2147483648;
  var n: int;
  assume -2147483648 <= n && n < 2147483648;
  assume n < 100000;
  var a: [int]int;
  assume 0 < j && j < 10000;
  i := 1;
  while(i < n) {
    var k: int;
    assume -2147483648 <= k && k < 2147483648;
    assume 0 < k && k < 10000;
    a := a[i := i + j + k];
    i := i + 1;
  }
  i := 1;
  while(i < n) {
    assert i + 2 <= a[i];
    i := i + 1;
  }
  c#result := 0;
  return;
}

