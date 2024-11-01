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
  var m: int := 1000;
  var n: int := 1500;
  var q: int;
  var s: int;
  var A: [int][int]int;
  var C: int;
  havoc q;
  havoc s;
  i := 0;
  j := 0;
  assume q < m;
  assume s < n;
  while(i < q) {
    j := 0;
    while(j < s) {
      A[i][j] := i + j + C;
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  j := 0;
  while(i < q) {
    j := 0;
    while(j < s) {
      assert A[i][j] == i + j + C;
      j := j + 1;
    }
    i := i + 1;
  }
  c#result := 0;
  return;
}

