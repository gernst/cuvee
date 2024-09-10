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
  var A: [int][int]int;
  var C: int;
  assume -2147483648 <= C && C < 2147483648;
  i := 0;
  j := 0;
  while(i < m) {
    j := 0;
    while(j < n) {
      A := A[i := A[i][j := C]];
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  j := 0;
  while(i < m) {
    j := 0;
    while(j < n) {
      assert A[i][j] == C;
      j := j + 1;
    }
    i := i + 1;
  }
  c#result := 0;
  return;
}

