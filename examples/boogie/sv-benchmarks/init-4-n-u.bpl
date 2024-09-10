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
  var k: int;
  var l: int;
  var m: int := 1000;
  var n: int := 1500;
  var p: int := 1800;
  var q: int := 2000;
  var A: [int][int][int][int]int;
  var C: int;
  i := 0;
  j := 0;
  k := 0;
  l := 0;
  while(i < m) {
    j := 0;
    k := 0;
    l := 0;
    while(j < n) {
      k := 0;
      l := 0;
      while(k < p) {
        l := 0;
        while(l < q) {
          A[i][j][k][l] := C;
          l := l + 1;
        }
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  j := 0;
  k := 0;
  l := 0;
  while(i < m) {
    j := 0;
    k := 0;
    l := 0;
    while(j < n) {
      k := 0;
      l := 0;
      while(k < p) {
        l := 0;
        while(l < q) {
          assert A[i][j][k][l] == C;
          l := l + 1;
        }
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  c#result := 0;
  return;
}

