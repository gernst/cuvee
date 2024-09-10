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
  var n: int := 1000;
  var p: int := 500;
  var A: [int][int][int]int;
  var B: [int][int][int]int;
  assume p < n;
  i := 0;
  j := 0;
  k := 0;
  while(i < n) {
    j := 0;
    k := 0;
    while(j < n) {
      k := 0;
      while(k < n) {
        var nondet_int₁: int;
        assume -2147483648 <= nondet_int₁ && nondet_int₁ < 2147483648;
        B := B[i := B[i][j := B[i][j][k := nondet_int₁]]];
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  j := 0;
  k := 0;
  while(i < p) {
    j := 0;
    k := 0;
    while(j < p) {
      k := 0;
      while(k < p) {
        A := A[i := A[i][j := A[i][j][k := B[i][j][k]]]];
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  i := p;
  while(i < n) {
    j := p;
    while(j < n) {
      k := p;
      while(k < n) {
        A := A[i := A[i][j := A[i][j][k := B[i][j][k]]]];
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  j := 0;
  k := 0;
  while(i < n) {
    j := 0;
    k := 0;
    while(j < n) {
      k := 0;
      while(k < n) {
        assert A[i][j][k] == B[i][j][k];
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  c#result := 0;
  return;
}

