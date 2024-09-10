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
  var A: [int][int][int]int;
  var B: [int][int][int]int;
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
  while(i < n) {
    j := 0;
    k := 0;
    while(j < n) {
      k := 0;
      while(k < n) {
        A := A[i := A[i][j := A[i][j][k := B[n - i - 1][n - j - 1][n - k - 1]]]];
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
        assert A[i][j][k] == B[n - i - 1][n - j - 1][n - k - 1];
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  c#result := 0;
  return;
}

