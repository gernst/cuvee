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
  var m: int := 1000;
  var n: int := 1500;
  var p: int := 1800;
  var A: [int][int][int]int;
  var B: [int][int][int]int;
  i := 0;
  j := 0;
  k := 0;
  while(i < m) {
    j := 0;
    k := 0;
    while(j < n) {
      k := 0;
      while(k < p) {
        var nondet_int₁: int;
        B[i][j][k] := nondet_int₁;
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  j := 0;
  k := 0;
  while(i < m) {
    j := 0;
    k := 0;
    while(j < n) {
      k := 0;
      while(k < p) {
        A[i][j][k] := B[i][j][k];
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  j := 0;
  k := 0;
  while(i < m) {
    j := 0;
    k := 0;
    while(j < n) {
      k := 0;
      while(k < p) {
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

