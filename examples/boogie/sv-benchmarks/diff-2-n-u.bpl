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
  var B: [int][int]int;
  var C: [int][int]int;
  i := 0;
  j := 0;
  while(i < m) {
    j := 0;
    while(j < n) {
      var nondet_uint₁: int;
      A[i][j] := nondet_uint₁;
      var nondet_uint₂: int;
      B[i][j] := nondet_uint₂;
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  j := 0;
  while(i < m) {
    j := 0;
    while(j < n) {
      var nondet_uint₃: int;
      A[i][j] := nondet_uint₃;
      var nondet_uint₄: int;
      B[i][j] := nondet_uint₄;
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  j := 0;
  while(i < m) {
    j := 0;
    while(j < n) {
      C[i][j] := A[i][j] - B[i][j];
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  j := 0;
  while(i < m) {
    j := 0;
    while(j < n) {
      assert C[i][j] == A[i][j] - B[i][j];
      j := j + 1;
    }
    i := i + 1;
  }
  c#result := 0;
  return;
}

