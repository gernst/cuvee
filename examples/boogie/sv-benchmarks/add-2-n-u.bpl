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
      assume 0 <= nondet_uint₁ && nondet_uint₁ < 4294967296;
      A := A[i := A[i][j := nondet_uint₁]];
      var nondet_uint₂: int;
      assume 0 <= nondet_uint₂ && nondet_uint₂ < 4294967296;
      B := B[i := B[i][j := nondet_uint₂]];
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  j := 0;
  while(i < m) {
    j := 0;
    while(j < n) {
      C := C[i := C[i][j := A[i][j] + B[i][j]]];
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  j := 0;
  while(i < m) {
    j := 0;
    while(j < n) {
      assert C[i][j] == A[i][j] + B[i][j];
      j := j + 1;
    }
    i := i + 1;
  }
  c#result := 0;
  return;
}

