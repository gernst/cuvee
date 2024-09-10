data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure malloc(size: int) returns (c#result: c#ptr<c#void>);

var SIZE: int;

var MAX: int;

procedure main()
  returns (c#result: int)
  modifies SIZE, MAX;
{
  SIZE := 0;
  MAX := 100000;
  havoc SIZE;
  assume -2147483648 <= SIZE && SIZE < 2147483648;
  if(1 < SIZE && SIZE < MAX) {
    var i: int;
    var tmp: int;
    var a: [int]int;
    var b: [int]int;
    var a_copy: [int]int;
    var b_copy: [int]int;
    i := 0;
    while(i < SIZE) {
      var nondet_int₁: int;
      assume -2147483648 <= nondet_int₁ && nondet_int₁ < 2147483648;
      a_copy[i] := nondet_int₁;
      var nondet_int₂: int;
      assume -2147483648 <= nondet_int₂ && nondet_int₂ < 2147483648;
      b_copy[i] := nondet_int₂;
      i := i + 1;
    }
    i := 0;
    while(i < SIZE) {
      a[i] := a_copy[SIZE - i - 1];
      b[i] := b_copy[SIZE - i - 1];
      i := i + 1;
    }
    i := 0;
    while(i < SIZE) {
      tmp := a[i];
      a[i] := b[i];
      b[i] := tmp;
      i := i + 1;
    }
    i := 0;
    while(i < SIZE) {
      tmp := a[i];
      a[i] := b[i];
      b[i] := tmp;
      i := i + 1;
    }
    i := 0;
    while(i < SIZE) {
      assert a[i] == a_copy[SIZE - i - 1];
      i := i + 1;
    }
  }
  c#result := 1;
  return;
}

