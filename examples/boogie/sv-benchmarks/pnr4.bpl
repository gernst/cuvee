data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure malloc(size: int) returns (c#result: c#ptr<c#void>);

procedure ReadFromPort()
  returns (c#result: int)
{
  var x: int;
  assume -2147483648 <= x && x < 2147483648;
  c#result := x;
  return;
}

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
    var value: int;
    var a: [int]int;
    var DEFAULTVAL: int := 0;
    var FIXEDVAL: int := 10;
    if(SIZE % 4 != 0) {
      c#result := 1;
      return;
    }
    assume SIZE % 4 == 0;
    i := 1;
    while(i <= SIZE / 4) {
      var ReadFromPort₁: int;
      ReadFromPort₁ := call ReadFromPort();
      value := ReadFromPort₁;
      if(value != DEFAULTVAL) {
        a := a[i * 4 - 4 := value];
      } else {
        a := a[i * 4 - 4 := FIXEDVAL];
      }
      var ReadFromPort₂: int;
      ReadFromPort₂ := call ReadFromPort();
      value := ReadFromPort₂;
      if(value != DEFAULTVAL) {
        a := a[i * 4 - 3 := value];
      } else {
        a := a[i * 4 - 3 := FIXEDVAL];
      }
      var ReadFromPort₃: int;
      ReadFromPort₃ := call ReadFromPort();
      value := ReadFromPort₃;
      if(value != DEFAULTVAL) {
        a := a[i * 4 - 2 := value];
      } else {
        a := a[i * 4 - 2 := FIXEDVAL];
      }
      var ReadFromPort₄: int;
      ReadFromPort₄ := call ReadFromPort();
      value := ReadFromPort₄;
      if(value != DEFAULTVAL) {
        a := a[i * 4 - 1 := value];
      } else {
        a := a[i * 4 - 1 := FIXEDVAL];
      }
      i := i + 1;
    }
    i := 0;
    while(i < SIZE) {
      assert a[i] != DEFAULTVAL;
      i := i + 1;
    }
  }
  c#result := 1;
  return;
}

