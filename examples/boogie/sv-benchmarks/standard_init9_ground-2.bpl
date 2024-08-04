data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var a: [int]int;
  var i: int := 0;
  while(i < 100000) {
    a := a[i := 42];
    i := i + 1;
  }
  i := 0;
  while(i < 100000) {
    a := a[i := 43];
    i := i + 1;
  }
  i := 0;
  while(i < 100000) {
    a := a[i := 44];
    i := i + 1;
  }
  i := 0;
  while(i < 100000) {
    a := a[i := 45];
    i := i + 1;
  }
  i := 0;
  while(i < 100000) {
    a := a[i := 46];
    i := i + 1;
  }
  i := 0;
  while(i < 100000) {
    a := a[i := 47];
    i := i + 1;
  }
  i := 0;
  while(i < 100000) {
    a := a[i := 48];
    i := i + 1;
  }
  i := 0;
  while(i < 100000) {
    a := a[i := 49];
    i := i + 1;
  }
  i := 0;
  while(i < 100000) {
    a := a[i := 50];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000) {
    assert a[x] == 50;
    x := x + 1;
  }
  c#result := 0;
  return;
}

