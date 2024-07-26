data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
  modifies c#heap;
{
  var i: int;
  var a: [int]int;
  i := 0;
  while(i < 100000) {
    a := a[i := 10];
    var x₃₇₇: int := i;
    i := i + 1;
  }
  i := 0;
  while(i < 100000) {
    assert a[i] == 10;
    if(i + 1 != 15000) {
      a := a[i + 1 := 20];
    }
    var x₃₇₈: int := i;
    i := i + 1;
  }
  c#result := 0;
  return;
}

