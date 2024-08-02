data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var i: int;
  var a: [int]int;
  i := 0;
  while(i < 100000) {
    a := a[i := 10];
    i := i + 1;
  }
  i := 0;
  while(i < 100000) {
    assert a[i] == 10;
    if(i + 1 != 15000) {
      a := a[i + 1 := 20];
    }
    i := i + 1;
  }
  c#result := 0;
  return;
}

