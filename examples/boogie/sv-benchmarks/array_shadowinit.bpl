data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var N: int;

procedure main()
  returns (c#result: int)
  modifies N;
{
  havoc N;
  if(0 < N) {
    var i: int;
    var k: int;
    var a: [int]int;
    i := 0;
    k := 0;
    while(i < N) {
      a := a[k := k];
      i := i + 1;
      k := k + 1;
    }
    i := 0;
    while(i < N) {
      assert a[i] == i;
      i := i + 1;
    }
  }
  c#result := 0;
  return;
}

