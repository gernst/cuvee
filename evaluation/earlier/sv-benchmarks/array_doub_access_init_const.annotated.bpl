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
  var N: int := 100000;
  var a: [int]int;
  i := 0;
  while(i <= N)
    decreases N + 1 - i;
    invariant old(i) <= i
      && (forall i₃: int ::
            (  old(i) <= i₃
              && i₃ < i
               ==> i₃ <= N
                && a[1 + 2 * i₃] == 0
                && (2 * i₃ != 1 + 2 * i₃
                   ==> a[2 * i₃] == 0)));
  {
    a := a[2 * i := 0];
    a := a[2 * i + 1 := 0];
    i := i + 1;
  }
  i := 0;
  while(i <= 2 * N)
    decreases 2 * N + 1 - i;
    invariant old(i) <= i
      && (forall i₆: int ::
            (  old(i) <= i₆
              && i₆ < i
               ==> i₆ <= 2 * N));
  {
    assert 0 <= a[i];
    i := i + 1;
  }
  c#result := 0;
  return;
}

