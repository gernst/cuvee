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
                && a[2 + 3 * i₃] == 0
                && (1 + 3 * i₃ != 2 + 3 * i₃
                   ==> a[1 + 3 * i₃] == 0)
                && (  3 * i₃ != 1 + 3 * i₃
                  && 3 * i₃ != 2 + 3 * i₃
                   ==> a[3 * i₃] == 0)));
  {
    a := a[3 * i := 0];
    a := a[3 * i + 1 := 0];
    a := a[3 * i + 2 := 0];
    i := i + 1;
  }
  i := 0;
  while(i <= 3 * N)
    decreases 3 * N + 1 - i;
    invariant old(i) <= i
      && (forall i₆: int ::
            (  old(i) <= i₆
              && i₆ < i
               ==> i₆ <= 3 * N));
  {
    assert 0 <= a[i];
    i := i + 1;
  }
  c#result := 0;
  return;
}

