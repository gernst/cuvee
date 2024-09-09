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
  var i: int;
  i := 1;
  a := a[0 := 7];
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && (forall i₃: int ::
            (  old(i) <= i₃
              && i₃ < i
               ==> i₃ < 100000
                && a[i₃] == 1 + old(a)[-1 + i₃]))
      && (forall i₃: int ::
            (!(  old(i) <= i₃
              && i₃ < i
            )
               ==> a[i₃] == old(a)[i₃]));
  {
    a := a[i := a[i - 1] + 1];
    i := i + 1;
  }
  var x: int;
  x := 1;
  while(x < 100000)
    decreases 100000 - x;
    invariant old(x) <= x
      && (forall x₇: int ::
            (  old(x) <= x₇
              && x₇ < x
               ==> x₇ < 100000));
  {
    assert a[x - 1] <= a[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

