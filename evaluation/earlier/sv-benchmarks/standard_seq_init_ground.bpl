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
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall x₄: int ::
            ((exists i₃: int ::
                    x₄ == i₃
                    && old(i) <= i₃
                    && i₃ < i)
               ==> (exists i₃: int ::
                      i₃ < 100000
                      && x₄ == i₃
                      && old(i) <= i₃
                      && i₃ < i
                      && a[x₄] == 1 + old(a)[-1 + i₃])))
      && (forall x₄: int ::
            (!((exists i₃: int ::
                    x₄ == i₃
                    && old(i) <= i₃
                    && i₃ < i)
            )
               ==> a[x₄] == old(a[x₄])))
      && (forall i₃: int ::
            (  old(i₃) <= i₃
              && old(i) <= i₃
              && i₃ < i
               ==> i₃ < 100000));
  {
    a := a[i := a[i - 1] + 1];
    i := i + 1;
  }
  var x: int;
  x := 1;
  while(x < 100000)
    decreases 100000 - x;
    invariant true
      && old(x) <= x
      && x <= 100000
      && (forall x₈: int ::
            (  old(x₈) <= x₈
              && old(x) <= x₈
              && x₈ < x
               ==> x₈ < 100000));
  {
    assert a[x - 1] <= a[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

