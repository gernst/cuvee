data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var a: [int]int;

var i: int;

procedure main()
  returns (c#result: int)
  modifies a, i;
{
  i := 0;
  while(i < 10000000)
    decreases 10000000 - i;
    invariant old(i) <= i
      && (forall i₁: int ::
            (  old(i) <= i₁
              && i₁ < i
               ==> i₁ < 10000000
                && a[i₁] == 0))
      && (forall i₁: int ::
            (!(  old(i) <= i₁
              && i₁ < i
            )
               ==> a[i₁] == old(a)[i₁]));
  {
    a := a[i := 0];
    i := i + 1;
  }
  i := 0;
  while(i < 10000000 / 2)
    decreases 10000000 / 2 - i;
    invariant old(i) <= i
      && (forall i₄: int ::
            (  old(i) <= i₄
              && i₄ < i
               ==> i₄ < 10000000 / 2
                && a[i₄] == 10))
      && (forall i₄: int ::
            (!(  old(i) <= i₄
              && i₄ < i
            )
               ==> a[i₄] == old(a)[i₄]));
  {
    a := a[i := 10];
    i := i + 1;
  }
  i := 0;
  while(i < 10000000 / 2)
    decreases 10000000 / 2 - i;
    invariant old(i) <= i
      && (forall i₇: int ::
            (  old(i) <= i₇
              && i₇ < i
               ==> i₇ < 10000000 / 2));
  {
    assert a[i] == 10;
    i := i + 1;
  }
  c#result := 0;
  return;
}

