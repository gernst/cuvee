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
    invariant true
      && old(i) <= i
      && i <= 10000000
      && (forall x₂: int ::
            ((exists i₁: int ::
                    x₂ == i₁
                    && old(i) <= i₁
                    && i₁ < i)
               ==> (exists i₁: int ::
                      i₁ < 10000000
                      && x₂ == i₁
                      && old(i) <= i₁
                      && i₁ < i
                      && a[x₂] == 0)))
      && (forall x₂: int ::
            (!((exists i₁: int ::
                    x₂ == i₁
                    && old(i) <= i₁
                    && i₁ < i)
            )
               ==> a[x₂] == old(a[x₂])))
      && (forall i₁: int ::
            (  old(i₁) <= i₁
              && old(i) <= i₁
              && i₁ < i
               ==> i₁ < 10000000));
  {
    a := a[i := 0];
    i := i + 1;
  }
  i := 0;
  while(i < 10000000 / 2)
    decreases 10000000 / 2 - i;
    invariant true
      && old(i) <= i
      && i <= 10000000 / 2
      && (forall x₆: int ::
            ((exists i₅: int ::
                    x₆ == i₅
                    && old(i) <= i₅
                    && i₅ < i)
               ==> (exists i₅: int ::
                      i₅ < 10000000 / 2
                      && x₆ == i₅
                      && old(i) <= i₅
                      && i₅ < i
                      && a[x₆] == 10)))
      && (forall x₆: int ::
            (!((exists i₅: int ::
                    x₆ == i₅
                    && old(i) <= i₅
                    && i₅ < i)
            )
               ==> a[x₆] == old(a[x₆])))
      && (forall i₅: int ::
            (  old(i₅) <= i₅
              && old(i) <= i₅
              && i₅ < i
               ==> i₅ < 10000000 / 2));
  {
    a := a[i := 10];
    i := i + 1;
  }
  i := 0;
  while(i < 10000000 / 2)
    decreases 10000000 / 2 - i;
    invariant true
      && old(i) <= i
      && i <= 10000000 / 2
      && (forall i₉: int ::
            (  old(i₉) <= i₉
              && old(i) <= i₉
              && i₉ < i
               ==> i₉ < 10000000 / 2));
  {
    assert a[i] == 10;
    i := i + 1;
  }
  c#result := 0;
  return;
}

