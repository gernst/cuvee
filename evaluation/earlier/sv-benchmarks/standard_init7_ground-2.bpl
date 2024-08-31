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
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall x₃: int ::
            ((exists i₂: int ::
                    x₃ == i₂
                    && old(i) <= i₂
                    && i₂ < i)
               ==> (exists i₂: int ::
                      i₂ < 100000
                      && x₃ == i₂
                      && old(i) <= i₂
                      && i₂ < i
                      && a[x₃] == 42)))
      && (forall x₃: int ::
            (!((exists i₂: int ::
                    x₃ == i₂
                    && old(i) <= i₂
                    && i₂ < i)
            )
               ==> a[x₃] == old(a[x₃])))
      && (forall i₂: int ::
            (  old(i₂) <= i₂
              && old(i) <= i₂
              && i₂ < i
               ==> i₂ < 100000));
  {
    a := a[i := 42];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall x₇: int ::
            ((exists i₆: int ::
                    x₇ == i₆
                    && old(i) <= i₆
                    && i₆ < i)
               ==> (exists i₆: int ::
                      i₆ < 100000
                      && x₇ == i₆
                      && old(i) <= i₆
                      && i₆ < i
                      && a[x₇] == 43)))
      && (forall x₇: int ::
            (!((exists i₆: int ::
                    x₇ == i₆
                    && old(i) <= i₆
                    && i₆ < i)
            )
               ==> a[x₇] == old(a[x₇])))
      && (forall i₆: int ::
            (  old(i₆) <= i₆
              && old(i) <= i₆
              && i₆ < i
               ==> i₆ < 100000));
  {
    a := a[i := 43];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall x₁₁: int ::
            ((exists i₁₀: int ::
                    x₁₁ == i₁₀
                    && old(i) <= i₁₀
                    && i₁₀ < i)
               ==> (exists i₁₀: int ::
                      i₁₀ < 100000
                      && x₁₁ == i₁₀
                      && old(i) <= i₁₀
                      && i₁₀ < i
                      && a[x₁₁] == 44)))
      && (forall x₁₁: int ::
            (!((exists i₁₀: int ::
                    x₁₁ == i₁₀
                    && old(i) <= i₁₀
                    && i₁₀ < i)
            )
               ==> a[x₁₁] == old(a[x₁₁])))
      && (forall i₁₀: int ::
            (  old(i₁₀) <= i₁₀
              && old(i) <= i₁₀
              && i₁₀ < i
               ==> i₁₀ < 100000));
  {
    a := a[i := 44];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall x₁₅: int ::
            ((exists i₁₄: int ::
                    x₁₅ == i₁₄
                    && old(i) <= i₁₄
                    && i₁₄ < i)
               ==> (exists i₁₄: int ::
                      i₁₄ < 100000
                      && x₁₅ == i₁₄
                      && old(i) <= i₁₄
                      && i₁₄ < i
                      && a[x₁₅] == 45)))
      && (forall x₁₅: int ::
            (!((exists i₁₄: int ::
                    x₁₅ == i₁₄
                    && old(i) <= i₁₄
                    && i₁₄ < i)
            )
               ==> a[x₁₅] == old(a[x₁₅])))
      && (forall i₁₄: int ::
            (  old(i₁₄) <= i₁₄
              && old(i) <= i₁₄
              && i₁₄ < i
               ==> i₁₄ < 100000));
  {
    a := a[i := 45];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall x₁₉: int ::
            ((exists i₁₈: int ::
                    x₁₉ == i₁₈
                    && old(i) <= i₁₈
                    && i₁₈ < i)
               ==> (exists i₁₈: int ::
                      i₁₈ < 100000
                      && x₁₉ == i₁₈
                      && old(i) <= i₁₈
                      && i₁₈ < i
                      && a[x₁₉] == 46)))
      && (forall x₁₉: int ::
            (!((exists i₁₈: int ::
                    x₁₉ == i₁₈
                    && old(i) <= i₁₈
                    && i₁₈ < i)
            )
               ==> a[x₁₉] == old(a[x₁₉])))
      && (forall i₁₈: int ::
            (  old(i₁₈) <= i₁₈
              && old(i) <= i₁₈
              && i₁₈ < i
               ==> i₁₈ < 100000));
  {
    a := a[i := 46];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall x₂₃: int ::
            ((exists i₂₂: int ::
                    x₂₃ == i₂₂
                    && old(i) <= i₂₂
                    && i₂₂ < i)
               ==> (exists i₂₂: int ::
                      i₂₂ < 100000
                      && x₂₃ == i₂₂
                      && old(i) <= i₂₂
                      && i₂₂ < i
                      && a[x₂₃] == 47)))
      && (forall x₂₃: int ::
            (!((exists i₂₂: int ::
                    x₂₃ == i₂₂
                    && old(i) <= i₂₂
                    && i₂₂ < i)
            )
               ==> a[x₂₃] == old(a[x₂₃])))
      && (forall i₂₂: int ::
            (  old(i₂₂) <= i₂₂
              && old(i) <= i₂₂
              && i₂₂ < i
               ==> i₂₂ < 100000));
  {
    a := a[i := 47];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall x₂₇: int ::
            ((exists i₂₆: int ::
                    x₂₇ == i₂₆
                    && old(i) <= i₂₆
                    && i₂₆ < i)
               ==> (exists i₂₆: int ::
                      i₂₆ < 100000
                      && x₂₇ == i₂₆
                      && old(i) <= i₂₆
                      && i₂₆ < i
                      && a[x₂₇] == 48)))
      && (forall x₂₇: int ::
            (!((exists i₂₆: int ::
                    x₂₇ == i₂₆
                    && old(i) <= i₂₆
                    && i₂₆ < i)
            )
               ==> a[x₂₇] == old(a[x₂₇])))
      && (forall i₂₆: int ::
            (  old(i₂₆) <= i₂₆
              && old(i) <= i₂₆
              && i₂₆ < i
               ==> i₂₆ < 100000));
  {
    a := a[i := 48];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant true
      && old(x) <= x
      && x <= 100000
      && (forall x₃₁: int ::
            (  old(x₃₁) <= x₃₁
              && old(x) <= x₃₁
              && x₃₁ < x
               ==> x₃₁ < 100000));
  {
    assert a[x] == 48;
    x := x + 1;
  }
  c#result := 0;
  return;
}

