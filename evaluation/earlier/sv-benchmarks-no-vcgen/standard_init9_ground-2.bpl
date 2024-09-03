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
      && 0 <= i
      && i <= 100000
      && (forall x₃: int ::
            ((exists i₂: int ::
                    x₃ == i₂
                    && 0 <= i₂
                    && i₂ < i)
               ==> (exists i₂: int ::
                      i₂ < 100000
                      && x₃ == i₂
                      && 0 <= i₂
                      && i₂ < i
                      && a[x₃] == 42)))
      && (forall x₃: int ::
            (!((exists i₂: int ::
                    x₃ == i₂
                    && 0 <= i₂
                    && i₂ < i)
            )
               ==> a[x₃] == old(a[x₃])))
      && (forall i₂: int ::
            (  0 <= i₂
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
      && 0 <= i
      && i <= 100000
      && (forall x₇: int ::
            ((exists i₆: int ::
                    x₇ == i₆
                    && 0 <= i₆
                    && i₆ < i)
               ==> (exists i₆: int ::
                      i₆ < 100000
                      && x₇ == i₆
                      && 0 <= i₆
                      && i₆ < i
                      && a[x₇] == 43)))
      && (forall x₇: int ::
            (!((exists i₆: int ::
                    x₇ == i₆
                    && 0 <= i₆
                    && i₆ < i)
            )
               ==> a[x₇] == old(a[x₇])))
      && (forall i₆: int ::
            (  0 <= i₆
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
      && 0 <= i
      && i <= 100000
      && (forall x₁₁: int ::
            ((exists i₁₀: int ::
                    x₁₁ == i₁₀
                    && 0 <= i₁₀
                    && i₁₀ < i)
               ==> (exists i₁₀: int ::
                      i₁₀ < 100000
                      && x₁₁ == i₁₀
                      && 0 <= i₁₀
                      && i₁₀ < i
                      && a[x₁₁] == 44)))
      && (forall x₁₁: int ::
            (!((exists i₁₀: int ::
                    x₁₁ == i₁₀
                    && 0 <= i₁₀
                    && i₁₀ < i)
            )
               ==> a[x₁₁] == old(a[x₁₁])))
      && (forall i₁₀: int ::
            (  0 <= i₁₀
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
      && 0 <= i
      && i <= 100000
      && (forall x₁₅: int ::
            ((exists i₁₄: int ::
                    x₁₅ == i₁₄
                    && 0 <= i₁₄
                    && i₁₄ < i)
               ==> (exists i₁₄: int ::
                      i₁₄ < 100000
                      && x₁₅ == i₁₄
                      && 0 <= i₁₄
                      && i₁₄ < i
                      && a[x₁₅] == 45)))
      && (forall x₁₅: int ::
            (!((exists i₁₄: int ::
                    x₁₅ == i₁₄
                    && 0 <= i₁₄
                    && i₁₄ < i)
            )
               ==> a[x₁₅] == old(a[x₁₅])))
      && (forall i₁₄: int ::
            (  0 <= i₁₄
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
      && 0 <= i
      && i <= 100000
      && (forall x₁₉: int ::
            ((exists i₁₈: int ::
                    x₁₉ == i₁₈
                    && 0 <= i₁₈
                    && i₁₈ < i)
               ==> (exists i₁₈: int ::
                      i₁₈ < 100000
                      && x₁₉ == i₁₈
                      && 0 <= i₁₈
                      && i₁₈ < i
                      && a[x₁₉] == 46)))
      && (forall x₁₉: int ::
            (!((exists i₁₈: int ::
                    x₁₉ == i₁₈
                    && 0 <= i₁₈
                    && i₁₈ < i)
            )
               ==> a[x₁₉] == old(a[x₁₉])))
      && (forall i₁₈: int ::
            (  0 <= i₁₈
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
      && 0 <= i
      && i <= 100000
      && (forall x₂₃: int ::
            ((exists i₂₂: int ::
                    x₂₃ == i₂₂
                    && 0 <= i₂₂
                    && i₂₂ < i)
               ==> (exists i₂₂: int ::
                      i₂₂ < 100000
                      && x₂₃ == i₂₂
                      && 0 <= i₂₂
                      && i₂₂ < i
                      && a[x₂₃] == 47)))
      && (forall x₂₃: int ::
            (!((exists i₂₂: int ::
                    x₂₃ == i₂₂
                    && 0 <= i₂₂
                    && i₂₂ < i)
            )
               ==> a[x₂₃] == old(a[x₂₃])))
      && (forall i₂₂: int ::
            (  0 <= i₂₂
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
      && 0 <= i
      && i <= 100000
      && (forall x₂₇: int ::
            ((exists i₂₆: int ::
                    x₂₇ == i₂₆
                    && 0 <= i₂₆
                    && i₂₆ < i)
               ==> (exists i₂₆: int ::
                      i₂₆ < 100000
                      && x₂₇ == i₂₆
                      && 0 <= i₂₆
                      && i₂₆ < i
                      && a[x₂₇] == 48)))
      && (forall x₂₇: int ::
            (!((exists i₂₆: int ::
                    x₂₇ == i₂₆
                    && 0 <= i₂₆
                    && i₂₆ < i)
            )
               ==> a[x₂₇] == old(a[x₂₇])))
      && (forall i₂₆: int ::
            (  0 <= i₂₆
              && i₂₆ < i
               ==> i₂₆ < 100000));
  {
    a := a[i := 48];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && 0 <= i
      && i <= 100000
      && (forall x₃₁: int ::
            ((exists i₃₀: int ::
                    x₃₁ == i₃₀
                    && 0 <= i₃₀
                    && i₃₀ < i)
               ==> (exists i₃₀: int ::
                      i₃₀ < 100000
                      && x₃₁ == i₃₀
                      && 0 <= i₃₀
                      && i₃₀ < i
                      && a[x₃₁] == 49)))
      && (forall x₃₁: int ::
            (!((exists i₃₀: int ::
                    x₃₁ == i₃₀
                    && 0 <= i₃₀
                    && i₃₀ < i)
            )
               ==> a[x₃₁] == old(a[x₃₁])))
      && (forall i₃₀: int ::
            (  0 <= i₃₀
              && i₃₀ < i
               ==> i₃₀ < 100000));
  {
    a := a[i := 49];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && 0 <= i
      && i <= 100000
      && (forall x₃₅: int ::
            ((exists i₃₄: int ::
                    x₃₅ == i₃₄
                    && 0 <= i₃₄
                    && i₃₄ < i)
               ==> (exists i₃₄: int ::
                      i₃₄ < 100000
                      && x₃₅ == i₃₄
                      && 0 <= i₃₄
                      && i₃₄ < i
                      && a[x₃₅] == 50)))
      && (forall x₃₅: int ::
            (!((exists i₃₄: int ::
                    x₃₅ == i₃₄
                    && 0 <= i₃₄
                    && i₃₄ < i)
            )
               ==> a[x₃₅] == old(a[x₃₅])))
      && (forall i₃₄: int ::
            (  0 <= i₃₄
              && i₃₄ < i
               ==> i₃₄ < 100000));
  {
    a := a[i := 50];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant true
      && 0 <= x
      && x <= 100000
      && (forall x₃₉: int ::
            (  0 <= x₃₉
              && x₃₉ < x
               ==> x₃₉ < 100000));
  {
    assert a[x] == 50;
    x := x + 1;
  }
  c#result := 0;
  return;
}

