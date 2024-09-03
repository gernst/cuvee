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
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant true
      && 0 <= x
      && x <= 100000
      && (forall x₂₃: int ::
            (  0 <= x₂₃
              && x₂₃ < x
               ==> x₂₃ < 100000));
  {
    assert a[x] == 45;
    x := x + 1;
  }
  c#result := 0;
  return;
}

