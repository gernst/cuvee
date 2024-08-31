data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var SIZE: int;

procedure main()
  returns (c#result: int)
  modifies SIZE;
{
  havoc SIZE;
  if(1 < SIZE) {
    var i: int;
    var a: [int]int;
    var sum: int := 0;
    {
      var i: int := 0;
      while(i < SIZE)
        decreases SIZE - i;
        invariant true
          && old(i) <= i
          && i <= SIZE
          && (forall x₆: int ::
                ((exists i₅: int ::
                        x₆ == i₅
                        && old(i) <= i₅
                        && i₅ < i)
                   ==> (exists __VERIFIER_nondet_short₁₄: int, i₅: int ::
                          i₅ < SIZE
                          && x₆ == i₅
                          && old(i) <= i₅
                          && i₅ < i
                          && a[x₆] == __VERIFIER_nondet_short₁₄)))
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
                   ==> i₅ < SIZE));
      {
        var __VERIFIER_nondet_short₁: int;
        a := a[i := __VERIFIER_nondet_short₁];
        i := i + 1;
      }
    }
    i := 0;
    while(i < SIZE)
      decreases SIZE - i;
      invariant true
        && old(i) <= i
        && i <= SIZE
        && (forall i₁₀: int ::
              (  old(i₁₀) <= i₁₀
                && old(i) <= i₁₀
                && i₁₀ < i
                 ==> i₁₀ < SIZE));
    {
      sum := sum + a[i];
      i := i + 1;
    }
    i := 0;
    while(i < SIZE)
      decreases SIZE - i;
      invariant true
        && old(i) <= i
        && i <= SIZE
        && (forall i₁₄: int ::
              (  old(i₁₄) <= i₁₄
                && old(i) <= i₁₄
                && i₁₄ < i
                 ==> i₁₄ < SIZE));
    {
      sum := sum + a[i];
      i := i + 1;
    }
    i := 0;
    while(i < SIZE)
      decreases SIZE - i;
      invariant true
        && old(i) <= i
        && i <= SIZE
        && (forall i₁₈: int ::
              (  old(i₁₈) <= i₁₈
                && old(i) <= i₁₈
                && i₁₈ < i
                 ==> i₁₈ < SIZE));
    {
      sum := sum + a[i];
      i := i + 1;
    }
    i := 0;
    while(i < SIZE)
      decreases SIZE - i;
      invariant true
        && old(i) <= i
        && i <= SIZE
        && (forall i₂₂: int ::
              (  old(i₂₂) <= i₂₂
                && old(i) <= i₂₂
                && i₂₂ < i
                 ==> i₂₂ < SIZE));
    {
      sum := sum + a[i];
      i := i + 1;
    }
    i := 0;
    while(i < SIZE)
      decreases SIZE - i;
      invariant true
        && old(i) <= i
        && i <= SIZE
        && (forall i₂₆: int ::
              (  old(i₂₆) <= i₂₆
                && old(i) <= i₂₆
                && i₂₆ < i
                 ==> i₂₆ < SIZE));
    {
      sum := sum - a[i];
      i := i + 1;
    }
    i := 0;
    while(i < SIZE)
      decreases SIZE - i;
      invariant true
        && old(i) <= i
        && i <= SIZE
        && (forall i₃₀: int ::
              (  old(i₃₀) <= i₃₀
                && old(i) <= i₃₀
                && i₃₀ < i
                 ==> i₃₀ < SIZE));
    {
      sum := sum - a[i];
      i := i + 1;
    }
    i := 0;
    while(i < SIZE)
      decreases SIZE - i;
      invariant true
        && old(i) <= i
        && i <= SIZE
        && (forall i₃₄: int ::
              (  old(i₃₄) <= i₃₄
                && old(i) <= i₃₄
                && i₃₄ < i
                 ==> i₃₄ < SIZE));
    {
      sum := sum - a[i];
      i := i + 1;
    }
    i := 0;
    while(i < SIZE)
      decreases SIZE - i;
      invariant true
        && old(i) <= i
        && i <= SIZE
        && (forall i₃₈: int ::
              (  old(i₃₈) <= i₃₈
                && old(i) <= i₃₈
                && i₃₈ < i
                 ==> i₃₈ < SIZE));
    {
      sum := sum - a[i];
      i := i + 1;
    }
    assert sum == 0;
  }
  c#result := 1;
  return;
}

