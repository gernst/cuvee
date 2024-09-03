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
  var b: [int]int;
  var k: int;
  var i: int;
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && 0 <= i
      && i <= 100000
      && (forall x₆: int ::
            ((exists i₅: int ::
                    x₆ == i₅
                    && 0 <= i₅
                    && i₅ < i)
               ==> (exists i₅: int ::
                      i₅ < 100000
                      && x₆ == i₅
                      && 0 <= i₅
                      && i₅ < i
                      && a[x₆] == i₅)))
      && (forall x₆: int ::
            (!((exists i₅: int ::
                    x₆ == i₅
                    && 0 <= i₅
                    && i₅ < i)
            )
               ==> a[x₆] == old(a[x₆])))
      && (forall x₇: int ::
            ((exists i₅: int ::
                    x₇ == i₅
                    && 0 <= i₅
                    && i₅ < i)
               ==> (exists i₅: int ::
                      i₅ < 100000
                      && x₇ == i₅
                      && 0 <= i₅
                      && i₅ < i
                      && b[x₇] == i₅)))
      && (forall x₇: int ::
            (!((exists i₅: int ::
                    x₇ == i₅
                    && 0 <= i₅
                    && i₅ < i)
            )
               ==> b[x₇] == old(b[x₇])))
      && (forall i₅: int ::
            (  0 <= i₅
              && i₅ < i
               ==> i₅ < 100000));
  {
    a := a[i := i];
    b := b[i := i];
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
               ==> (exists __VERIFIER_nondet_short₂₁₁: int, k₁₂: int, i₁₄: int ::
                      __VERIFIER_nondet_short₂₁₁ != 0
                      && i₁₄ < 100000
                      && x₁₅ == i₁₄
                      && 0 <= i₁₄
                      && i₁₄ < i
                      && a[x₁₅] == k₁₂)))
      && (forall x₁₅: int ::
            (!((exists i₁₄: int ::
                    x₁₅ == i₁₄
                    && 0 <= i₁₄
                    && i₁₄ < i)
            )
               ==> a[x₁₅] == old(a[x₁₅])))
      && (forall x₁₆: int ::
            ((exists i₁₄: int ::
                    x₁₆ == i₁₄
                    && 0 <= i₁₄
                    && i₁₄ < i)
               ==> (exists __VERIFIER_nondet_short₂₁₁: int, k₁₂: int, i₁₄: int ::
                      __VERIFIER_nondet_short₂₁₁ != 0
                      && i₁₄ < 100000
                      && x₁₆ == i₁₄
                      && 0 <= i₁₄
                      && i₁₄ < i
                      && b[x₁₆] == k₁₂ * k₁₂)))
      && (forall x₁₆: int ::
            (!((exists i₁₄: int ::
                    x₁₆ == i₁₄
                    && 0 <= i₁₄
                    && i₁₄ < i)
            )
               ==> b[x₁₆] == old(b[x₁₆])))
      && (forall i₁₄: int ::
            (  0 <= i₁₄
              && i₁₄ < i
               ==> i₁₄ < 100000));
  {
    var __VERIFIER_nondet_short₂: int;
    if(__VERIFIER_nondet_short₂ != 0) {
      havoc k;
      a := a[i := k];
      b := b[i := k * k];
    }
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && 0 <= i
      && i <= 100000
      && (forall i₂₁: int ::
            (  0 <= i₂₁
              && i₂₁ < i
               ==> i₂₁ < 100000));
  {
    assert a[i] == b[i] || b[i] == a[i] * a[i];
    i := i + 1;
  }
}

