data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var a1: [int]int;
  var a2: [int]int;
  var a3: [int]int;
  var a: int;
  a := 0;
  while(a < 100000)
    decreases 100000 - a;
    invariant true
      && 0 <= a
      && a <= 100000
      && (forall x₇: int ::
            ((exists a₆: int ::
                    x₇ == a₆
                    && 0 <= a₆
                    && a₆ < a)
               ==> (exists __VERIFIER_nondet_int₁₅: int, a₆: int ::
                      a₆ < 100000
                      && x₇ == a₆
                      && 0 <= a₆
                      && a₆ < a
                      && a1[x₇] == __VERIFIER_nondet_int₁₅)))
      && (forall x₇: int ::
            (!((exists a₆: int ::
                    x₇ == a₆
                    && 0 <= a₆
                    && a₆ < a)
            )
               ==> a1[x₇] == old(a1[x₇])))
      && (forall a₆: int ::
            (  0 <= a₆
              && a₆ < a
               ==> a₆ < 100000));
  {
    var __VERIFIER_nondet_int₁: int;
    a1 := a1[a := __VERIFIER_nondet_int₁];
    a := a + 1;
  }
  var i: int;
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && 0 <= i
      && i <= 100000
      && (forall x₁₂: int ::
            ((exists i₁₁: int ::
                    x₁₂ == i₁₁
                    && 0 <= i₁₁
                    && i₁₁ < i)
               ==> (exists i₁₁: int ::
                      i₁₁ < 100000
                      && x₁₂ == i₁₁
                      && 0 <= i₁₁
                      && i₁₁ < i
                      && a2[x₁₂] == a1[i₁₁])))
      && (forall x₁₂: int ::
            (!((exists i₁₁: int ::
                    x₁₂ == i₁₁
                    && 0 <= i₁₁
                    && i₁₁ < i)
            )
               ==> a2[x₁₂] == old(a2[x₁₂])))
      && (forall i₁₁: int ::
            (  0 <= i₁₁
              && i₁₁ < i
               ==> i₁₁ < 100000));
  {
    a2 := a2[i := a1[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && 0 <= i
      && i <= 100000
      && (forall x₁₆: int ::
            ((exists i₁₅: int ::
                    x₁₆ == i₁₅
                    && 0 <= i₁₅
                    && i₁₅ < i)
               ==> (exists i₁₅: int ::
                      i₁₅ < 100000
                      && x₁₆ == i₁₅
                      && 0 <= i₁₅
                      && i₁₅ < i
                      && a3[x₁₆] == a2[i₁₅])))
      && (forall x₁₆: int ::
            (!((exists i₁₅: int ::
                    x₁₆ == i₁₅
                    && 0 <= i₁₅
                    && i₁₅ < i)
            )
               ==> a3[x₁₆] == old(a3[x₁₆])))
      && (forall i₁₅: int ::
            (  0 <= i₁₅
              && i₁₅ < i
               ==> i₁₅ < 100000));
  {
    a3 := a3[i := a2[i]];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant true
      && 0 <= x
      && x <= 100000
      && (forall x₂₀: int ::
            (  0 <= x₂₀
              && x₂₀ < x
               ==> x₂₀ < 100000));
  {
    assert a1[x] == a3[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

