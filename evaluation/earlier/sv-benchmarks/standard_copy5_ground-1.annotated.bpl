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
  var a4: [int]int;
  var a5: [int]int;
  var a6: [int]int;
  var a: int;
  a := 0;
  while(a < 100000)
    decreases 100000 - a;
    invariant true
      && old(a) <= a
      && a <= 100000
      && (forall x₁₀: int ::
            ((exists a₉: int ::
                    x₁₀ == a₉
                    && old(a) <= a₉
                    && a₉ < a)
               ==> (exists __VERIFIER_nondet_int₁₈: int, a₉: int ::
                      a₉ < 100000
                      && x₁₀ == a₉
                      && old(a) <= a₉
                      && a₉ < a
                      && a1[x₁₀] == __VERIFIER_nondet_int₁₈)))
      && (forall x₁₀: int ::
            (!((exists a₉: int ::
                    x₁₀ == a₉
                    && old(a) <= a₉
                    && a₉ < a)
            )
               ==> a1[x₁₀] == old(a1[x₁₀])))
      && (forall a₉: int ::
            (  old(a) <= a₉
              && a₉ < a
               ==> a₉ < 100000));
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
                      && a2[x₁₅] == a1[i₁₄])))
      && (forall x₁₅: int ::
            (!((exists i₁₄: int ::
                    x₁₅ == i₁₄
                    && old(i) <= i₁₄
                    && i₁₄ < i)
            )
               ==> a2[x₁₅] == old(a2[x₁₅])))
      && (forall i₁₄: int ::
            (  old(i) <= i₁₄
              && i₁₄ < i
               ==> i₁₄ < 100000));
  {
    a2 := a2[i := a1[i]];
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
                      && a3[x₁₉] == a2[i₁₈])))
      && (forall x₁₉: int ::
            (!((exists i₁₈: int ::
                    x₁₉ == i₁₈
                    && old(i) <= i₁₈
                    && i₁₈ < i)
            )
               ==> a3[x₁₉] == old(a3[x₁₉])))
      && (forall i₁₈: int ::
            (  old(i) <= i₁₈
              && i₁₈ < i
               ==> i₁₈ < 100000));
  {
    a3 := a3[i := a2[i]];
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
                      && a4[x₂₃] == a3[i₂₂])))
      && (forall x₂₃: int ::
            (!((exists i₂₂: int ::
                    x₂₃ == i₂₂
                    && old(i) <= i₂₂
                    && i₂₂ < i)
            )
               ==> a4[x₂₃] == old(a4[x₂₃])))
      && (forall i₂₂: int ::
            (  old(i) <= i₂₂
              && i₂₂ < i
               ==> i₂₂ < 100000));
  {
    a4 := a4[i := a3[i]];
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
                      && a5[x₂₇] == a4[i₂₆])))
      && (forall x₂₇: int ::
            (!((exists i₂₆: int ::
                    x₂₇ == i₂₆
                    && old(i) <= i₂₆
                    && i₂₆ < i)
            )
               ==> a5[x₂₇] == old(a5[x₂₇])))
      && (forall i₂₆: int ::
            (  old(i) <= i₂₆
              && i₂₆ < i
               ==> i₂₆ < 100000));
  {
    a5 := a5[i := a4[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall x₃₁: int ::
            ((exists i₃₀: int ::
                    x₃₁ == i₃₀
                    && old(i) <= i₃₀
                    && i₃₀ < i)
               ==> (exists i₃₀: int ::
                      i₃₀ < 100000
                      && x₃₁ == i₃₀
                      && old(i) <= i₃₀
                      && i₃₀ < i
                      && a6[x₃₁] == a5[i₃₀])))
      && (forall x₃₁: int ::
            (!((exists i₃₀: int ::
                    x₃₁ == i₃₀
                    && old(i) <= i₃₀
                    && i₃₀ < i)
            )
               ==> a6[x₃₁] == old(a6[x₃₁])))
      && (forall i₃₀: int ::
            (  old(i) <= i₃₀
              && i₃₀ < i
               ==> i₃₀ < 100000));
  {
    a6 := a6[i := a5[i]];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant true
      && old(x) <= x
      && x <= 100000
      && (forall x₃₅: int ::
            (  old(x) <= x₃₅
              && x₃₅ < x
               ==> x₃₅ < 100000));
  {
    assert a1[x] == a6[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

