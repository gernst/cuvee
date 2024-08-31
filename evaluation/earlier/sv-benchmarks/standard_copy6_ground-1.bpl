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
  var a7: [int]int;
  var a: int;
  a := 0;
  while(a < 100000)
    decreases 100000 - a;
    invariant true
      && old(a) <= a
      && a <= 100000
      && (forall x₁₂: int ::
            ((exists a₁₁: int ::
                    x₁₂ == a₁₁
                    && old(a) <= a₁₁
                    && a₁₁ < a)
               ==> (exists __VERIFIER_nondet_int₁₉: int, a₁₁: int ::
                      a₁₁ < 100000
                      && x₁₂ == a₁₁
                      && old(a) <= a₁₁
                      && a₁₁ < a
                      && a1[x₁₂] == __VERIFIER_nondet_int₁₉)))
      && (forall x₁₂: int ::
            (!((exists a₁₁: int ::
                    x₁₂ == a₁₁
                    && old(a) <= a₁₁
                    && a₁₁ < a)
            )
               ==> a1[x₁₂] == old(a1[x₁₂])))
      && (forall x₁₃: int ::
            ((exists a₁₁: int ::
                    x₁₃ == a₁₁
                    && old(a) <= a₁₁
                    && a₁₁ < a)
               ==> (exists __VERIFIER_nondet_int₂₁₀: int, a₁₁: int ::
                      a₁₁ < 100000
                      && x₁₃ == a₁₁
                      && old(a) <= a₁₁
                      && a₁₁ < a
                      && a6[x₁₃] == __VERIFIER_nondet_int₂₁₀)))
      && (forall x₁₃: int ::
            (!((exists a₁₁: int ::
                    x₁₃ == a₁₁
                    && old(a) <= a₁₁
                    && a₁₁ < a)
            )
               ==> a6[x₁₃] == old(a6[x₁₃])))
      && (forall a₁₁: int ::
            (  old(a₁₁) <= a₁₁
              && old(a) <= a₁₁
              && a₁₁ < a
               ==> a₁₁ < 100000));
  {
    var __VERIFIER_nondet_int₁: int;
    a1 := a1[a := __VERIFIER_nondet_int₁];
    var __VERIFIER_nondet_int₂: int;
    a6 := a6[a := __VERIFIER_nondet_int₂];
    a := a + 1;
  }
  var i: int;
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
                      && a2[x₁₉] == a1[i₁₈])))
      && (forall x₁₉: int ::
            (!((exists i₁₈: int ::
                    x₁₉ == i₁₈
                    && old(i) <= i₁₈
                    && i₁₈ < i)
            )
               ==> a2[x₁₉] == old(a2[x₁₉])))
      && (forall i₁₈: int ::
            (  old(i₁₈) <= i₁₈
              && old(i) <= i₁₈
              && i₁₈ < i
               ==> i₁₈ < 100000));
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
                      && a3[x₂₃] == a2[i₂₂])))
      && (forall x₂₃: int ::
            (!((exists i₂₂: int ::
                    x₂₃ == i₂₂
                    && old(i) <= i₂₂
                    && i₂₂ < i)
            )
               ==> a3[x₂₃] == old(a3[x₂₃])))
      && (forall i₂₂: int ::
            (  old(i₂₂) <= i₂₂
              && old(i) <= i₂₂
              && i₂₂ < i
               ==> i₂₂ < 100000));
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
                      && a4[x₂₇] == a3[i₂₆])))
      && (forall x₂₇: int ::
            (!((exists i₂₆: int ::
                    x₂₇ == i₂₆
                    && old(i) <= i₂₆
                    && i₂₆ < i)
            )
               ==> a4[x₂₇] == old(a4[x₂₇])))
      && (forall i₂₆: int ::
            (  old(i₂₆) <= i₂₆
              && old(i) <= i₂₆
              && i₂₆ < i
               ==> i₂₆ < 100000));
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
                      && a5[x₃₁] == a4[i₃₀])))
      && (forall x₃₁: int ::
            (!((exists i₃₀: int ::
                    x₃₁ == i₃₀
                    && old(i) <= i₃₀
                    && i₃₀ < i)
            )
               ==> a5[x₃₁] == old(a5[x₃₁])))
      && (forall i₃₀: int ::
            (  old(i₃₀) <= i₃₀
              && old(i) <= i₃₀
              && i₃₀ < i
               ==> i₃₀ < 100000));
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
      && (forall x₃₅: int ::
            ((exists i₃₄: int ::
                    x₃₅ == i₃₄
                    && old(i) <= i₃₄
                    && i₃₄ < i)
               ==> (exists i₃₄: int ::
                      i₃₄ < 100000
                      && x₃₅ == i₃₄
                      && old(i) <= i₃₄
                      && i₃₄ < i
                      && a7[x₃₅] == a5[i₃₄])))
      && (forall x₃₅: int ::
            (!((exists i₃₄: int ::
                    x₃₅ == i₃₄
                    && old(i) <= i₃₄
                    && i₃₄ < i)
            )
               ==> a7[x₃₅] == old(a7[x₃₅])))
      && (forall i₃₄: int ::
            (  old(i₃₄) <= i₃₄
              && old(i) <= i₃₄
              && i₃₄ < i
               ==> i₃₄ < 100000));
  {
    a7 := a7[i := a5[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall x₃₉: int ::
            ((exists i₃₈: int ::
                    x₃₉ == i₃₈
                    && old(i) <= i₃₈
                    && i₃₈ < i)
               ==> (exists i₃₈: int ::
                      i₃₈ < 100000
                      && x₃₉ == i₃₈
                      && old(i) <= i₃₈
                      && i₃₈ < i
                      && a7[x₃₉] == a6[i₃₈])))
      && (forall x₃₉: int ::
            (!((exists i₃₈: int ::
                    x₃₉ == i₃₈
                    && old(i) <= i₃₈
                    && i₃₈ < i)
            )
               ==> a7[x₃₉] == old(a7[x₃₉])))
      && (forall i₃₈: int ::
            (  old(i₃₈) <= i₃₈
              && old(i) <= i₃₈
              && i₃₈ < i
               ==> i₃₈ < 100000));
  {
    a7 := a7[i := a6[i]];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant true
      && old(x) <= x
      && x <= 100000
      && (forall x₄₃: int ::
            (  old(x₄₃) <= x₄₃
              && old(x) <= x₄₃
              && x₄₃ < x
               ==> x₄₃ < 100000));
  {
    assert a1[x] == a7[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

