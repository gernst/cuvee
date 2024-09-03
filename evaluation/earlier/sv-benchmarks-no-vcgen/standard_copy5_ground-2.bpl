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
      && 0 <= a
      && a <= 100000
      && (forall x₁₁: int ::
            ((exists a₁₀: int ::
                    x₁₁ == a₁₀
                    && 0 <= a₁₀
                    && a₁₀ < a)
               ==> (exists __VERIFIER_nondet_int₁₈: int, a₁₀: int ::
                      a₁₀ < 100000
                      && x₁₁ == a₁₀
                      && 0 <= a₁₀
                      && a₁₀ < a
                      && a1[x₁₁] == __VERIFIER_nondet_int₁₈)))
      && (forall x₁₁: int ::
            (!((exists a₁₀: int ::
                    x₁₁ == a₁₀
                    && 0 <= a₁₀
                    && a₁₀ < a)
            )
               ==> a1[x₁₁] == old(a1[x₁₁])))
      && (forall x₁₂: int ::
            ((exists a₁₀: int ::
                    x₁₂ == a₁₀
                    && 0 <= a₁₀
                    && a₁₀ < a)
               ==> (exists __VERIFIER_nondet_int₂₉: int, a₁₀: int ::
                      a₁₀ < 100000
                      && x₁₂ == a₁₀
                      && 0 <= a₁₀
                      && a₁₀ < a
                      && a5[x₁₂] == __VERIFIER_nondet_int₂₉)))
      && (forall x₁₂: int ::
            (!((exists a₁₀: int ::
                    x₁₂ == a₁₀
                    && 0 <= a₁₀
                    && a₁₀ < a)
            )
               ==> a5[x₁₂] == old(a5[x₁₂])))
      && (forall a₁₀: int ::
            (  0 <= a₁₀
              && a₁₀ < a
               ==> a₁₀ < 100000));
  {
    var __VERIFIER_nondet_int₁: int;
    a1 := a1[a := __VERIFIER_nondet_int₁];
    var __VERIFIER_nondet_int₂: int;
    a5 := a5[a := __VERIFIER_nondet_int₂];
    a := a + 1;
  }
  var i: int;
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && 0 <= i
      && i <= 100000
      && (forall x₁₈: int ::
            ((exists i₁₇: int ::
                    x₁₈ == i₁₇
                    && 0 <= i₁₇
                    && i₁₇ < i)
               ==> (exists i₁₇: int ::
                      i₁₇ < 100000
                      && x₁₈ == i₁₇
                      && 0 <= i₁₇
                      && i₁₇ < i
                      && a2[x₁₈] == a1[i₁₇])))
      && (forall x₁₈: int ::
            (!((exists i₁₇: int ::
                    x₁₈ == i₁₇
                    && 0 <= i₁₇
                    && i₁₇ < i)
            )
               ==> a2[x₁₈] == old(a2[x₁₈])))
      && (forall i₁₇: int ::
            (  0 <= i₁₇
              && i₁₇ < i
               ==> i₁₇ < 100000));
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
      && (forall x₂₂: int ::
            ((exists i₂₁: int ::
                    x₂₂ == i₂₁
                    && 0 <= i₂₁
                    && i₂₁ < i)
               ==> (exists i₂₁: int ::
                      i₂₁ < 100000
                      && x₂₂ == i₂₁
                      && 0 <= i₂₁
                      && i₂₁ < i
                      && a3[x₂₂] == a2[i₂₁])))
      && (forall x₂₂: int ::
            (!((exists i₂₁: int ::
                    x₂₂ == i₂₁
                    && 0 <= i₂₁
                    && i₂₁ < i)
            )
               ==> a3[x₂₂] == old(a3[x₂₂])))
      && (forall i₂₁: int ::
            (  0 <= i₂₁
              && i₂₁ < i
               ==> i₂₁ < 100000));
  {
    a3 := a3[i := a2[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && 0 <= i
      && i <= 100000
      && (forall x₂₆: int ::
            ((exists i₂₅: int ::
                    x₂₆ == i₂₅
                    && 0 <= i₂₅
                    && i₂₅ < i)
               ==> (exists i₂₅: int ::
                      i₂₅ < 100000
                      && x₂₆ == i₂₅
                      && 0 <= i₂₅
                      && i₂₅ < i
                      && a4[x₂₆] == a3[i₂₅])))
      && (forall x₂₆: int ::
            (!((exists i₂₅: int ::
                    x₂₆ == i₂₅
                    && 0 <= i₂₅
                    && i₂₅ < i)
            )
               ==> a4[x₂₆] == old(a4[x₂₆])))
      && (forall i₂₅: int ::
            (  0 <= i₂₅
              && i₂₅ < i
               ==> i₂₅ < 100000));
  {
    a4 := a4[i := a3[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && 0 <= i
      && i <= 100000
      && (forall x₃₀: int ::
            ((exists i₂₉: int ::
                    x₃₀ == i₂₉
                    && 0 <= i₂₉
                    && i₂₉ < i)
               ==> (exists i₂₉: int ::
                      i₂₉ < 100000
                      && x₃₀ == i₂₉
                      && 0 <= i₂₉
                      && i₂₉ < i
                      && a6[x₃₀] == a4[i₂₉])))
      && (forall x₃₀: int ::
            (!((exists i₂₉: int ::
                    x₃₀ == i₂₉
                    && 0 <= i₂₉
                    && i₂₉ < i)
            )
               ==> a6[x₃₀] == old(a6[x₃₀])))
      && (forall i₂₉: int ::
            (  0 <= i₂₉
              && i₂₉ < i
               ==> i₂₉ < 100000));
  {
    a6 := a6[i := a4[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && 0 <= i
      && i <= 100000
      && (forall x₃₄: int ::
            ((exists i₃₃: int ::
                    x₃₄ == i₃₃
                    && 0 <= i₃₃
                    && i₃₃ < i)
               ==> (exists i₃₃: int ::
                      i₃₃ < 100000
                      && x₃₄ == i₃₃
                      && 0 <= i₃₃
                      && i₃₃ < i
                      && a6[x₃₄] == a5[i₃₃])))
      && (forall x₃₄: int ::
            (!((exists i₃₃: int ::
                    x₃₄ == i₃₃
                    && 0 <= i₃₃
                    && i₃₃ < i)
            )
               ==> a6[x₃₄] == old(a6[x₃₄])))
      && (forall i₃₃: int ::
            (  0 <= i₃₃
              && i₃₃ < i
               ==> i₃₃ < 100000));
  {
    a6 := a6[i := a5[i]];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant true
      && 0 <= x
      && x <= 100000
      && (forall x₃₈: int ::
            (  0 <= x₃₈
              && x₃₈ < x
               ==> x₃₈ < 100000));
  {
    assert a1[x] == a6[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

