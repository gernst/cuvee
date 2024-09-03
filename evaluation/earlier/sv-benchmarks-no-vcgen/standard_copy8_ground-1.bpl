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
  var a8: [int]int;
  var a9: [int]int;
  var a: int;
  a := 0;
  while(a < 100000)
    decreases 100000 - a;
    invariant true
      && 0 <= a
      && a <= 100000
      && (forall x₁₃: int ::
            ((exists a₁₂: int ::
                    x₁₃ == a₁₂
                    && 0 <= a₁₂
                    && a₁₂ < a)
               ==> (exists __VERIFIER_nondet_int₁₁₁: int, a₁₂: int ::
                      a₁₂ < 100000
                      && x₁₃ == a₁₂
                      && 0 <= a₁₂
                      && a₁₂ < a
                      && a1[x₁₃] == __VERIFIER_nondet_int₁₁₁)))
      && (forall x₁₃: int ::
            (!((exists a₁₂: int ::
                    x₁₃ == a₁₂
                    && 0 <= a₁₂
                    && a₁₂ < a)
            )
               ==> a1[x₁₃] == old(a1[x₁₃])))
      && (forall a₁₂: int ::
            (  0 <= a₁₂
              && a₁₂ < a
               ==> a₁₂ < 100000));
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
                      && a5[x₃₀] == a4[i₂₉])))
      && (forall x₃₀: int ::
            (!((exists i₂₉: int ::
                    x₃₀ == i₂₉
                    && 0 <= i₂₉
                    && i₂₉ < i)
            )
               ==> a5[x₃₀] == old(a5[x₃₀])))
      && (forall i₂₉: int ::
            (  0 <= i₂₉
              && i₂₉ < i
               ==> i₂₉ < 100000));
  {
    a5 := a5[i := a4[i]];
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
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && 0 <= i
      && i <= 100000
      && (forall x₃₈: int ::
            ((exists i₃₇: int ::
                    x₃₈ == i₃₇
                    && 0 <= i₃₇
                    && i₃₇ < i)
               ==> (exists i₃₇: int ::
                      i₃₇ < 100000
                      && x₃₈ == i₃₇
                      && 0 <= i₃₇
                      && i₃₇ < i
                      && a7[x₃₈] == a6[i₃₇])))
      && (forall x₃₈: int ::
            (!((exists i₃₇: int ::
                    x₃₈ == i₃₇
                    && 0 <= i₃₇
                    && i₃₇ < i)
            )
               ==> a7[x₃₈] == old(a7[x₃₈])))
      && (forall i₃₇: int ::
            (  0 <= i₃₇
              && i₃₇ < i
               ==> i₃₇ < 100000));
  {
    a7 := a7[i := a6[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && 0 <= i
      && i <= 100000
      && (forall x₄₂: int ::
            ((exists i₄₁: int ::
                    x₄₂ == i₄₁
                    && 0 <= i₄₁
                    && i₄₁ < i)
               ==> (exists i₄₁: int ::
                      i₄₁ < 100000
                      && x₄₂ == i₄₁
                      && 0 <= i₄₁
                      && i₄₁ < i
                      && a8[x₄₂] == a7[i₄₁])))
      && (forall x₄₂: int ::
            (!((exists i₄₁: int ::
                    x₄₂ == i₄₁
                    && 0 <= i₄₁
                    && i₄₁ < i)
            )
               ==> a8[x₄₂] == old(a8[x₄₂])))
      && (forall i₄₁: int ::
            (  0 <= i₄₁
              && i₄₁ < i
               ==> i₄₁ < 100000));
  {
    a8 := a8[i := a7[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && 0 <= i
      && i <= 100000
      && (forall x₄₆: int ::
            ((exists i₄₅: int ::
                    x₄₆ == i₄₅
                    && 0 <= i₄₅
                    && i₄₅ < i)
               ==> (exists i₄₅: int ::
                      i₄₅ < 100000
                      && x₄₆ == i₄₅
                      && 0 <= i₄₅
                      && i₄₅ < i
                      && a9[x₄₆] == a8[i₄₅])))
      && (forall x₄₆: int ::
            (!((exists i₄₅: int ::
                    x₄₆ == i₄₅
                    && 0 <= i₄₅
                    && i₄₅ < i)
            )
               ==> a9[x₄₆] == old(a9[x₄₆])))
      && (forall i₄₅: int ::
            (  0 <= i₄₅
              && i₄₅ < i
               ==> i₄₅ < 100000));
  {
    a9 := a9[i := a8[i]];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant true
      && 0 <= x
      && x <= 100000
      && (forall x₅₀: int ::
            (  0 <= x₅₀
              && x₅₀ < x
               ==> x₅₀ < 100000));
  {
    assert a1[x] == a9[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

