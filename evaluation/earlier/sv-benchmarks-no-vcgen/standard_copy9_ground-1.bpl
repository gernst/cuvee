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
  var a0: [int]int;
  var a: int;
  a := 0;
  while(a < 100000)
    decreases 100000 - a;
    invariant true
      && 0 <= a
      && a <= 100000
      && (forall x₁₅: int ::
            ((exists a₁₄: int ::
                    x₁₅ == a₁₄
                    && 0 <= a₁₄
                    && a₁₄ < a)
               ==> (exists __VERIFIER_nondet_int₁₁₂: int, a₁₄: int ::
                      a₁₄ < 100000
                      && x₁₅ == a₁₄
                      && 0 <= a₁₄
                      && a₁₄ < a
                      && a1[x₁₅] == __VERIFIER_nondet_int₁₁₂)))
      && (forall x₁₅: int ::
            (!((exists a₁₄: int ::
                    x₁₅ == a₁₄
                    && 0 <= a₁₄
                    && a₁₄ < a)
            )
               ==> a1[x₁₅] == old(a1[x₁₅])))
      && (forall x₁₆: int ::
            ((exists a₁₄: int ::
                    x₁₆ == a₁₄
                    && 0 <= a₁₄
                    && a₁₄ < a)
               ==> (exists __VERIFIER_nondet_int₂₁₃: int, a₁₄: int ::
                      a₁₄ < 100000
                      && x₁₆ == a₁₄
                      && 0 <= a₁₄
                      && a₁₄ < a
                      && a9[x₁₆] == __VERIFIER_nondet_int₂₁₃)))
      && (forall x₁₆: int ::
            (!((exists a₁₄: int ::
                    x₁₆ == a₁₄
                    && 0 <= a₁₄
                    && a₁₄ < a)
            )
               ==> a9[x₁₆] == old(a9[x₁₆])))
      && (forall a₁₄: int ::
            (  0 <= a₁₄
              && a₁₄ < a
               ==> a₁₄ < 100000));
  {
    var __VERIFIER_nondet_int₁: int;
    a1 := a1[a := __VERIFIER_nondet_int₁];
    var __VERIFIER_nondet_int₂: int;
    a9 := a9[a := __VERIFIER_nondet_int₂];
    a := a + 1;
  }
  var i: int;
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
                      && a2[x₂₂] == a1[i₂₁])))
      && (forall x₂₂: int ::
            (!((exists i₂₁: int ::
                    x₂₂ == i₂₁
                    && 0 <= i₂₁
                    && i₂₁ < i)
            )
               ==> a2[x₂₂] == old(a2[x₂₂])))
      && (forall i₂₁: int ::
            (  0 <= i₂₁
              && i₂₁ < i
               ==> i₂₁ < 100000));
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
                      && a3[x₂₆] == a2[i₂₅])))
      && (forall x₂₆: int ::
            (!((exists i₂₅: int ::
                    x₂₆ == i₂₅
                    && 0 <= i₂₅
                    && i₂₅ < i)
            )
               ==> a3[x₂₆] == old(a3[x₂₆])))
      && (forall i₂₅: int ::
            (  0 <= i₂₅
              && i₂₅ < i
               ==> i₂₅ < 100000));
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
                      && a4[x₃₀] == a3[i₂₉])))
      && (forall x₃₀: int ::
            (!((exists i₂₉: int ::
                    x₃₀ == i₂₉
                    && 0 <= i₂₉
                    && i₂₉ < i)
            )
               ==> a4[x₃₀] == old(a4[x₃₀])))
      && (forall i₂₉: int ::
            (  0 <= i₂₉
              && i₂₉ < i
               ==> i₂₉ < 100000));
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
                      && a5[x₃₄] == a4[i₃₃])))
      && (forall x₃₄: int ::
            (!((exists i₃₃: int ::
                    x₃₄ == i₃₃
                    && 0 <= i₃₃
                    && i₃₃ < i)
            )
               ==> a5[x₃₄] == old(a5[x₃₄])))
      && (forall i₃₃: int ::
            (  0 <= i₃₃
              && i₃₃ < i
               ==> i₃₃ < 100000));
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
                      && a6[x₃₈] == a5[i₃₇])))
      && (forall x₃₈: int ::
            (!((exists i₃₇: int ::
                    x₃₈ == i₃₇
                    && 0 <= i₃₇
                    && i₃₇ < i)
            )
               ==> a6[x₃₈] == old(a6[x₃₈])))
      && (forall i₃₇: int ::
            (  0 <= i₃₇
              && i₃₇ < i
               ==> i₃₇ < 100000));
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
                      && a7[x₄₂] == a6[i₄₁])))
      && (forall x₄₂: int ::
            (!((exists i₄₁: int ::
                    x₄₂ == i₄₁
                    && 0 <= i₄₁
                    && i₄₁ < i)
            )
               ==> a7[x₄₂] == old(a7[x₄₂])))
      && (forall i₄₁: int ::
            (  0 <= i₄₁
              && i₄₁ < i
               ==> i₄₁ < 100000));
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
                      && a8[x₄₆] == a7[i₄₅])))
      && (forall x₄₆: int ::
            (!((exists i₄₅: int ::
                    x₄₆ == i₄₅
                    && 0 <= i₄₅
                    && i₄₅ < i)
            )
               ==> a8[x₄₆] == old(a8[x₄₆])))
      && (forall i₄₅: int ::
            (  0 <= i₄₅
              && i₄₅ < i
               ==> i₄₅ < 100000));
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
      && (forall x₅₀: int ::
            ((exists i₄₉: int ::
                    x₅₀ == i₄₉
                    && 0 <= i₄₉
                    && i₄₉ < i)
               ==> (exists i₄₉: int ::
                      i₄₉ < 100000
                      && x₅₀ == i₄₉
                      && 0 <= i₄₉
                      && i₄₉ < i
                      && a0[x₅₀] == a8[i₄₉])))
      && (forall x₅₀: int ::
            (!((exists i₄₉: int ::
                    x₅₀ == i₄₉
                    && 0 <= i₄₉
                    && i₄₉ < i)
            )
               ==> a0[x₅₀] == old(a0[x₅₀])))
      && (forall i₄₉: int ::
            (  0 <= i₄₉
              && i₄₉ < i
               ==> i₄₉ < 100000));
  {
    a0 := a0[i := a8[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && 0 <= i
      && i <= 100000
      && (forall x₅₄: int ::
            ((exists i₅₃: int ::
                    x₅₄ == i₅₃
                    && 0 <= i₅₃
                    && i₅₃ < i)
               ==> (exists i₅₃: int ::
                      i₅₃ < 100000
                      && x₅₄ == i₅₃
                      && 0 <= i₅₃
                      && i₅₃ < i
                      && a0[x₅₄] == a9[i₅₃])))
      && (forall x₅₄: int ::
            (!((exists i₅₃: int ::
                    x₅₄ == i₅₃
                    && 0 <= i₅₃
                    && i₅₃ < i)
            )
               ==> a0[x₅₄] == old(a0[x₅₄])))
      && (forall i₅₃: int ::
            (  0 <= i₅₃
              && i₅₃ < i
               ==> i₅₃ < 100000));
  {
    a0 := a0[i := a9[i]];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant true
      && 0 <= x
      && x <= 100000
      && (forall x₅₈: int ::
            (  0 <= x₅₈
              && x₅₈ < x
               ==> x₅₈ < 100000));
  {
    assert a1[x] == a0[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

