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
               ==> (exists __VERIFIER_nondet_int₁₁₀: int, a₁₂: int ::
                      a₁₂ < 100000
                      && x₁₃ == a₁₂
                      && 0 <= a₁₂
                      && a₁₂ < a
                      && a1[x₁₃] == __VERIFIER_nondet_int₁₁₀)))
      && (forall x₁₃: int ::
            (!((exists a₁₂: int ::
                    x₁₃ == a₁₂
                    && 0 <= a₁₂
                    && a₁₂ < a)
            )
               ==> a1[x₁₃] == old(a1[x₁₃])))
      && (forall x₁₄: int ::
            ((exists a₁₂: int ::
                    x₁₄ == a₁₂
                    && 0 <= a₁₂
                    && a₁₂ < a)
               ==> (exists __VERIFIER_nondet_int₂₁₁: int, a₁₂: int ::
                      a₁₂ < 100000
                      && x₁₄ == a₁₂
                      && 0 <= a₁₂
                      && a₁₂ < a
                      && a7[x₁₄] == __VERIFIER_nondet_int₂₁₁)))
      && (forall x₁₄: int ::
            (!((exists a₁₂: int ::
                    x₁₄ == a₁₂
                    && 0 <= a₁₂
                    && a₁₂ < a)
            )
               ==> a7[x₁₄] == old(a7[x₁₄])))
      && (forall a₁₂: int ::
            (  0 <= a₁₂
              && a₁₂ < a
               ==> a₁₂ < 100000));
  {
    var __VERIFIER_nondet_int₁: int;
    a1 := a1[a := __VERIFIER_nondet_int₁];
    var __VERIFIER_nondet_int₂: int;
    a7 := a7[a := __VERIFIER_nondet_int₂];
    a := a + 1;
  }
  var i: int;
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && 0 <= i
      && i <= 100000
      && (forall x₂₀: int ::
            ((exists i₁₉: int ::
                    x₂₀ == i₁₉
                    && 0 <= i₁₉
                    && i₁₉ < i)
               ==> (exists i₁₉: int ::
                      i₁₉ < 100000
                      && x₂₀ == i₁₉
                      && 0 <= i₁₉
                      && i₁₉ < i
                      && a2[x₂₀] == a1[i₁₉])))
      && (forall x₂₀: int ::
            (!((exists i₁₉: int ::
                    x₂₀ == i₁₉
                    && 0 <= i₁₉
                    && i₁₉ < i)
            )
               ==> a2[x₂₀] == old(a2[x₂₀])))
      && (forall i₁₉: int ::
            (  0 <= i₁₉
              && i₁₉ < i
               ==> i₁₉ < 100000));
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
      && (forall x₂₄: int ::
            ((exists i₂₃: int ::
                    x₂₄ == i₂₃
                    && 0 <= i₂₃
                    && i₂₃ < i)
               ==> (exists i₂₃: int ::
                      i₂₃ < 100000
                      && x₂₄ == i₂₃
                      && 0 <= i₂₃
                      && i₂₃ < i
                      && a3[x₂₄] == a2[i₂₃])))
      && (forall x₂₄: int ::
            (!((exists i₂₃: int ::
                    x₂₄ == i₂₃
                    && 0 <= i₂₃
                    && i₂₃ < i)
            )
               ==> a3[x₂₄] == old(a3[x₂₄])))
      && (forall i₂₃: int ::
            (  0 <= i₂₃
              && i₂₃ < i
               ==> i₂₃ < 100000));
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
      && (forall x₂₈: int ::
            ((exists i₂₇: int ::
                    x₂₈ == i₂₇
                    && 0 <= i₂₇
                    && i₂₇ < i)
               ==> (exists i₂₇: int ::
                      i₂₇ < 100000
                      && x₂₈ == i₂₇
                      && 0 <= i₂₇
                      && i₂₇ < i
                      && a4[x₂₈] == a3[i₂₇])))
      && (forall x₂₈: int ::
            (!((exists i₂₇: int ::
                    x₂₈ == i₂₇
                    && 0 <= i₂₇
                    && i₂₇ < i)
            )
               ==> a4[x₂₈] == old(a4[x₂₈])))
      && (forall i₂₇: int ::
            (  0 <= i₂₇
              && i₂₇ < i
               ==> i₂₇ < 100000));
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
      && (forall x₃₂: int ::
            ((exists i₃₁: int ::
                    x₃₂ == i₃₁
                    && 0 <= i₃₁
                    && i₃₁ < i)
               ==> (exists i₃₁: int ::
                      i₃₁ < 100000
                      && x₃₂ == i₃₁
                      && 0 <= i₃₁
                      && i₃₁ < i
                      && a5[x₃₂] == a4[i₃₁])))
      && (forall x₃₂: int ::
            (!((exists i₃₁: int ::
                    x₃₂ == i₃₁
                    && 0 <= i₃₁
                    && i₃₁ < i)
            )
               ==> a5[x₃₂] == old(a5[x₃₂])))
      && (forall i₃₁: int ::
            (  0 <= i₃₁
              && i₃₁ < i
               ==> i₃₁ < 100000));
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
      && (forall x₃₆: int ::
            ((exists i₃₅: int ::
                    x₃₆ == i₃₅
                    && 0 <= i₃₅
                    && i₃₅ < i)
               ==> (exists i₃₅: int ::
                      i₃₅ < 100000
                      && x₃₆ == i₃₅
                      && 0 <= i₃₅
                      && i₃₅ < i
                      && a6[x₃₆] == a5[i₃₅])))
      && (forall x₃₆: int ::
            (!((exists i₃₅: int ::
                    x₃₆ == i₃₅
                    && 0 <= i₃₅
                    && i₃₅ < i)
            )
               ==> a6[x₃₆] == old(a6[x₃₆])))
      && (forall i₃₅: int ::
            (  0 <= i₃₅
              && i₃₅ < i
               ==> i₃₅ < 100000));
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
      && (forall x₄₀: int ::
            ((exists i₃₉: int ::
                    x₄₀ == i₃₉
                    && 0 <= i₃₉
                    && i₃₉ < i)
               ==> (exists i₃₉: int ::
                      i₃₉ < 100000
                      && x₄₀ == i₃₉
                      && 0 <= i₃₉
                      && i₃₉ < i
                      && a8[x₄₀] == a6[i₃₉])))
      && (forall x₄₀: int ::
            (!((exists i₃₉: int ::
                    x₄₀ == i₃₉
                    && 0 <= i₃₉
                    && i₃₉ < i)
            )
               ==> a8[x₄₀] == old(a8[x₄₀])))
      && (forall i₃₉: int ::
            (  0 <= i₃₉
              && i₃₉ < i
               ==> i₃₉ < 100000));
  {
    a8 := a8[i := a6[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && 0 <= i
      && i <= 100000
      && (forall x₄₄: int ::
            ((exists i₄₃: int ::
                    x₄₄ == i₄₃
                    && 0 <= i₄₃
                    && i₄₃ < i)
               ==> (exists i₄₃: int ::
                      i₄₃ < 100000
                      && x₄₄ == i₄₃
                      && 0 <= i₄₃
                      && i₄₃ < i
                      && a8[x₄₄] == a7[i₄₃])))
      && (forall x₄₄: int ::
            (!((exists i₄₃: int ::
                    x₄₄ == i₄₃
                    && 0 <= i₄₃
                    && i₄₃ < i)
            )
               ==> a8[x₄₄] == old(a8[x₄₄])))
      && (forall i₄₃: int ::
            (  0 <= i₄₃
              && i₄₃ < i
               ==> i₄₃ < 100000));
  {
    a8 := a8[i := a7[i]];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant true
      && 0 <= x
      && x <= 100000
      && (forall x₄₈: int ::
            (  0 <= x₄₈
              && x₄₈ < x
               ==> x₄₈ < 100000));
  {
    assert a1[x] == a8[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

