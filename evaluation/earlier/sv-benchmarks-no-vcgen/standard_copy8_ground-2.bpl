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
      && (forall x₁₄: int ::
            ((exists a₁₃: int ::
                    x₁₄ == a₁₃
                    && 0 <= a₁₃
                    && a₁₃ < a)
               ==> (exists __VERIFIER_nondet_int₁₁₁: int, a₁₃: int ::
                      a₁₃ < 100000
                      && x₁₄ == a₁₃
                      && 0 <= a₁₃
                      && a₁₃ < a
                      && a1[x₁₄] == __VERIFIER_nondet_int₁₁₁)))
      && (forall x₁₄: int ::
            (!((exists a₁₃: int ::
                    x₁₄ == a₁₃
                    && 0 <= a₁₃
                    && a₁₃ < a)
            )
               ==> a1[x₁₄] == old(a1[x₁₄])))
      && (forall x₁₅: int ::
            ((exists a₁₃: int ::
                    x₁₅ == a₁₃
                    && 0 <= a₁₃
                    && a₁₃ < a)
               ==> (exists __VERIFIER_nondet_int₂₁₂: int, a₁₃: int ::
                      a₁₃ < 100000
                      && x₁₅ == a₁₃
                      && 0 <= a₁₃
                      && a₁₃ < a
                      && a8[x₁₅] == __VERIFIER_nondet_int₂₁₂)))
      && (forall x₁₅: int ::
            (!((exists a₁₃: int ::
                    x₁₅ == a₁₃
                    && 0 <= a₁₃
                    && a₁₃ < a)
            )
               ==> a8[x₁₅] == old(a8[x₁₅])))
      && (forall a₁₃: int ::
            (  0 <= a₁₃
              && a₁₃ < a
               ==> a₁₃ < 100000));
  {
    var __VERIFIER_nondet_int₁: int;
    a1 := a1[a := __VERIFIER_nondet_int₁];
    var __VERIFIER_nondet_int₂: int;
    a8 := a8[a := __VERIFIER_nondet_int₂];
    a := a + 1;
  }
  var i: int;
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && 0 <= i
      && i <= 100000
      && (forall x₂₁: int ::
            ((exists i₂₀: int ::
                    x₂₁ == i₂₀
                    && 0 <= i₂₀
                    && i₂₀ < i)
               ==> (exists i₂₀: int ::
                      i₂₀ < 100000
                      && x₂₁ == i₂₀
                      && 0 <= i₂₀
                      && i₂₀ < i
                      && a2[x₂₁] == a1[i₂₀])))
      && (forall x₂₁: int ::
            (!((exists i₂₀: int ::
                    x₂₁ == i₂₀
                    && 0 <= i₂₀
                    && i₂₀ < i)
            )
               ==> a2[x₂₁] == old(a2[x₂₁])))
      && (forall i₂₀: int ::
            (  0 <= i₂₀
              && i₂₀ < i
               ==> i₂₀ < 100000));
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
      && (forall x₂₅: int ::
            ((exists i₂₄: int ::
                    x₂₅ == i₂₄
                    && 0 <= i₂₄
                    && i₂₄ < i)
               ==> (exists i₂₄: int ::
                      i₂₄ < 100000
                      && x₂₅ == i₂₄
                      && 0 <= i₂₄
                      && i₂₄ < i
                      && a3[x₂₅] == a2[i₂₄])))
      && (forall x₂₅: int ::
            (!((exists i₂₄: int ::
                    x₂₅ == i₂₄
                    && 0 <= i₂₄
                    && i₂₄ < i)
            )
               ==> a3[x₂₅] == old(a3[x₂₅])))
      && (forall i₂₄: int ::
            (  0 <= i₂₄
              && i₂₄ < i
               ==> i₂₄ < 100000));
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
      && (forall x₂₉: int ::
            ((exists i₂₈: int ::
                    x₂₉ == i₂₈
                    && 0 <= i₂₈
                    && i₂₈ < i)
               ==> (exists i₂₈: int ::
                      i₂₈ < 100000
                      && x₂₉ == i₂₈
                      && 0 <= i₂₈
                      && i₂₈ < i
                      && a4[x₂₉] == a3[i₂₈])))
      && (forall x₂₉: int ::
            (!((exists i₂₈: int ::
                    x₂₉ == i₂₈
                    && 0 <= i₂₈
                    && i₂₈ < i)
            )
               ==> a4[x₂₉] == old(a4[x₂₉])))
      && (forall i₂₈: int ::
            (  0 <= i₂₈
              && i₂₈ < i
               ==> i₂₈ < 100000));
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
      && (forall x₃₃: int ::
            ((exists i₃₂: int ::
                    x₃₃ == i₃₂
                    && 0 <= i₃₂
                    && i₃₂ < i)
               ==> (exists i₃₂: int ::
                      i₃₂ < 100000
                      && x₃₃ == i₃₂
                      && 0 <= i₃₂
                      && i₃₂ < i
                      && a5[x₃₃] == a4[i₃₂])))
      && (forall x₃₃: int ::
            (!((exists i₃₂: int ::
                    x₃₃ == i₃₂
                    && 0 <= i₃₂
                    && i₃₂ < i)
            )
               ==> a5[x₃₃] == old(a5[x₃₃])))
      && (forall i₃₂: int ::
            (  0 <= i₃₂
              && i₃₂ < i
               ==> i₃₂ < 100000));
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
      && (forall x₃₇: int ::
            ((exists i₃₆: int ::
                    x₃₇ == i₃₆
                    && 0 <= i₃₆
                    && i₃₆ < i)
               ==> (exists i₃₆: int ::
                      i₃₆ < 100000
                      && x₃₇ == i₃₆
                      && 0 <= i₃₆
                      && i₃₆ < i
                      && a6[x₃₇] == a5[i₃₆])))
      && (forall x₃₇: int ::
            (!((exists i₃₆: int ::
                    x₃₇ == i₃₆
                    && 0 <= i₃₆
                    && i₃₆ < i)
            )
               ==> a6[x₃₇] == old(a6[x₃₇])))
      && (forall i₃₆: int ::
            (  0 <= i₃₆
              && i₃₆ < i
               ==> i₃₆ < 100000));
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
      && (forall x₄₁: int ::
            ((exists i₄₀: int ::
                    x₄₁ == i₄₀
                    && 0 <= i₄₀
                    && i₄₀ < i)
               ==> (exists i₄₀: int ::
                      i₄₀ < 100000
                      && x₄₁ == i₄₀
                      && 0 <= i₄₀
                      && i₄₀ < i
                      && a7[x₄₁] == a6[i₄₀])))
      && (forall x₄₁: int ::
            (!((exists i₄₀: int ::
                    x₄₁ == i₄₀
                    && 0 <= i₄₀
                    && i₄₀ < i)
            )
               ==> a7[x₄₁] == old(a7[x₄₁])))
      && (forall i₄₀: int ::
            (  0 <= i₄₀
              && i₄₀ < i
               ==> i₄₀ < 100000));
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
      && (forall x₄₅: int ::
            ((exists i₄₄: int ::
                    x₄₅ == i₄₄
                    && 0 <= i₄₄
                    && i₄₄ < i)
               ==> (exists i₄₄: int ::
                      i₄₄ < 100000
                      && x₄₅ == i₄₄
                      && 0 <= i₄₄
                      && i₄₄ < i
                      && a9[x₄₅] == a7[i₄₄])))
      && (forall x₄₅: int ::
            (!((exists i₄₄: int ::
                    x₄₅ == i₄₄
                    && 0 <= i₄₄
                    && i₄₄ < i)
            )
               ==> a9[x₄₅] == old(a9[x₄₅])))
      && (forall i₄₄: int ::
            (  0 <= i₄₄
              && i₄₄ < i
               ==> i₄₄ < 100000));
  {
    a9 := a9[i := a7[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && 0 <= i
      && i <= 100000
      && (forall x₄₉: int ::
            ((exists i₄₈: int ::
                    x₄₉ == i₄₈
                    && 0 <= i₄₈
                    && i₄₈ < i)
               ==> (exists i₄₈: int ::
                      i₄₈ < 100000
                      && x₄₉ == i₄₈
                      && 0 <= i₄₈
                      && i₄₈ < i
                      && a9[x₄₉] == a8[i₄₈])))
      && (forall x₄₉: int ::
            (!((exists i₄₈: int ::
                    x₄₉ == i₄₈
                    && 0 <= i₄₈
                    && i₄₈ < i)
            )
               ==> a9[x₄₉] == old(a9[x₄₉])))
      && (forall i₄₈: int ::
            (  0 <= i₄₈
              && i₄₈ < i
               ==> i₄₈ < 100000));
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
      && (forall x₅₃: int ::
            (  0 <= x₅₃
              && x₅₃ < x
               ==> x₅₃ < 100000));
  {
    assert a1[x] == a9[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

