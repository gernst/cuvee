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
      && old(a) <= a
      && a <= 100000
      && (forall x₁₄: int ::
            ((exists a₁₃: int ::
                    x₁₄ == a₁₃
                    && old(a) <= a₁₃
                    && a₁₃ < a)
               ==> (exists __VERIFIER_nondet_int₁₁₂: int, a₁₃: int ::
                      a₁₃ < 100000
                      && x₁₄ == a₁₃
                      && old(a) <= a₁₃
                      && a₁₃ < a
                      && a1[x₁₄] == __VERIFIER_nondet_int₁₁₂)))
      && (forall x₁₄: int ::
            (!((exists a₁₃: int ::
                    x₁₄ == a₁₃
                    && old(a) <= a₁₃
                    && a₁₃ < a)
            )
               ==> a1[x₁₄] == old(a1[x₁₄])))
      && (forall a₁₃: int ::
            (  old(a₁₃) <= a₁₃
              && old(a) <= a₁₃
              && a₁₃ < a
               ==> a₁₃ < 100000));
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
                      && a6[x₃₅] == a5[i₃₄])))
      && (forall x₃₅: int ::
            (!((exists i₃₄: int ::
                    x₃₅ == i₃₄
                    && old(i) <= i₃₄
                    && i₃₄ < i)
            )
               ==> a6[x₃₅] == old(a6[x₃₅])))
      && (forall i₃₄: int ::
            (  old(i₃₄) <= i₃₄
              && old(i) <= i₃₄
              && i₃₄ < i
               ==> i₃₄ < 100000));
  {
    a6 := a6[i := a5[i]];
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
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall x₄₃: int ::
            ((exists i₄₂: int ::
                    x₄₃ == i₄₂
                    && old(i) <= i₄₂
                    && i₄₂ < i)
               ==> (exists i₄₂: int ::
                      i₄₂ < 100000
                      && x₄₃ == i₄₂
                      && old(i) <= i₄₂
                      && i₄₂ < i
                      && a8[x₄₃] == a7[i₄₂])))
      && (forall x₄₃: int ::
            (!((exists i₄₂: int ::
                    x₄₃ == i₄₂
                    && old(i) <= i₄₂
                    && i₄₂ < i)
            )
               ==> a8[x₄₃] == old(a8[x₄₃])))
      && (forall i₄₂: int ::
            (  old(i₄₂) <= i₄₂
              && old(i) <= i₄₂
              && i₄₂ < i
               ==> i₄₂ < 100000));
  {
    a8 := a8[i := a7[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall x₄₇: int ::
            ((exists i₄₆: int ::
                    x₄₇ == i₄₆
                    && old(i) <= i₄₆
                    && i₄₆ < i)
               ==> (exists i₄₆: int ::
                      i₄₆ < 100000
                      && x₄₇ == i₄₆
                      && old(i) <= i₄₆
                      && i₄₆ < i
                      && a9[x₄₇] == a8[i₄₆])))
      && (forall x₄₇: int ::
            (!((exists i₄₆: int ::
                    x₄₇ == i₄₆
                    && old(i) <= i₄₆
                    && i₄₆ < i)
            )
               ==> a9[x₄₇] == old(a9[x₄₇])))
      && (forall i₄₆: int ::
            (  old(i₄₆) <= i₄₆
              && old(i) <= i₄₆
              && i₄₆ < i
               ==> i₄₆ < 100000));
  {
    a9 := a9[i := a8[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall x₅₁: int ::
            ((exists i₅₀: int ::
                    x₅₁ == i₅₀
                    && old(i) <= i₅₀
                    && i₅₀ < i)
               ==> (exists i₅₀: int ::
                      i₅₀ < 100000
                      && x₅₁ == i₅₀
                      && old(i) <= i₅₀
                      && i₅₀ < i
                      && a0[x₅₁] == a9[i₅₀])))
      && (forall x₅₁: int ::
            (!((exists i₅₀: int ::
                    x₅₁ == i₅₀
                    && old(i) <= i₅₀
                    && i₅₀ < i)
            )
               ==> a0[x₅₁] == old(a0[x₅₁])))
      && (forall i₅₀: int ::
            (  old(i₅₀) <= i₅₀
              && old(i) <= i₅₀
              && i₅₀ < i
               ==> i₅₀ < 100000));
  {
    a0 := a0[i := a9[i]];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant true
      && old(x) <= x
      && x <= 100000
      && (forall x₅₅: int ::
            (  old(x₅₅) <= x₅₅
              && old(x) <= x₅₅
              && x₅₅ < x
               ==> x₅₅ < 100000));
  {
    assert a1[x] == a0[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

