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
      && (forall x₁₁: int ::
            ((exists a₁₀: int ::
                    x₁₁ == a₁₀
                    && old(a) <= a₁₀
                    && a₁₀ < a)
               ==> (exists __VERIFIER_nondet_int₁₉: int, a₁₀: int ::
                      a₁₀ < 100000
                      && x₁₁ == a₁₀
                      && old(a) <= a₁₀
                      && a₁₀ < a
                      && a1[x₁₁] == __VERIFIER_nondet_int₁₉)))
      && (forall x₁₁: int ::
            (!((exists a₁₀: int ::
                    x₁₁ == a₁₀
                    && old(a) <= a₁₀
                    && a₁₀ < a)
            )
               ==> a1[x₁₁] == old(a1[x₁₁])))
      && (forall a₁₀: int ::
            (  old(a₁₀) <= a₁₀
              && old(a) <= a₁₀
              && a₁₀ < a
               ==> a₁₀ < 100000));
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
      && (forall x₁₆: int ::
            ((exists i₁₅: int ::
                    x₁₆ == i₁₅
                    && old(i) <= i₁₅
                    && i₁₅ < i)
               ==> (exists i₁₅: int ::
                      i₁₅ < 100000
                      && x₁₆ == i₁₅
                      && old(i) <= i₁₅
                      && i₁₅ < i
                      && a2[x₁₆] == a1[i₁₅])))
      && (forall x₁₆: int ::
            (!((exists i₁₅: int ::
                    x₁₆ == i₁₅
                    && old(i) <= i₁₅
                    && i₁₅ < i)
            )
               ==> a2[x₁₆] == old(a2[x₁₆])))
      && (forall i₁₅: int ::
            (  old(i₁₅) <= i₁₅
              && old(i) <= i₁₅
              && i₁₅ < i
               ==> i₁₅ < 100000));
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
      && (forall x₂₀: int ::
            ((exists i₁₉: int ::
                    x₂₀ == i₁₉
                    && old(i) <= i₁₉
                    && i₁₉ < i)
               ==> (exists i₁₉: int ::
                      i₁₉ < 100000
                      && x₂₀ == i₁₉
                      && old(i) <= i₁₉
                      && i₁₉ < i
                      && a3[x₂₀] == a2[i₁₉])))
      && (forall x₂₀: int ::
            (!((exists i₁₉: int ::
                    x₂₀ == i₁₉
                    && old(i) <= i₁₉
                    && i₁₉ < i)
            )
               ==> a3[x₂₀] == old(a3[x₂₀])))
      && (forall i₁₉: int ::
            (  old(i₁₉) <= i₁₉
              && old(i) <= i₁₉
              && i₁₉ < i
               ==> i₁₉ < 100000));
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
      && (forall x₂₄: int ::
            ((exists i₂₃: int ::
                    x₂₄ == i₂₃
                    && old(i) <= i₂₃
                    && i₂₃ < i)
               ==> (exists i₂₃: int ::
                      i₂₃ < 100000
                      && x₂₄ == i₂₃
                      && old(i) <= i₂₃
                      && i₂₃ < i
                      && a4[x₂₄] == a3[i₂₃])))
      && (forall x₂₄: int ::
            (!((exists i₂₃: int ::
                    x₂₄ == i₂₃
                    && old(i) <= i₂₃
                    && i₂₃ < i)
            )
               ==> a4[x₂₄] == old(a4[x₂₄])))
      && (forall i₂₃: int ::
            (  old(i₂₃) <= i₂₃
              && old(i) <= i₂₃
              && i₂₃ < i
               ==> i₂₃ < 100000));
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
      && (forall x₂₈: int ::
            ((exists i₂₇: int ::
                    x₂₈ == i₂₇
                    && old(i) <= i₂₇
                    && i₂₇ < i)
               ==> (exists i₂₇: int ::
                      i₂₇ < 100000
                      && x₂₈ == i₂₇
                      && old(i) <= i₂₇
                      && i₂₇ < i
                      && a5[x₂₈] == a4[i₂₇])))
      && (forall x₂₈: int ::
            (!((exists i₂₇: int ::
                    x₂₈ == i₂₇
                    && old(i) <= i₂₇
                    && i₂₇ < i)
            )
               ==> a5[x₂₈] == old(a5[x₂₈])))
      && (forall i₂₇: int ::
            (  old(i₂₇) <= i₂₇
              && old(i) <= i₂₇
              && i₂₇ < i
               ==> i₂₇ < 100000));
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
      && (forall x₃₂: int ::
            ((exists i₃₁: int ::
                    x₃₂ == i₃₁
                    && old(i) <= i₃₁
                    && i₃₁ < i)
               ==> (exists i₃₁: int ::
                      i₃₁ < 100000
                      && x₃₂ == i₃₁
                      && old(i) <= i₃₁
                      && i₃₁ < i
                      && a6[x₃₂] == a5[i₃₁])))
      && (forall x₃₂: int ::
            (!((exists i₃₁: int ::
                    x₃₂ == i₃₁
                    && old(i) <= i₃₁
                    && i₃₁ < i)
            )
               ==> a6[x₃₂] == old(a6[x₃₂])))
      && (forall i₃₁: int ::
            (  old(i₃₁) <= i₃₁
              && old(i) <= i₃₁
              && i₃₁ < i
               ==> i₃₁ < 100000));
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
      && (forall x₃₆: int ::
            ((exists i₃₅: int ::
                    x₃₆ == i₃₅
                    && old(i) <= i₃₅
                    && i₃₅ < i)
               ==> (exists i₃₅: int ::
                      i₃₅ < 100000
                      && x₃₆ == i₃₅
                      && old(i) <= i₃₅
                      && i₃₅ < i
                      && a7[x₃₆] == a6[i₃₅])))
      && (forall x₃₆: int ::
            (!((exists i₃₅: int ::
                    x₃₆ == i₃₅
                    && old(i) <= i₃₅
                    && i₃₅ < i)
            )
               ==> a7[x₃₆] == old(a7[x₃₆])))
      && (forall i₃₅: int ::
            (  old(i₃₅) <= i₃₅
              && old(i) <= i₃₅
              && i₃₅ < i
               ==> i₃₅ < 100000));
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
      && (forall x₄₀: int ::
            (  old(x₄₀) <= x₄₀
              && old(x) <= x₄₀
              && x₄₀ < x
               ==> x₄₀ < 100000));
  {
    assert a1[x] == a7[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

