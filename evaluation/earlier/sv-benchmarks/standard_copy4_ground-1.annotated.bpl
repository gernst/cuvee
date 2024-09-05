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
  var a: int;
  a := 0;
  while(a < 100000)
    decreases 100000 - a;
    invariant true
      && old(a) <= a
      && a <= 100000
      && (forall x₉: int ::
            ((exists a₈: int ::
                    x₉ == a₈
                    && old(a) <= a₈
                    && a₈ < a)
               ==> (exists __VERIFIER_nondet_int₁₇: int, a₈: int ::
                      a₈ < 100000
                      && x₉ == a₈
                      && old(a) <= a₈
                      && a₈ < a
                      && a1[x₉] == __VERIFIER_nondet_int₁₇)))
      && (forall x₉: int ::
            (!((exists a₈: int ::
                    x₉ == a₈
                    && old(a) <= a₈
                    && a₈ < a)
            )
               ==> a1[x₉] == old(a1[x₉])))
      && (forall a₈: int ::
            (  old(a) <= a₈
              && a₈ < a
               ==> a₈ < 100000));
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
      && (forall x₁₄: int ::
            ((exists i₁₃: int ::
                    x₁₄ == i₁₃
                    && old(i) <= i₁₃
                    && i₁₃ < i)
               ==> (exists i₁₃: int ::
                      i₁₃ < 100000
                      && x₁₄ == i₁₃
                      && old(i) <= i₁₃
                      && i₁₃ < i
                      && a2[x₁₄] == a1[i₁₃])))
      && (forall x₁₄: int ::
            (!((exists i₁₃: int ::
                    x₁₄ == i₁₃
                    && old(i) <= i₁₃
                    && i₁₃ < i)
            )
               ==> a2[x₁₄] == old(a2[x₁₄])))
      && (forall i₁₃: int ::
            (  old(i) <= i₁₃
              && i₁₃ < i
               ==> i₁₃ < 100000));
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
      && (forall x₁₈: int ::
            ((exists i₁₇: int ::
                    x₁₈ == i₁₇
                    && old(i) <= i₁₇
                    && i₁₇ < i)
               ==> (exists i₁₇: int ::
                      i₁₇ < 100000
                      && x₁₈ == i₁₇
                      && old(i) <= i₁₇
                      && i₁₇ < i
                      && a3[x₁₈] == a2[i₁₇])))
      && (forall x₁₈: int ::
            (!((exists i₁₇: int ::
                    x₁₈ == i₁₇
                    && old(i) <= i₁₇
                    && i₁₇ < i)
            )
               ==> a3[x₁₈] == old(a3[x₁₈])))
      && (forall i₁₇: int ::
            (  old(i) <= i₁₇
              && i₁₇ < i
               ==> i₁₇ < 100000));
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
      && (forall x₂₂: int ::
            ((exists i₂₁: int ::
                    x₂₂ == i₂₁
                    && old(i) <= i₂₁
                    && i₂₁ < i)
               ==> (exists i₂₁: int ::
                      i₂₁ < 100000
                      && x₂₂ == i₂₁
                      && old(i) <= i₂₁
                      && i₂₁ < i
                      && a4[x₂₂] == a3[i₂₁])))
      && (forall x₂₂: int ::
            (!((exists i₂₁: int ::
                    x₂₂ == i₂₁
                    && old(i) <= i₂₁
                    && i₂₁ < i)
            )
               ==> a4[x₂₂] == old(a4[x₂₂])))
      && (forall i₂₁: int ::
            (  old(i) <= i₂₁
              && i₂₁ < i
               ==> i₂₁ < 100000));
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
      && (forall x₂₆: int ::
            ((exists i₂₅: int ::
                    x₂₆ == i₂₅
                    && old(i) <= i₂₅
                    && i₂₅ < i)
               ==> (exists i₂₅: int ::
                      i₂₅ < 100000
                      && x₂₆ == i₂₅
                      && old(i) <= i₂₅
                      && i₂₅ < i
                      && a5[x₂₆] == a4[i₂₅])))
      && (forall x₂₆: int ::
            (!((exists i₂₅: int ::
                    x₂₆ == i₂₅
                    && old(i) <= i₂₅
                    && i₂₅ < i)
            )
               ==> a5[x₂₆] == old(a5[x₂₆])))
      && (forall i₂₅: int ::
            (  old(i) <= i₂₅
              && i₂₅ < i
               ==> i₂₅ < 100000));
  {
    a5 := a5[i := a4[i]];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant true
      && old(x) <= x
      && x <= 100000
      && (forall x₃₀: int ::
            (  old(x) <= x₃₀
              && x₃₀ < x
               ==> x₃₀ < 100000));
  {
    assert a1[x] == a5[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

