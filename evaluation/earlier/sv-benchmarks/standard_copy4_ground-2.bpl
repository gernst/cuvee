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
      && (forall x₁₀: int ::
            ((exists a₉: int ::
                    x₁₀ == a₉
                    && old(a) <= a₉
                    && a₉ < a)
               ==> (exists __VERIFIER_nondet_int₁₇: int, a₉: int ::
                      a₉ < 100000
                      && x₁₀ == a₉
                      && old(a) <= a₉
                      && a₉ < a
                      && a1[x₁₀] == __VERIFIER_nondet_int₁₇)))
      && (forall x₁₀: int ::
            (!((exists a₉: int ::
                    x₁₀ == a₉
                    && old(a) <= a₉
                    && a₉ < a)
            )
               ==> a1[x₁₀] == old(a1[x₁₀])))
      && (forall x₁₁: int ::
            ((exists a₉: int ::
                    x₁₁ == a₉
                    && old(a) <= a₉
                    && a₉ < a)
               ==> (exists __VERIFIER_nondet_int₂₈: int, a₉: int ::
                      a₉ < 100000
                      && x₁₁ == a₉
                      && old(a) <= a₉
                      && a₉ < a
                      && a4[x₁₁] == __VERIFIER_nondet_int₂₈)))
      && (forall x₁₁: int ::
            (!((exists a₉: int ::
                    x₁₁ == a₉
                    && old(a) <= a₉
                    && a₉ < a)
            )
               ==> a4[x₁₁] == old(a4[x₁₁])))
      && (forall a₉: int ::
            (  old(a₉) <= a₉
              && old(a) <= a₉
              && a₉ < a
               ==> a₉ < 100000));
  {
    var __VERIFIER_nondet_int₁: int;
    a1 := a1[a := __VERIFIER_nondet_int₁];
    var __VERIFIER_nondet_int₂: int;
    a4 := a4[a := __VERIFIER_nondet_int₂];
    a := a + 1;
  }
  var i: int;
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall x₁₇: int ::
            ((exists i₁₆: int ::
                    x₁₇ == i₁₆
                    && old(i) <= i₁₆
                    && i₁₆ < i)
               ==> (exists i₁₆: int ::
                      i₁₆ < 100000
                      && x₁₇ == i₁₆
                      && old(i) <= i₁₆
                      && i₁₆ < i
                      && a2[x₁₇] == a1[i₁₆])))
      && (forall x₁₇: int ::
            (!((exists i₁₆: int ::
                    x₁₇ == i₁₆
                    && old(i) <= i₁₆
                    && i₁₆ < i)
            )
               ==> a2[x₁₇] == old(a2[x₁₇])))
      && (forall i₁₆: int ::
            (  old(i₁₆) <= i₁₆
              && old(i) <= i₁₆
              && i₁₆ < i
               ==> i₁₆ < 100000));
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
      && (forall x₂₁: int ::
            ((exists i₂₀: int ::
                    x₂₁ == i₂₀
                    && old(i) <= i₂₀
                    && i₂₀ < i)
               ==> (exists i₂₀: int ::
                      i₂₀ < 100000
                      && x₂₁ == i₂₀
                      && old(i) <= i₂₀
                      && i₂₀ < i
                      && a3[x₂₁] == a2[i₂₀])))
      && (forall x₂₁: int ::
            (!((exists i₂₀: int ::
                    x₂₁ == i₂₀
                    && old(i) <= i₂₀
                    && i₂₀ < i)
            )
               ==> a3[x₂₁] == old(a3[x₂₁])))
      && (forall i₂₀: int ::
            (  old(i₂₀) <= i₂₀
              && old(i) <= i₂₀
              && i₂₀ < i
               ==> i₂₀ < 100000));
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
      && (forall x₂₅: int ::
            ((exists i₂₄: int ::
                    x₂₅ == i₂₄
                    && old(i) <= i₂₄
                    && i₂₄ < i)
               ==> (exists i₂₄: int ::
                      i₂₄ < 100000
                      && x₂₅ == i₂₄
                      && old(i) <= i₂₄
                      && i₂₄ < i
                      && a5[x₂₅] == a3[i₂₄])))
      && (forall x₂₅: int ::
            (!((exists i₂₄: int ::
                    x₂₅ == i₂₄
                    && old(i) <= i₂₄
                    && i₂₄ < i)
            )
               ==> a5[x₂₅] == old(a5[x₂₅])))
      && (forall i₂₄: int ::
            (  old(i₂₄) <= i₂₄
              && old(i) <= i₂₄
              && i₂₄ < i
               ==> i₂₄ < 100000));
  {
    a5 := a5[i := a3[i]];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall x₂₉: int ::
            ((exists i₂₈: int ::
                    x₂₉ == i₂₈
                    && old(i) <= i₂₈
                    && i₂₈ < i)
               ==> (exists i₂₈: int ::
                      i₂₈ < 100000
                      && x₂₉ == i₂₈
                      && old(i) <= i₂₈
                      && i₂₈ < i
                      && a5[x₂₉] == a4[i₂₈])))
      && (forall x₂₉: int ::
            (!((exists i₂₈: int ::
                    x₂₉ == i₂₈
                    && old(i) <= i₂₈
                    && i₂₈ < i)
            )
               ==> a5[x₂₉] == old(a5[x₂₉])))
      && (forall i₂₈: int ::
            (  old(i₂₈) <= i₂₈
              && old(i) <= i₂₈
              && i₂₈ < i
               ==> i₂₈ < 100000));
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
      && (forall x₃₃: int ::
            (  old(x₃₃) <= x₃₃
              && old(x) <= x₃₃
              && x₃₃ < x
               ==> x₃₃ < 100000));
  {
    assert a1[x] == a5[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

