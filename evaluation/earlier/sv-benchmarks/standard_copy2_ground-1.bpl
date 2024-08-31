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
  var a: int;
  a := 0;
  while(a < 100000)
    decreases 100000 - a;
    invariant true
      && old(a) <= a
      && a <= 100000
      && (forall x₈: int ::
            ((exists a₇: int ::
                    x₈ == a₇
                    && old(a) <= a₇
                    && a₇ < a)
               ==> (exists __VERIFIER_nondet_int₁₅: int, a₇: int ::
                      a₇ < 100000
                      && x₈ == a₇
                      && old(a) <= a₇
                      && a₇ < a
                      && a1[x₈] == __VERIFIER_nondet_int₁₅)))
      && (forall x₈: int ::
            (!((exists a₇: int ::
                    x₈ == a₇
                    && old(a) <= a₇
                    && a₇ < a)
            )
               ==> a1[x₈] == old(a1[x₈])))
      && (forall x₉: int ::
            ((exists a₇: int ::
                    x₉ == a₇
                    && old(a) <= a₇
                    && a₇ < a)
               ==> (exists __VERIFIER_nondet_int₂₆: int, a₇: int ::
                      a₇ < 100000
                      && x₉ == a₇
                      && old(a) <= a₇
                      && a₇ < a
                      && a2[x₉] == __VERIFIER_nondet_int₂₆)))
      && (forall x₉: int ::
            (!((exists a₇: int ::
                    x₉ == a₇
                    && old(a) <= a₇
                    && a₇ < a)
            )
               ==> a2[x₉] == old(a2[x₉])))
      && (forall a₇: int ::
            (  old(a₇) <= a₇
              && old(a) <= a₇
              && a₇ < a
               ==> a₇ < 100000));
  {
    var __VERIFIER_nondet_int₁: int;
    a1 := a1[a := __VERIFIER_nondet_int₁];
    var __VERIFIER_nondet_int₂: int;
    a2 := a2[a := __VERIFIER_nondet_int₂];
    a := a + 1;
  }
  var i: int;
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall x₁₅: int ::
            ((exists i₁₄: int ::
                    x₁₅ == i₁₄
                    && old(i) <= i₁₄
                    && i₁₄ < i)
               ==> (exists i₁₄: int ::
                      i₁₄ < 100000
                      && x₁₅ == i₁₄
                      && old(i) <= i₁₄
                      && i₁₄ < i
                      && a3[x₁₅] == a1[i₁₄])))
      && (forall x₁₅: int ::
            (!((exists i₁₄: int ::
                    x₁₅ == i₁₄
                    && old(i) <= i₁₄
                    && i₁₄ < i)
            )
               ==> a3[x₁₅] == old(a3[x₁₅])))
      && (forall i₁₄: int ::
            (  old(i₁₄) <= i₁₄
              && old(i) <= i₁₄
              && i₁₄ < i
               ==> i₁₄ < 100000));
  {
    a3 := a3[i := a1[i]];
    i := i + 1;
  }
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
                      && a3[x₁₉] == a2[i₁₈])))
      && (forall x₁₉: int ::
            (!((exists i₁₈: int ::
                    x₁₉ == i₁₈
                    && old(i) <= i₁₈
                    && i₁₈ < i)
            )
               ==> a3[x₁₉] == old(a3[x₁₉])))
      && (forall i₁₈: int ::
            (  old(i₁₈) <= i₁₈
              && old(i) <= i₁₈
              && i₁₈ < i
               ==> i₁₈ < 100000));
  {
    a3 := a3[i := a2[i]];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant true
      && old(x) <= x
      && x <= 100000
      && (forall x₂₃: int ::
            (  old(x₂₃) <= x₂₃
              && old(x) <= x₂₃
              && x₂₃ < x
               ==> x₂₃ < 100000));
  {
    assert a1[x] == a3[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

