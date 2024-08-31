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
  var a: int;
  a := 0;
  while(a < 100000)
    decreases 100000 - a;
    invariant true
      && old(a) <= a
      && a <= 100000
      && (forall x₇: int ::
            ((exists a₆: int ::
                    x₇ == a₆
                    && old(a) <= a₆
                    && a₆ < a)
               ==> (exists __VERIFIER_nondet_int₁₄: int, a₆: int ::
                      a₆ < 100000
                      && x₇ == a₆
                      && old(a) <= a₆
                      && a₆ < a
                      && a1[x₇] == __VERIFIER_nondet_int₁₄)))
      && (forall x₇: int ::
            (!((exists a₆: int ::
                    x₇ == a₆
                    && old(a) <= a₆
                    && a₆ < a)
            )
               ==> a1[x₇] == old(a1[x₇])))
      && (forall x₈: int ::
            ((exists a₆: int ::
                    x₈ == a₆
                    && old(a) <= a₆
                    && a₆ < a)
               ==> (exists __VERIFIER_nondet_int₂₅: int, a₆: int ::
                      a₆ < 100000
                      && x₈ == a₆
                      && old(a) <= a₆
                      && a₆ < a
                      && a2[x₈] == __VERIFIER_nondet_int₂₅)))
      && (forall x₈: int ::
            (!((exists a₆: int ::
                    x₈ == a₆
                    && old(a) <= a₆
                    && a₆ < a)
            )
               ==> a2[x₈] == old(a2[x₈])))
      && (forall a₆: int ::
            (  old(a₆) <= a₆
              && old(a) <= a₆
              && a₆ < a
               ==> a₆ < 100000));
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
                      && a1[x₁₄] == old(a1)[i₁₃])))
      && (forall x₁₄: int ::
            (!((exists i₁₃: int ::
                    x₁₄ == i₁₃
                    && old(i) <= i₁₃
                    && i₁₃ < i)
            )
               ==> a1[x₁₄] == old(a1[x₁₄])))
      && (forall i₁₃: int ::
            (  old(i₁₃) <= i₁₃
              && old(i) <= i₁₃
              && i₁₃ < i
               ==> i₁₃ < 100000));
  {
    a1 := a1[i := a1[i]];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant true
      && old(x) <= x
      && x <= 100000
      && (forall x₁₈: int ::
            (  old(x₁₈) <= x₁₈
              && old(x) <= x₁₈
              && x₁₈ < x
               ==> x₁₈ < 100000));
  {
    assert a1[x] == a2[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

