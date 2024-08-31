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
               ==> (exists __VERIFIER_nondet_int₁₆: int, a₈: int ::
                      a₈ < 100000
                      && x₉ == a₈
                      && old(a) <= a₈
                      && a₈ < a
                      && a1[x₉] == __VERIFIER_nondet_int₁₆)))
      && (forall x₉: int ::
            (!((exists a₈: int ::
                    x₉ == a₈
                    && old(a) <= a₈
                    && a₈ < a)
            )
               ==> a1[x₉] == old(a1[x₉])))
      && (forall x₁₀: int ::
            ((exists a₈: int ::
                    x₁₀ == a₈
                    && old(a) <= a₈
                    && a₈ < a)
               ==> (exists __VERIFIER_nondet_int₂₇: int, a₈: int ::
                      a₈ < 100000
                      && x₁₀ == a₈
                      && old(a) <= a₈
                      && a₈ < a
                      && a3[x₁₀] == __VERIFIER_nondet_int₂₇)))
      && (forall x₁₀: int ::
            (!((exists a₈: int ::
                    x₁₀ == a₈
                    && old(a) <= a₈
                    && a₈ < a)
            )
               ==> a3[x₁₀] == old(a3[x₁₀])))
      && (forall a₈: int ::
            (  old(a₈) <= a₈
              && old(a) <= a₈
              && a₈ < a
               ==> a₈ < 100000));
  {
    var __VERIFIER_nondet_int₁: int;
    a1 := a1[a := __VERIFIER_nondet_int₁];
    var __VERIFIER_nondet_int₂: int;
    a3 := a3[a := __VERIFIER_nondet_int₂];
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
                      && a4[x₂₀] == a2[i₁₉])))
      && (forall x₂₀: int ::
            (!((exists i₁₉: int ::
                    x₂₀ == i₁₉
                    && old(i) <= i₁₉
                    && i₁₉ < i)
            )
               ==> a4[x₂₀] == old(a4[x₂₀])))
      && (forall i₁₉: int ::
            (  old(i₁₉) <= i₁₉
              && old(i) <= i₁₉
              && i₁₉ < i
               ==> i₁₉ < 100000));
  {
    a4 := a4[i := a2[i]];
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
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant true
      && old(x) <= x
      && x <= 100000
      && (forall x₂₈: int ::
            (  old(x₂₈) <= x₂₈
              && old(x) <= x₂₈
              && x₂₈ < x
               ==> x₂₈ < 100000));
  {
    assert a1[x] == a4[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

