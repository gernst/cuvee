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
      && 0 <= a
      && a <= 100000
      && (forall x₈: int ::
            ((exists a₇: int ::
                    x₈ == a₇
                    && 0 <= a₇
                    && a₇ < a)
               ==> (exists __VERIFIER_nondet_int₁₆: int, a₇: int ::
                      a₇ < 100000
                      && x₈ == a₇
                      && 0 <= a₇
                      && a₇ < a
                      && a1[x₈] == __VERIFIER_nondet_int₁₆)))
      && (forall x₈: int ::
            (!((exists a₇: int ::
                    x₈ == a₇
                    && 0 <= a₇
                    && a₇ < a)
            )
               ==> a1[x₈] == old(a1[x₈])))
      && (forall a₇: int ::
            (  0 <= a₇
              && a₇ < a
               ==> a₇ < 100000));
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
      && 0 <= i
      && i <= 100000
      && (forall x₁₃: int ::
            ((exists i₁₂: int ::
                    x₁₃ == i₁₂
                    && 0 <= i₁₂
                    && i₁₂ < i)
               ==> (exists i₁₂: int ::
                      i₁₂ < 100000
                      && x₁₃ == i₁₂
                      && 0 <= i₁₂
                      && i₁₂ < i
                      && a2[x₁₃] == a1[i₁₂])))
      && (forall x₁₃: int ::
            (!((exists i₁₂: int ::
                    x₁₃ == i₁₂
                    && 0 <= i₁₂
                    && i₁₂ < i)
            )
               ==> a2[x₁₃] == old(a2[x₁₃])))
      && (forall i₁₂: int ::
            (  0 <= i₁₂
              && i₁₂ < i
               ==> i₁₂ < 100000));
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
      && (forall x₁₇: int ::
            ((exists i₁₆: int ::
                    x₁₇ == i₁₆
                    && 0 <= i₁₆
                    && i₁₆ < i)
               ==> (exists i₁₆: int ::
                      i₁₆ < 100000
                      && x₁₇ == i₁₆
                      && 0 <= i₁₆
                      && i₁₆ < i
                      && a3[x₁₇] == a2[i₁₆])))
      && (forall x₁₇: int ::
            (!((exists i₁₆: int ::
                    x₁₇ == i₁₆
                    && 0 <= i₁₆
                    && i₁₆ < i)
            )
               ==> a3[x₁₇] == old(a3[x₁₇])))
      && (forall i₁₆: int ::
            (  0 <= i₁₆
              && i₁₆ < i
               ==> i₁₆ < 100000));
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
                      && a4[x₂₁] == a3[i₂₀])))
      && (forall x₂₁: int ::
            (!((exists i₂₀: int ::
                    x₂₁ == i₂₀
                    && 0 <= i₂₀
                    && i₂₀ < i)
            )
               ==> a4[x₂₁] == old(a4[x₂₁])))
      && (forall i₂₀: int ::
            (  0 <= i₂₀
              && i₂₀ < i
               ==> i₂₀ < 100000));
  {
    a4 := a4[i := a3[i]];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant true
      && 0 <= x
      && x <= 100000
      && (forall x₂₅: int ::
            (  0 <= x₂₅
              && x₂₅ < x
               ==> x₂₅ < 100000));
  {
    assert a1[x] == a4[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

