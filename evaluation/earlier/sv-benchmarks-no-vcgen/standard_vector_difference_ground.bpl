data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var a: [int]int;
  var b: [int]int;
  var c: [int]int;
  var i: int := 0;
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant true
      && 0 <= i
      && i <= 100000
      && (forall x₇: int ::
            ((exists i₆: int ::
                    x₇ == i₆
                    && 0 <= i₆
                    && i₆ < i)
               ==> (exists __VERIFIER_nondet_int₁₄: int, i₆: int ::
                      i₆ < 100000
                      && x₇ == i₆
                      && 0 <= i₆
                      && i₆ < i
                      && a[x₇] == __VERIFIER_nondet_int₁₄)))
      && (forall x₇: int ::
            (!((exists i₆: int ::
                    x₇ == i₆
                    && 0 <= i₆
                    && i₆ < i)
            )
               ==> a[x₇] == old(a[x₇])))
      && (forall x₈: int ::
            ((exists i₆: int ::
                    x₈ == i₆
                    && 0 <= i₆
                    && i₆ < i)
               ==> (exists __VERIFIER_nondet_int₂₅: int, i₆: int ::
                      i₆ < 100000
                      && x₈ == i₆
                      && 0 <= i₆
                      && i₆ < i
                      && b[x₈] == __VERIFIER_nondet_int₂₅)))
      && (forall x₈: int ::
            (!((exists i₆: int ::
                    x₈ == i₆
                    && 0 <= i₆
                    && i₆ < i)
            )
               ==> b[x₈] == old(b[x₈])))
      && (forall i₆: int ::
            (  0 <= i₆
              && i₆ < i
               ==> i₆ < 100000));
  {
    var __VERIFIER_nondet_int₁: int;
    a := a[i := __VERIFIER_nondet_int₁];
    var __VERIFIER_nondet_int₂: int;
    b := b[i := __VERIFIER_nondet_int₂];
    i := i + 1;
  }
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
                      && c[x₁₃] == a[i₁₂] + -b[i₁₂])))
      && (forall x₁₃: int ::
            (!((exists i₁₂: int ::
                    x₁₃ == i₁₂
                    && 0 <= i₁₂
                    && i₁₂ < i)
            )
               ==> c[x₁₃] == old(c[x₁₃])))
      && (forall i₁₂: int ::
            (  0 <= i₁₂
              && i₁₂ < i
               ==> i₁₂ < 100000));
  {
    c := c[i := a[i] - b[i]];
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < 100000)
    decreases 100000 - x;
    invariant true
      && 0 <= x
      && x <= 100000
      && (forall x₁₇: int ::
            (  0 <= x₁₇
              && x₁₇ < x
               ==> x₁₇ < 100000));
  {
    assert c[x] == a[x] - b[x];
    x := x + 1;
  }
  c#result := 0;
  return;
}

