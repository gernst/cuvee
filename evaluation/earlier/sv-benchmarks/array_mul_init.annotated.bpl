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
  var k: int;
  var i: int;
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && i <= 100000
      && (forall i₅: int ::
            (  old(i) <= i₅
              && i₅ < i
               ==> i₅ < 100000
                && a[i₅] == i₅
                && b[i₅] == i₅))
      && (forall i₅: int ::
            (!(  old(i) <= i₅
              && i₅ < i
            )
               ==> a[i₅] == old(a)[i₅]
                && b[i₅] == old(b)[i₅]));
  {
    a := a[i := i];
    b := b[i := i];
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && i <= 100000
      && (forall i₁₂: int ::
            (  old(i) <= i₁₂
              && i₁₂ < i
               ==> (exists __VERIFIER_nondet_short₂₉: int, k₁₀: int ::
                        __VERIFIER_nondet_short₂₉ != 0
                        && i₁₂ < 100000
                        && a[i₁₂] == k₁₀
                        && b[i₁₂] == k₁₀ * k₁₀)
                || (exists __VERIFIER_nondet_short₂₉: int ::
                        __VERIFIER_nondet_short₂₉ == 0
                        && i₁₂ < 100000)))
      && (forall i₁₂: int ::
            (!(  old(i) <= i₁₂
              && i₁₂ < i
            )
               ==> a[i₁₂] == old(a)[i₁₂]
                && b[i₁₂] == old(b)[i₁₂]));
  {
    var __VERIFIER_nondet_short₂: int;
    if(__VERIFIER_nondet_short₂ != 0) {
      havoc k;
      a := a[i := k];
      b := b[i := k * k];
    }
    i := i + 1;
  }
  i := 0;
  while(i < 100000)
    decreases 100000 - i;
    invariant old(i) <= i
      && i <= 100000
      && (forall i₁₇: int ::
            (  old(i) <= i₁₇
              && i₁₇ < i
               ==> i₁₇ < 100000));
  {
    assert a[i] == b[i] || b[i] == a[i] * a[i];
    i := i + 1;
  }
}

