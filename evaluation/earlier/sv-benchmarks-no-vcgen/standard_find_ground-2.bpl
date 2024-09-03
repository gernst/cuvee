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
  var __VERIFIER_nondet_int₁: int;
  var e: int;
  e := __VERIFIER_nondet_int₁;
  var j: int := 0;
  while(j < 100000)
    decreases 100000 - j;
    invariant true
      && 0 <= j
      && j <= 100000
      && (forall x₆: int ::
            ((exists j₅: int ::
                    x₆ == j₅
                    && 0 <= j₅
                    && j₅ < j)
               ==> (exists __VERIFIER_nondet_int₂₄: int, j₅: int ::
                      j₅ < 100000
                      && x₆ == j₅
                      && 0 <= j₅
                      && j₅ < j
                      && a[x₆] == __VERIFIER_nondet_int₂₄)))
      && (forall x₆: int ::
            (!((exists j₅: int ::
                    x₆ == j₅
                    && 0 <= j₅
                    && j₅ < j)
            )
               ==> a[x₆] == old(a[x₆])))
      && (forall j₅: int ::
            (  0 <= j₅
              && j₅ < j
               ==> j₅ < 100000));
  {
    var __VERIFIER_nondet_int₂: int;
    a := a[j := __VERIFIER_nondet_int₂];
    j := j + 1;
  }
  var i: int := 0;
  while(i < 100000 && a[i] != e)
    decreases 100000 - i;
    invariant true
      && 0 <= i
      && i <= 100000
      && (forall i₉: int ::
            (  0 <= i₉
              && i₉ < i
               ==> i₉ < 100000
                && a[i₉] != e));
  {
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < i)
    decreases i - x;
    invariant true
      && 0 <= x
      && x <= i
      && (forall x₁₂: int ::
            (  0 <= x₁₂
              && x₁₂ < x
               ==> x₁₂ < i));
  {
    assert a[x] != e;
    x := x + 1;
  }
  c#result := 0;
  return;
}

