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
  var i: int := 0;
  var j: int;
  j := 0;
  while(j < 100000)
    decreases 100000 - j;
    invariant old(j) <= j
      && j <= 100000
      && (forall j₆: int ::
            (  old(j) <= j₆
              && j₆ < j
               ==> (exists __VERIFIER_nondet_int₂₅: int ::
                      j₆ < 100000
                      && a[j₆] == __VERIFIER_nondet_int₂₅)))
      && (forall j₆: int ::
            (!(  old(j) <= j₆
              && j₆ < j
            )
               ==> a[j₆] == old(a)[j₆]));
  {
    var __VERIFIER_nondet_int₂: int;
    a := a[j := __VERIFIER_nondet_int₂];
    j := j + 1;
  }
  while(i < 100000 && a[i] != e)
    decreases 100000 - i;
    invariant old(i) <= i
      && i <= 100000
      && (forall i₉: int ::
            (  old(i) <= i₉
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
    invariant old(x) <= x
      && x <= i
      && (forall x₁₂: int ::
            (  old(x) <= x₁₂
              && x₁₂ < x
               ==> x₁₂ < i));
  {
    assert a[x] != e;
    x := x + 1;
  }
  c#result := 0;
  return;
}

