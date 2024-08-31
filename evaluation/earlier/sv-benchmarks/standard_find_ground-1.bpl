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
    invariant true
      && old(j) <= j
      && j <= 100000
      && (forall x₇: int ::
            ((exists j₆: int ::
                    x₇ == j₆
                    && old(j) <= j₆
                    && j₆ < j)
               ==> (exists __VERIFIER_nondet_int₂₅: int, j₆: int ::
                      j₆ < 100000
                      && x₇ == j₆
                      && old(j) <= j₆
                      && j₆ < j
                      && a[x₇] == __VERIFIER_nondet_int₂₅)))
      && (forall x₇: int ::
            (!((exists j₆: int ::
                    x₇ == j₆
                    && old(j) <= j₆
                    && j₆ < j)
            )
               ==> a[x₇] == old(a[x₇])))
      && (forall j₆: int ::
            (  old(j₆) <= j₆
              && old(j) <= j₆
              && j₆ < j
               ==> j₆ < 100000));
  {
    var __VERIFIER_nondet_int₂: int;
    a := a[j := __VERIFIER_nondet_int₂];
    j := j + 1;
  }
  while(i < 100000 && a[i] != e)
    decreases 100000 - i;
    invariant true
      && old(i) <= i
      && i <= 100000
      && (forall i₁₀: int ::
            (  old(i₁₀) <= i₁₀
              && old(i) <= i₁₀
              && i₁₀ < i
               ==> i₁₀ < 100000
                && a[i₁₀] != e));
  {
    i := i + 1;
  }
  var x: int;
  x := 0;
  while(x < i)
    decreases i - x;
    invariant true
      && old(x) <= x
      && x <= i
      && (forall x₁₃: int ::
            (  old(x₁₃) <= x₁₃
              && old(x) <= x₁₃
              && x₁₃ < x
               ==> x₁₃ < i));
  {
    assert a[x] != e;
    x := x + 1;
  }
  c#result := 0;
  return;
}

