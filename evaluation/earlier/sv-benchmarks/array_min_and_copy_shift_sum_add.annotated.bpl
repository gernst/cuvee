data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure main()
  returns (c#result: int)
{
  var i: int;
  var __VERIFIER_nondet_int₁: int;
  var j: int;
  j := __VERIFIER_nondet_int₁;
  assume j < 10000 && -10000 < j;
  var k: int := 0;
  var __VERIFIER_nondet_int₂: int;
  var N: int;
  N := __VERIFIER_nondet_int₂;
  assume N < 10000 && -10000 < N;
  var a: [int]int;
  var b: [int]int;
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall j₈: int, i₉: int ::
            (  old(i) <= i₉
              && i₉ < i
               ==> a[i₉] < j₈
                  && a[i₉] < 10000
                  && -10000 < a[i₉]
                  && i₉ < N
                ||   !(a[i₉] < j₈
                  )
                  && a[i₉] < 10000
                  && -10000 < a[i₉]
                  && i₉ < N));
  {
    assume a[i] < 10000 && -10000 < a[i];
    if(a[i] < j) {
      j := a[i];
    }
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₁₂: int ::
            (  old(i) <= i₁₂
              && i₁₂ < i
               ==> i₁₂ < N
                && b[i₁₂] == a[i₁₂] + -j))
      && (forall i₁₂: int ::
            (!(  old(i) <= i₁₂
              && i₁₂ < i
            )
               ==> b[i₁₂] == old(b)[i₁₂]));
  {
    b := b[i := a[i] - j];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₁₆: int ::
            (  old(i) <= i₁₆
              && i₁₆ < i
               ==> i₁₆ < N));
  {
    k := k + b[i] + i;
    i := i + 1;
  }
  assert 0 <= k;
  c#result := 0;
  return;
}

