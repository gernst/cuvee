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
    invariant true
      && 0 <= i
      && i <= N
      && (forall i₉: int ::
            (  0 <= i₉
              && i₉ < i
               ==> i₉ < N));
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
    invariant true
      && 0 <= i
      && i <= N
      && (forall x₁₃: int ::
            ((exists i₁₂: int ::
                    x₁₃ == i₁₂
                    && 0 <= i₁₂
                    && i₁₂ < i)
               ==> (exists i₁₂: int ::
                      i₁₂ < N
                      && x₁₃ == i₁₂
                      && 0 <= i₁₂
                      && i₁₂ < i
                      && b[x₁₃] == a[i₁₂] + -j)))
      && (forall x₁₃: int ::
            (!((exists i₁₂: int ::
                    x₁₃ == i₁₂
                    && 0 <= i₁₂
                    && i₁₂ < i)
            )
               ==> b[x₁₃] == old(b[x₁₃])))
      && (forall i₁₂: int ::
            (  0 <= i₁₂
              && i₁₂ < i
               ==> i₁₂ < N));
  {
    b := b[i := a[i] - j];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && 0 <= i
      && i <= N
      && (forall i₁₇: int ::
            (  0 <= i₁₇
              && i₁₇ < i
               ==> i₁₇ < N));
  {
    k := k + b[i] + i;
    i := i + 1;
  }
  assert 0 <= k;
  c#result := 0;
  return;
}

