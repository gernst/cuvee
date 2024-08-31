data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

procedure malloc(size: int) returns (c#result: c#ptr<c#void>);

var N: int;

procedure main()
  returns (c#result: int)
  modifies N;
{
  havoc N;
  if(N <= 0) {
    c#result := 1;
    return;
  }
  assume N <= 2147483647 / 4;
  var i: int;
  var a: [int]int;
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && old(i) <= i
      && i <= N
      && (forall x₆: int ::
            ((exists i₅: int ::
                    x₆ == i₅
                    && old(i) <= i₅
                    && i₅ < i)
               ==> (exists __VERIFIER_nondet_int₁₄: int, i₅: int ::
                      i₅ < N
                      && x₆ == i₅
                      && old(i) <= i₅
                      && i₅ < i
                      && a[x₆] == __VERIFIER_nondet_int₁₄)))
      && (forall x₆: int ::
            (!((exists i₅: int ::
                    x₆ == i₅
                    && old(i) <= i₅
                    && i₅ < i)
            )
               ==> a[x₆] == old(a[x₆])))
      && (forall i₅: int ::
            (  old(i₅) <= i₅
              && old(i) <= i₅
              && i₅ < i
               ==> i₅ < N));
  {
    var __VERIFIER_nondet_int₁: int;
    a := a[i := __VERIFIER_nondet_int₁];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && old(i) <= i
      && i <= N
      && (forall x₁₀: int ::
            ((exists i₉: int ::
                    x₁₀ == i₉
                    && old(i) <= i₉
                    && i₉ < i)
               ==> (exists i₉: int ::
                        a[i₉] < N
                        && i₉ < N
                        && x₁₀ == i₉
                        && old(i) <= i₉
                        && i₉ < i
                        && a[x₁₀] == old(a)[i₉])
                || (exists i₉: int ::
                        !(a[i₉] < N
                        )
                        && i₉ < N
                        && x₁₀ == i₉
                        && old(i) <= i₉
                        && i₉ < i
                        && a[x₁₀] == N)))
      && (forall x₁₀: int ::
            (!((exists i₉: int ::
                    x₁₀ == i₉
                    && old(i) <= i₉
                    && i₉ < i)
            )
               ==> a[x₁₀] == old(a[x₁₀])))
      && (forall i₉: int ::
            (  old(i₉) <= i₉
              && old(i) <= i₉
              && i₉ < i
               ==> i₉ < N));
  {
    if(a[i] < N) {
      a := a[i := a[i]];
    } else {
      a := a[i := N];
    }
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && old(i) <= i
      && i <= N
      && (forall i₁₃: int ::
            (  old(i₁₃) <= i₁₃
              && old(i) <= i₁₃
              && i₁₃ < i
               ==> i₁₃ < N));
  {
    assert a[i] <= N;
    i := i + 1;
  }
  c#result := 1;
  return;
}

