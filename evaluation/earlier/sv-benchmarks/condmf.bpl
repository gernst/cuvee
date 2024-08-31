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
      && (forall x₅: int ::
            ((exists i₄: int ::
                    x₅ == i₄
                    && old(i) <= i₄
                    && i₄ < i)
               ==> (exists i₄: int ::
                      i₄ < N
                      && x₅ == i₄
                      && old(i) <= i₄
                      && i₄ < i
                      && a[x₅] == 0)))
      && (forall x₅: int ::
            (!((exists i₄: int ::
                    x₅ == i₄
                    && old(i) <= i₄
                    && i₄ < i)
            )
               ==> a[x₅] == old(a[x₅])))
      && (forall i₄: int ::
            (  old(i₄) <= i₄
              && old(i) <= i₄
              && i₄ < i
               ==> i₄ < N));
  {
    a := a[i := 0];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && old(i) <= i
      && i <= N
      && (forall x₉: int ::
            ((exists i₈: int ::
                    x₉ == i₈
                    && old(i) <= i₈
                    && i₈ < i)
               ==> (exists i₈: int ::
                        N % 2 == 1
                        && i₈ < N
                        && x₉ == i₈
                        && old(i) <= i₈
                        && i₈ < i
                        && a[x₉] == 2 + old(a)[i₈])
                || (exists i₈: int ::
                        N % 2 != 1
                        && i₈ < N
                        && x₉ == i₈
                        && old(i) <= i₈
                        && i₈ < i
                        && a[x₉] == 1 + old(a)[i₈])))
      && (forall x₉: int ::
            (!((exists i₈: int ::
                    x₉ == i₈
                    && old(i) <= i₈
                    && i₈ < i)
            )
               ==> a[x₉] == old(a[x₉])))
      && (forall i₈: int ::
            (  old(i₈) <= i₈
              && old(i) <= i₈
              && i₈ < i
               ==> i₈ < N));
  {
    if(N % 2 == 1) {
      a := a[i := a[i] + 2];
    } else {
      a := a[i := a[i] + 1];
    }
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && old(i) <= i
      && i <= N
      && (forall i₁₂: int ::
            (  old(i₁₂) <= i₁₂
              && old(i) <= i₁₂
              && i₁₂ < i
               ==> i₁₂ < N));
  {
    assert a[i] % 2 == N % 2;
    i := i + 1;
  }
  c#result := 1;
  return;
}

