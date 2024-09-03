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
      && 0 <= i
      && i <= N
      && (forall x₅: int ::
            ((exists i₄: int ::
                    x₅ == i₄
                    && 0 <= i₄
                    && i₄ < i)
               ==> (exists i₄: int ::
                      i₄ < N
                      && x₅ == i₄
                      && 0 <= i₄
                      && i₄ < i
                      && a[x₅] == -1 + i₄ * i₄)))
      && (forall x₅: int ::
            (!((exists i₄: int ::
                    x₅ == i₄
                    && 0 <= i₄
                    && i₄ < i)
            )
               ==> a[x₅] == old(a[x₅])))
      && (forall i₄: int ::
            (  0 <= i₄
              && i₄ < i
               ==> i₄ < N));
  {
    a := a[i := (i - 1) * (i + 1)];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && 0 <= i
      && i <= N
      && (forall x₉: int ::
            ((exists i₈: int ::
                    x₉ == i₈
                    && 0 <= i₈
                    && i₈ < i)
               ==> (exists i₈: int ::
                      i₈ < N
                      && x₉ == i₈
                      && 0 <= i₈
                      && i₈ < i
                      && a[x₉] == old(a)[i₈] + -(i₈ * i₈))))
      && (forall x₉: int ::
            (!((exists i₈: int ::
                    x₉ == i₈
                    && 0 <= i₈
                    && i₈ < i)
            )
               ==> a[x₉] == old(a[x₉])))
      && (forall i₈: int ::
            (  0 <= i₈
              && i₈ < i
               ==> i₈ < N));
  {
    a := a[i := a[i] - i * i];
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
                      && a[x₁₃] == -1 + old(a)[i₁₂])))
      && (forall x₁₃: int ::
            (!((exists i₁₂: int ::
                    x₁₃ == i₁₂
                    && 0 <= i₁₂
                    && i₁₂ < i)
            )
               ==> a[x₁₃] == old(a[x₁₃])))
      && (forall i₁₂: int ::
            (  0 <= i₁₂
              && i₁₂ < i
               ==> i₁₂ < N));
  {
    a := a[i := a[i] - 1];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && 0 <= i
      && i <= N
      && (forall i₁₆: int ::
            (  0 <= i₁₆
              && i₁₆ < i
               ==> i₁₆ < N));
  {
    assert a[i] == 0;
    i := i + 1;
  }
  c#result := 1;
  return;
}

