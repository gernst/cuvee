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
  var sum: [int]int;
  var a: [int]int;
  var b: [int]int;
  sum := sum[0 := 0];
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && old(i) <= i
      && i <= N
      && (forall x₇: int ::
            ((exists i₆: int ::
                    x₇ == i₆
                    && old(i) <= i₆
                    && i₆ < i)
               ==> (exists i₆: int ::
                      i₆ < N
                      && x₇ == i₆
                      && old(i) <= i₆
                      && i₆ < i
                      && a[x₇] == 1)))
      && (forall x₇: int ::
            (!((exists i₆: int ::
                    x₇ == i₆
                    && old(i) <= i₆
                    && i₆ < i)
            )
               ==> a[x₇] == old(a[x₇])))
      && (forall i₆: int ::
            (  old(i₆) <= i₆
              && old(i) <= i₆
              && i₆ < i
               ==> i₆ < N));
  {
    a := a[i := 1];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && old(i) <= i
      && i <= N
      && (forall x₁₁: int ::
            (x₁₁ == 0
               ==> (exists i₁₀: int ::
                      i₁₀ < N
                      && x₁₁ == 0
                      && sum[x₁₁] == old(sum)[0] + a[i₁₀])))
      && (forall x₁₁: int ::
            (x₁₁ != 0
               ==> sum[x₁₁] == old(sum[x₁₁])))
      && (forall i₁₀: int ::
            (  old(i₁₀) <= i₁₀
              && old(i) <= i₁₀
              && i₁₀ < i
               ==> i₁₀ < N));
  {
    sum := sum[0 := sum[0] + a[i]];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && old(i) <= i
      && i <= N
      && (forall x₁₅: int ::
            ((exists i₁₄: int ::
                    x₁₅ == i₁₄
                    && old(i) <= i₁₄
                    && i₁₄ < i)
               ==> (exists i₁₄: int ::
                      i₁₄ < N
                      && x₁₅ == i₁₄
                      && old(i) <= i₁₄
                      && i₁₄ < i
                      && a[x₁₅] == old(a)[i₁₄] + sum[0])))
      && (forall x₁₅: int ::
            (!((exists i₁₄: int ::
                    x₁₅ == i₁₄
                    && old(i) <= i₁₄
                    && i₁₄ < i)
            )
               ==> a[x₁₅] == old(a[x₁₅])))
      && (forall i₁₄: int ::
            (  old(i₁₄) <= i₁₄
              && old(i) <= i₁₄
              && i₁₄ < i
               ==> i₁₄ < N));
  {
    a := a[i := a[i] + sum[0]];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && old(i) <= i
      && i <= N
      && (forall x₁₉: int ::
            ((exists i₁₈: int ::
                    x₁₉ == i₁₈
                    && old(i) <= i₁₈
                    && i₁₈ < i)
               ==> (exists i₁₈: int ::
                      i₁₈ < N
                      && x₁₉ == i₁₈
                      && old(i) <= i₁₈
                      && i₁₈ < i
                      && b[x₁₉] == 1 + a[i₁₈])))
      && (forall x₁₉: int ::
            (!((exists i₁₈: int ::
                    x₁₉ == i₁₈
                    && old(i) <= i₁₈
                    && i₁₈ < i)
            )
               ==> b[x₁₉] == old(b[x₁₉])))
      && (forall i₁₈: int ::
            (  old(i₁₈) <= i₁₈
              && old(i) <= i₁₈
              && i₁₈ < i
               ==> i₁₈ < N));
  {
    b := b[i := a[i] + 1];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && old(i) <= i
      && i <= N
      && (forall i₂₂: int ::
            (  old(i₂₂) <= i₂₂
              && old(i) <= i₂₂
              && i₂₂ < i
               ==> i₂₂ < N));
  {
    assert b[i] == N + 2;
    i := i + 1;
  }
  c#result := 1;
  return;
}

