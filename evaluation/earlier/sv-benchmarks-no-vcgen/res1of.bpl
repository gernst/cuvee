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
      && 0 <= i
      && i <= N
      && (forall x₇: int ::
            ((exists i₆: int ::
                    x₇ == i₆
                    && 0 <= i₆
                    && i₆ < i)
               ==> (exists i₆: int ::
                      i₆ < N
                      && x₇ == i₆
                      && 0 <= i₆
                      && i₆ < i
                      && a[x₇] == 1)))
      && (forall x₇: int ::
            (!((exists i₆: int ::
                    x₇ == i₆
                    && 0 <= i₆
                    && i₆ < i)
            )
               ==> a[x₇] == old(a[x₇])))
      && (forall i₆: int ::
            (  0 <= i₆
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
      && 0 <= i
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
            (  0 <= i₁₀
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
      && 0 <= i
      && i <= N
      && (forall x₁₅: int ::
            ((exists i₁₄: int ::
                    x₁₅ == i₁₄
                    && 0 <= i₁₄
                    && i₁₄ < i)
               ==> (exists i₁₄: int ::
                      i₁₄ < N
                      && x₁₅ == i₁₄
                      && 0 <= i₁₄
                      && i₁₄ < i
                      && b[x₁₅] == 1)))
      && (forall x₁₅: int ::
            (!((exists i₁₄: int ::
                    x₁₅ == i₁₄
                    && 0 <= i₁₄
                    && i₁₄ < i)
            )
               ==> b[x₁₅] == old(b[x₁₅])))
      && (forall i₁₄: int ::
            (  0 <= i₁₄
              && i₁₄ < i
               ==> i₁₄ < N));
  {
    b := b[i := 1];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && 0 <= i
      && i <= N
      && (forall x₁₉: int ::
            (x₁₉ == 0
               ==> (exists i₁₈: int ::
                      i₁₈ < N
                      && x₁₉ == 0
                      && sum[x₁₉] == b[i₁₈] + old(sum)[0])))
      && (forall x₁₉: int ::
            (x₁₉ != 0
               ==> sum[x₁₉] == old(sum[x₁₉])))
      && (forall i₁₈: int ::
            (  0 <= i₁₈
              && i₁₈ < i
               ==> i₁₈ < N));
  {
    sum := sum[0 := sum[0] + b[i]];
    i := i + 1;
  }
  assert sum[0] <= N;
  c#result := 1;
  return;
}

