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
  var c: [int]int;
  sum := sum[0 := 0];
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && 0 <= i
      && i <= N
      && (forall x₈: int ::
            ((exists i₇: int ::
                    x₈ == i₇
                    && 0 <= i₇
                    && i₇ < i)
               ==> (exists i₇: int ::
                      i₇ < N
                      && x₈ == i₇
                      && 0 <= i₇
                      && i₇ < i
                      && a[x₈] == 1)))
      && (forall x₈: int ::
            (!((exists i₇: int ::
                    x₈ == i₇
                    && 0 <= i₇
                    && i₇ < i)
            )
               ==> a[x₈] == old(a[x₈])))
      && (forall i₇: int ::
            (  0 <= i₇
              && i₇ < i
               ==> i₇ < N));
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
      && (forall x₁₂: int ::
            (x₁₂ == 0
               ==> (exists i₁₁: int ::
                      i₁₁ < N
                      && x₁₂ == 0
                      && sum[x₁₂] == old(sum)[0] + a[i₁₁])))
      && (forall x₁₂: int ::
            (x₁₂ != 0
               ==> sum[x₁₂] == old(sum[x₁₂])))
      && (forall i₁₁: int ::
            (  0 <= i₁₁
              && i₁₁ < i
               ==> i₁₁ < N));
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
      && (forall x₁₆: int ::
            ((exists i₁₅: int ::
                    x₁₆ == i₁₅
                    && 0 <= i₁₅
                    && i₁₅ < i)
               ==> (exists i₁₅: int ::
                      i₁₅ < N
                      && x₁₆ == i₁₅
                      && 0 <= i₁₅
                      && i₁₅ < i
                      && b[x₁₆] == 1)))
      && (forall x₁₆: int ::
            (!((exists i₁₅: int ::
                    x₁₆ == i₁₅
                    && 0 <= i₁₅
                    && i₁₅ < i)
            )
               ==> b[x₁₆] == old(b[x₁₆])))
      && (forall i₁₅: int ::
            (  0 <= i₁₅
              && i₁₅ < i
               ==> i₁₅ < N));
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
      && (forall x₂₀: int ::
            (x₂₀ == 0
               ==> (exists i₁₉: int ::
                      i₁₉ < N
                      && x₂₀ == 0
                      && sum[x₂₀] == b[i₁₉] + old(sum)[0])))
      && (forall x₂₀: int ::
            (x₂₀ != 0
               ==> sum[x₂₀] == old(sum[x₂₀])))
      && (forall i₁₉: int ::
            (  0 <= i₁₉
              && i₁₉ < i
               ==> i₁₉ < N));
  {
    sum := sum[0 := sum[0] + b[i]];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && 0 <= i
      && i <= N
      && (forall x₂₄: int ::
            ((exists i₂₃: int ::
                    x₂₄ == i₂₃
                    && 0 <= i₂₃
                    && i₂₃ < i)
               ==> (exists i₂₃: int ::
                      i₂₃ < N
                      && x₂₄ == i₂₃
                      && 0 <= i₂₃
                      && i₂₃ < i
                      && c[x₂₄] == 1)))
      && (forall x₂₄: int ::
            (!((exists i₂₃: int ::
                    x₂₄ == i₂₃
                    && 0 <= i₂₃
                    && i₂₃ < i)
            )
               ==> c[x₂₄] == old(c[x₂₄])))
      && (forall i₂₃: int ::
            (  0 <= i₂₃
              && i₂₃ < i
               ==> i₂₃ < N));
  {
    c := c[i := 1];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && 0 <= i
      && i <= N
      && (forall x₂₈: int ::
            (x₂₈ == 0
               ==> (exists i₂₇: int ::
                      i₂₇ < N
                      && x₂₈ == 0
                      && sum[x₂₈] == old(sum)[0] + c[i₂₇])))
      && (forall x₂₈: int ::
            (x₂₈ != 0
               ==> sum[x₂₈] == old(sum[x₂₈])))
      && (forall i₂₇: int ::
            (  0 <= i₂₇
              && i₂₇ < i
               ==> i₂₇ < N));
  {
    sum := sum[0 := sum[0] + c[i]];
    i := i + 1;
  }
  assert sum[0] <= 3 * N;
  c#result := 1;
  return;
}

