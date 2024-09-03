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
  var sum: [int]int;
  sum := sum[0 := 1];
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && 0 <= i
      && i <= N
      && (forall x₆: int ::
            ((exists i₅: int ::
                    x₆ == i₅
                    && 0 <= i₅
                    && i₅ < i)
               ==> (exists i₅: int ::
                      i₅ < N
                      && x₆ == i₅
                      && 0 <= i₅
                      && i₅ < i
                      && a[x₆] == 1 + i₅ * i₅ + 2 * i₅)))
      && (forall x₆: int ::
            (!((exists i₅: int ::
                    x₆ == i₅
                    && 0 <= i₅
                    && i₅ < i)
            )
               ==> a[x₆] == old(a[x₆])))
      && (forall i₅: int ::
            (  0 <= i₅
              && i₅ < i
               ==> i₅ < N));
  {
    a := a[i := (i + 1) * (i + 1)];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && 0 <= i
      && i <= N
      && (forall x₁₀: int ::
            ((exists i₉: int ::
                    x₁₀ == i₉
                    && 0 <= i₉
                    && i₉ < i)
               ==> (exists i₉: int ::
                      i₉ < N
                      && x₁₀ == i₉
                      && 0 <= i₉
                      && i₉ < i
                      && a[x₁₀] == -(i₉ * i₉) + old(a)[i₉])))
      && (forall x₁₀: int ::
            (!((exists i₉: int ::
                    x₁₀ == i₉
                    && 0 <= i₉
                    && i₉ < i)
            )
               ==> a[x₁₀] == old(a[x₁₀])))
      && (forall i₉: int ::
            (  0 <= i₉
              && i₉ < i
               ==> i₉ < N));
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
      && (forall x₁₄: int ::
            ((exists i₁₃: int ::
                    x₁₄ == i₁₃
                    && 0 <= i₁₃
                    && i₁₃ < i)
               ==> (exists i₁₃: int ::
                      i₁₃ < N
                      && x₁₄ == i₁₃
                      && 0 <= i₁₃
                      && i₁₃ < i
                      && a[x₁₄] == -i₁₃ + old(a)[i₁₃])))
      && (forall x₁₄: int ::
            (!((exists i₁₃: int ::
                    x₁₄ == i₁₃
                    && 0 <= i₁₃
                    && i₁₃ < i)
            )
               ==> a[x₁₄] == old(a[x₁₄])))
      && (forall i₁₃: int ::
            (  0 <= i₁₃
              && i₁₃ < i
               ==> i₁₃ < N));
  {
    a := a[i := a[i] - i];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && 0 <= i
      && i <= N
      && (forall x₁₈: int ::
            ((exists i₁₇: int ::
                    x₁₈ == i₁₇
                    && 0 <= i₁₇
                    && i₁₇ < i)
               ==> (exists i₁₇: int ::
                      i₁₇ < N
                      && x₁₈ == i₁₇
                      && 0 <= i₁₇
                      && i₁₇ < i
                      && a[x₁₈] == -i₁₇ + old(a)[i₁₇])))
      && (forall x₁₈: int ::
            (!((exists i₁₇: int ::
                    x₁₈ == i₁₇
                    && 0 <= i₁₇
                    && i₁₇ < i)
            )
               ==> a[x₁₈] == old(a[x₁₈])))
      && (forall i₁₇: int ::
            (  0 <= i₁₇
              && i₁₇ < i
               ==> i₁₇ < N));
  {
    a := a[i := a[i] - i];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && 0 <= i
      && i <= N
      && (forall x₂₂: int ::
            (x₂₂ == 0
               ==> (exists i₂₁: int ::
                      i₂₁ < N
                      && x₂₂ == 0
                      && sum[x₂₂] == old(sum)[0] + a[i₂₁])))
      && (forall x₂₂: int ::
            (x₂₂ != 0
               ==> sum[x₂₂] == old(sum[x₂₂])))
      && (forall i₂₁: int ::
            (  0 <= i₂₁
              && i₂₁ < i
               ==> i₂₁ < N));
  {
    sum := sum[0 := sum[0] + a[i]];
    i := i + 1;
  }
  assert sum[0] == N;
  c#result := 1;
  return;
}

