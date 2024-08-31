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
  sum := sum[0 := 0];
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
               ==> (exists i₅: int ::
                      i₅ < N
                      && x₆ == i₅
                      && old(i) <= i₅
                      && i₅ < i
                      && a[x₆] == 1)))
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
    a := a[i := 1];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && old(i) <= i
      && i <= N
      && (forall x₁₀: int ::
            (x₁₀ == 0
               ==> (exists i₉: int ::
                      i₉ < N
                      && x₁₀ == 0
                      && sum[x₁₀] == a[i₉] + old(sum)[0])))
      && (forall x₁₀: int ::
            (x₁₀ != 0
               ==> sum[x₁₀] == old(sum[x₁₀])))
      && (forall i₉: int ::
            (  old(i₉) <= i₉
              && old(i) <= i₉
              && i₉ < i
               ==> i₉ < N));
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
      && (forall x₁₄: int ::
            ((exists i₁₃: int ::
                    x₁₄ == i₁₃
                    && old(i) <= i₁₃
                    && i₁₃ < i)
               ==> (exists i₁₃: int ::
                      i₁₃ < N
                      && x₁₄ == i₁₃
                      && old(i) <= i₁₃
                      && i₁₃ < i
                      && a[x₁₄] == sum[0] + old(a)[i₁₃])))
      && (forall x₁₄: int ::
            (!((exists i₁₃: int ::
                    x₁₄ == i₁₃
                    && old(i) <= i₁₃
                    && i₁₃ < i)
            )
               ==> a[x₁₄] == old(a[x₁₄])))
      && (forall i₁₃: int ::
            (  old(i₁₃) <= i₁₃
              && old(i) <= i₁₃
              && i₁₃ < i
               ==> i₁₃ < N));
  {
    a := a[i := a[i] + sum[0]];
    i := i + 1;
  }
  sum := sum[0 := 1];
  i := 0;
  while(i < N)
    decreases N - i;
    invariant true
      && old(i) <= i
      && i <= N
      && (forall x₁₈: int ::
            (x₁₈ == 0
               ==> (exists i₁₇: int ::
                      i₁₇ < N
                      && x₁₈ == 0
                      && sum[x₁₈] == a[i₁₇] + old(sum)[0])))
      && (forall x₁₈: int ::
            (x₁₈ != 0
               ==> sum[x₁₈] == old(sum[x₁₈])))
      && (forall i₁₇: int ::
            (  old(i₁₇) <= i₁₇
              && old(i) <= i₁₇
              && i₁₇ < i
               ==> i₁₇ < N));
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
      && (forall x₂₂: int ::
            ((exists i₂₁: int ::
                    x₂₂ == i₂₁
                    && old(i) <= i₂₁
                    && i₂₁ < i)
               ==> (exists i₂₁: int ::
                      i₂₁ < N
                      && x₂₂ == i₂₁
                      && old(i) <= i₂₁
                      && i₂₁ < i
                      && a[x₂₂] == old(a)[i₂₁] + sum[0])))
      && (forall x₂₂: int ::
            (!((exists i₂₁: int ::
                    x₂₂ == i₂₁
                    && old(i) <= i₂₁
                    && i₂₁ < i)
            )
               ==> a[x₂₂] == old(a[x₂₂])))
      && (forall i₂₁: int ::
            (  old(i₂₁) <= i₂₁
              && old(i) <= i₂₁
              && i₂₁ < i
               ==> i₂₁ < N));
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
      && (forall i₂₅: int ::
            (  old(i₂₅) <= i₂₅
              && old(i) <= i₂₅
              && i₂₅ < i
               ==> i₂₅ < N));
  {
    assert a[i] == (N + 1) * (N + 1);
    i := i + 1;
  }
  c#result := 1;
  return;
}

