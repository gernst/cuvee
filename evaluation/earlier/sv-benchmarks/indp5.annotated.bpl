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
  sum := sum[0 := 0];
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₅: int ::
            (  old(i) <= i₅
              && i₅ < i
               ==> i₅ < N
                && a[i₅] == 1 + i₅ * i₅ + 2 * i₅))
      && (forall i₅: int ::
            (!(  old(i) <= i₅
              && i₅ < i
            )
               ==> a[i₅] == old(a)[i₅]));
  {
    a := a[i := (i + 1) * (i + 1)];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₈: int ::
            (  old(i) <= i₈
              && i₈ < i
               ==> i₈ < N
                && a[i₈] == -(i₈ * i₈) + old(a)[i₈]))
      && (forall i₈: int ::
            (!(  old(i) <= i₈
              && i₈ < i
            )
               ==> a[i₈] == old(a)[i₈]));
  {
    a := a[i := a[i] - i * i];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₁₁: int ::
            (  old(i) <= i₁₁
              && i₁₁ < i
               ==> i₁₁ < N
                && a[i₁₁] == -i₁₁ + old(a)[i₁₁]))
      && (forall i₁₁: int ::
            (!(  old(i) <= i₁₁
              && i₁₁ < i
            )
               ==> a[i₁₁] == old(a)[i₁₁]));
  {
    a := a[i := a[i] - i];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₁₄: int ::
            (  old(i) <= i₁₄
              && i₁₄ < i
               ==> i₁₄ < N
                && a[i₁₄] == old(a)[i₁₄] + -i₁₄))
      && (forall i₁₄: int ::
            (!(  old(i) <= i₁₄
              && i₁₄ < i
            )
               ==> a[i₁₄] == old(a)[i₁₄]));
  {
    a := a[i := a[i] - i];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₁₇: int ::
            (  old(i) <= i₁₇
              && i₁₇ < i
               ==> i₁₇ < N
                && sum[0] == a[i₁₇] + old(sum)[0]))
      && (forall i₁₇: int ::
            (!(  old(i) <= i₁₇
              && i₁₇ < i
            )
               ==> sum[0] == old(sum)[0]));
  {
    sum := sum[0 := sum[0] + a[i]];
    i := i + 1;
  }
  assert sum[0] == N;
  c#result := 1;
  return;
}

