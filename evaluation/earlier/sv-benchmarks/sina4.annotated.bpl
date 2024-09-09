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
    invariant old(i) <= i
      && (forall i₆: int ::
            (  old(i) <= i₆
              && i₆ < i
               ==> i₆ < N
                && a[i₆] == 1))
      && (forall i₆: int ::
            (!(  old(i) <= i₆
              && i₆ < i
            )
               ==> a[i₆] == old(a)[i₆]));
  {
    a := a[i := 1];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₉: int ::
            (  old(i) <= i₉
              && i₉ < i
               ==> i₉ < N
                && sum[0] == a[i₉] + old(sum)[0]))
      && (forall i₉: int ::
            (!(  old(i) <= i₉
              && i₉ < i
            )
               ==> sum[0] == old(sum)[0]));
  {
    sum := sum[0 := sum[0] + a[i]];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₁₂: int ::
            (  old(i) <= i₁₂
              && i₁₂ < i
               ==> i₁₂ < N
                && a[i₁₂] == old(a)[i₁₂] + sum[0]))
      && (forall i₁₂: int ::
            (!(  old(i) <= i₁₂
              && i₁₂ < i
            )
               ==> a[i₁₂] == old(a)[i₁₂]));
  {
    a := a[i := a[i] + sum[0]];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₁₅: int ::
            (  old(i) <= i₁₅
              && i₁₅ < i
               ==> i₁₅ < N
                && b[i₁₅] == 1 + a[i₁₅]))
      && (forall i₁₅: int ::
            (!(  old(i) <= i₁₅
              && i₁₅ < i
            )
               ==> b[i₁₅] == old(b)[i₁₅]));
  {
    b := b[i := a[i] + 1];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && (forall i₁₈: int ::
            (  old(i) <= i₁₈
              && i₁₈ < i
               ==> i₁₈ < N));
  {
    assert b[i] == N + 2;
    i := i + 1;
  }
  c#result := 1;
  return;
}

