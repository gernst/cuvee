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
                && b[i₁₂] == 1))
      && (forall i₁₂: int ::
            (!(  old(i) <= i₁₂
              && i₁₂ < i
            )
               ==> b[i₁₂] == old(b)[i₁₂]));
  {
    b := b[i := 1];
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
                && sum[0] == b[i₁₅] + old(sum)[0]))
      && (forall i₁₅: int ::
            (!(  old(i) <= i₁₅
              && i₁₅ < i
            )
               ==> sum[0] == old(sum)[0]));
  {
    sum := sum[0 := sum[0] + b[i]];
    i := i + 1;
  }
  assert sum[0] <= 2 * N;
  c#result := 1;
  return;
}

