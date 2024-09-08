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
    invariant old(i) <= i
      && i <= N
      && (forall i₅: int ::
            (  old(i) <= i₅
              && i₅ < i
               ==> i₅ < N
                && a[i₅] == 1))
      && (forall i₅: int ::
            (!(  old(i) <= i₅
              && i₅ < i
            )
               ==> a[i₅] == old(a)[i₅]));
  {
    a := a[i := 1];
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && i <= N
      && (forall i₈: int ::
            (  old(i) <= i₈
              && i₈ < i
               ==> a[i₈] == 1
                  && i₈ < N
                  && a[i₈] == 1 + old(a)[i₈]
                ||   a[i₈] != 1
                  && i₈ < N
                  && a[i₈] == -1 + old(a)[i₈]))
      && (forall i₈: int ::
            (!(  old(i) <= i₈
              && i₈ < i
            )
               ==> a[i₈] == old(a)[i₈]));
  {
    if(a[i] == 1) {
      a := a[i := a[i] + 1];
    } else {
      a := a[i := a[i] - 1];
    }
    i := i + 1;
  }
  i := 0;
  while(i < N)
    decreases N - i;
    invariant old(i) <= i
      && i <= N
      && (forall i₁₁: int ::
            (  old(i) <= i₁₁
              && i₁₁ < i
               ==> a[i₁₁] == 2
                  && i₁₁ < N
                  && sum[0] == old(sum)[0] + a[i₁₁]
                ||   a[i₁₁] != 2
                  && i₁₁ < N
                  && sum[0] == old(sum)[0] * a[i₁₁]))
      && (forall i₁₁: int ::
            (!(  old(i) <= i₁₁
              && i₁₁ < i
            )
               ==> sum[0] == old(sum)[0]));
  {
    if(a[i] == 2) {
      sum := sum[0 := sum[0] + a[i]];
    } else {
      sum := sum[0 := sum[0] * a[i]];
    }
    i := i + 1;
  }
  assert sum[0] == 2 * N;
  c#result := 1;
  return;
}

